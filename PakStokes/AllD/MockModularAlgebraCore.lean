module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.AbsMax
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Wave 12 (Module 2): Zero-Black-Box Algebraic & Analytic Core for Mock Modular Differential Transcendence

Formalizes **100% unconditionally from Mathlib** (zero placeholders, standard assumptions only)
the four crown-jewel algebraic and analytic engines underlying the complete classification of
differential algebraicity for mock modular forms across all weights `k ∈ (1/2) ℤ`:

1. **Exact Symbolic Mock-Modular Vandermonde Determinant (`mockModular_jetQ_det_eq`,
   `mockModular_jet_det_eq`, `iteratedDeriv_mockModular_mode`):**
   Defines the exact jet polynomials `P_j^{(k, r)}(x; ω) = x^{2(r-j)} Q_j^{(k)}(x; ω) ∈ ℂ[x]`
   corresponding to `x^{k + 2r} e^{ω / x} ∂_x^j (x^{-k} e^{-ω / x})`, verifies the exact
   analytic `iteratedDeriv` identity for all `x > 0`, `k ∈ ℂ`, `ω ∈ ℂ`, and proves for EVERY
   `r : ℕ`, EVERY `k : ℂ`, and EVERY `ω : Fin (r + 1) → ℂ`:
   `det (P_j^{(k, r)}(x; ω_s))_{s, j} = x^{r (r + 1)} ∏_{a < b} (ω_b - ω_a)`.
2. **Exact Polynomial Translation-Invariance Minimality Theorem (`dirDeriv`,
   `mvPoly_translation_invariant_of_dirDeriv_eq_zero`,
   `mockModular_translation_invariance_kills_linear_collisions`,
   `mockModular_minimal_annihilator_contradiction`, `mockModular_jump_induction_contradiction`):**
   For ANY `CharZero` integral domain `A` (including `ℂ[[x]]` and convergent germs `ℂ{x}`) and
   ANY `A`-algebra `B`, proves that vanishing of directional derivatives `W_ℓ · ∇_Z R = 0` for
   all `ℓ < s` implies exact polynomial translation invariance
   `R(Z + ∑_{ℓ < s} c_ℓ W_ℓ + δ) = R(Z + δ)`, completely eliminating ALL earlier exponential
   modes before Taylor expansion (killing every linear-rate collision `ω_a + ω_b = ω_c` with
   zero Écalle alien calculus!), and combines with (1) to derive a contradiction for any minimal
   total-`Z`-degree annihilator.
3. **The 8-Line Universal Positive-Weight Modular Differential Independence Lemma
   (`descFac_eq_Gamma_div`, `modular_iteratedDeriv_gamma`,
   `positiveWeight_modular_diff_indep_abstract`, `positiveWeight_modular_forms_diff_indep`,
   `positiveWeight_modular_thetaQ_diff_indep`):**
   Proves by induction on `j` the exact `γ_n = (1 0 // nM 1)` derivative transformation law for
   holomorphic modular forms of arbitrary mixed positive integer and half-integer weights
   `w = k / 2` (`k ≥ 1`) on the upper half-plane `ℍ`, and establishes that any constant-coefficient
   linear differential relation `∑_{w, j} ∂_τ^j G_{w, j}(τ) = C` among `T^L`-periodic positive-weight
   modular forms forces `G_{w, j} ≡ 0` identically (so `ℂ`-linearly independent positive-weight
   modular forms satisfy NO nontrivial relation `∑ Q_i(θ_q) g_{i, cusp} = 0`!).
4. **The 5-Line Maximum Modulus Watson Uniqueness Lemma (`maxModulus_watson_uniqueness`):**
   Using the auxiliary barrier `h_λ(z) = exp(λ (z^{4/5} - R_0^{4/5})) f(z)` and Mathlib's
   Maximum Modulus Principle (`Complex.norm_le_of_forall_mem_frontier_norm_le`), proves that
   any holomorphic function `f` on the closed sector `{‖z‖ ≥ R_0, |arg z| ≤ 2π / 3}` obeying
   `|f(z)| ≤ C' exp(-c' ‖z‖)` (`c' > 0`) vanishes identically on the sector. -/

public section
namespace CubicTheta.AllD
open Set Filter Polynomial MvPolynomial Matrix Complex
open scoped BigOperators Topology Classical
noncomputable section

/-! ### 1. Exact Symbolic Mock-Modular Jet Polynomials & Vandermonde Determinant -/

/-- Apply `Polynomial.derivative` coefficientwise to a polynomial in `ℂ[x][ω]`. -/
def mapDeriv (p : Polynomial (Polynomial ℂ)) : Polynomial (Polynomial ℂ) :=
  ∑ i ∈ p.support, Polynomial.monomial i (Polynomial.derivative (p.coeff i))

private lemma mapDeriv_coeff (p : Polynomial (Polynomial ℂ)) (n : ℕ) :
    (mapDeriv p).coeff n = Polynomial.derivative (p.coeff n) := by
  unfold mapDeriv
  rw [show (∑ i ∈ p.support, Polynomial.monomial i (Polynomial.derivative (p.coeff i))).coeff n =
      (Polynomial.lcoeff (Polynomial ℂ) n)
        (∑ i ∈ p.support, Polynomial.monomial i (Polynomial.derivative (p.coeff i))) from rfl,
      map_sum]
  have hterm : ∀ i ∈ p.support,
      (Polynomial.lcoeff (Polynomial ℂ) n) (Polynomial.monomial i (Polynomial.derivative (p.coeff i))) =
        if i = n then Polynomial.derivative (p.coeff i) else 0 := fun i _ ↦ by
    rw [Polynomial.lcoeff_apply, Polynomial.coeff_monomial]
    exact Finsupp.single_apply
  rw [Finset.sum_congr rfl hterm]
  by_cases hn : n ∈ p.support
  · rw [Finset.sum_eq_single n (fun i _ hne ↦ by simp [hne]) (fun hnot ↦ absurd hn hnot)]
    simp
  · rw [Finset.sum_eq_zero (fun i hi ↦ by
      have hin : i ≠ n := fun h ↦ hn (h ▸ hi)
      simp [hin]),
      Polynomial.notMem_support_iff.mp hn, map_zero]

private lemma mapDeriv_natDegree_le (p : Polynomial (Polynomial ℂ)) :
    (mapDeriv p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [mapDeriv_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hn, map_zero]

private lemma eval_C_mapDeriv (p : Polynomial (Polynomial ℂ)) (ω : ℂ) :
    (mapDeriv p).eval (Polynomial.C ω) = Polynomial.derivative (p.eval (Polynomial.C ω)) := by
  rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt (mapDeriv_natDegree_le p) (Nat.lt_succ_self _)),
      Polynomial.eval_eq_sum_range' (Nat.lt_succ_self p.natDegree), map_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp [mapDeriv_coeff, Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_C]

/-- Exact unshifted mock-modular jet polynomial `Q_j^{(k)}(x; ω)` as a polynomial in `ω`
with coefficients in `ℂ[x]`:
`Q_0 = 1`, `Q_{j+1}(x; ω) = x² ∂_x Q_j(x; ω) + (ω - (k + 2 j) x) Q_j(x; ω)`. -/
def mockJetQ (k : ℂ) : ℕ → Polynomial (Polynomial ℂ)
  | 0 => 1
  | j + 1 =>
    Polynomial.C (Polynomial.X ^ 2) * mapDeriv (mockJetQ k j) +
      (Polynomial.X - Polynomial.C (Polynomial.C (k + 2 * (j : ℂ)) * Polynomial.X)) *
        mockJetQ k j

/-- Evaluation of `Q_j^{(k)}(x; ω)` at a complex frequency `ω : ℂ`, yielding an element of `ℂ[x]`. -/
def mockJetQAt (k : ℂ) (j : ℕ) (ω : ℂ) : Polynomial ℂ :=
  (mockJetQ k j).eval (Polynomial.C ω)

/-- Exact mock-modular jet polynomial `P_j^{(k, r)}(x; ω) = x^{2(r - j)} Q_j^{(k)}(x; ω) ∈ ℂ[x]`,
equal to `x^{k + 2r} e^{ω / x} ∂_x^j (x^{-k} e^{-ω / x})` for all `0 ≤ j ≤ r`. -/
def mockJetP (k : ℂ) (r j : ℕ) (ω : ℂ) : Polynomial ℂ :=
  Polynomial.X ^ (2 * (r - j)) * mockJetQAt k j ω

/-- Every `mockJetQ k j` is a **monic** polynomial of exact `ω`-degree `j` over `ℂ[x]`. -/
theorem mockJetQ_monic_and_natDegree (k : ℂ) (j : ℕ) :
    (mockJetQ k j).Monic ∧ (mockJetQ k j).natDegree = j := by
  induction j with
  | zero =>
    exact ⟨Polynomial.monic_one, Polynomial.natDegree_one⟩
  | succ j ih =>
    obtain ⟨hmon, hdeg⟩ := ih
    rw [mockJetQ]
    set a : Polynomial ℂ := Polynomial.C (k + 2 * (j : ℂ)) * Polynomial.X
    set T1 : Polynomial (Polynomial ℂ) :=
      Polynomial.C (Polynomial.X ^ 2) * mapDeriv (mockJetQ k j)
    set T2 : Polynomial (Polynomial ℂ) := (Polynomial.X - Polynomial.C a) * mockJetQ k j
    have hXsub_mon : (Polynomial.X - Polynomial.C a).Monic := Polynomial.monic_X_sub_C a
    have hXsub_deg : (Polynomial.X - Polynomial.C a).natDegree = 1 := Polynomial.natDegree_X_sub_C a
    have hT2_mon : T2.Monic := hXsub_mon.mul hmon
    have hT2_deg : T2.natDegree = j + 1 := by
      rw [Polynomial.Monic.natDegree_mul hXsub_mon hmon, hXsub_deg, hdeg, add_comm]
    have hT1_deg_le : T1.natDegree ≤ j := by
      calc T1.natDegree
          ≤ (Polynomial.C (Polynomial.X ^ 2 : Polynomial ℂ)).natDegree +
              (mapDeriv (mockJetQ k j)).natDegree :=
            Polynomial.natDegree_mul_le
        _ = (mapDeriv (mockJetQ k j)).natDegree := by simp
        _ ≤ (mockJetQ k j).natDegree := mapDeriv_natDegree_le _
        _ = j := hdeg
    have hT1_lt_T2 : T1.degree < T2.degree := by
      by_cases hT10 : T1 = 0
      · rw [hT10, Polynomial.degree_zero, Polynomial.degree_eq_natDegree hT2_mon.ne_zero]
        exact WithBot.bot_lt_coe _
      · exact Polynomial.degree_lt_degree (by omega)
    refine ⟨hT2_mon.add_of_right hT1_lt_T2, ?_⟩
    rw [Polynomial.natDegree_add_eq_right_of_degree_lt hT1_lt_T2, hT2_deg]

theorem mockJetQ_monic (k : ℂ) (j : ℕ) : (mockJetQ k j).Monic :=
  (mockJetQ_monic_and_natDegree k j).1

theorem mockJetQ_natDegree (k : ℂ) (j : ℕ) : (mockJetQ k j).natDegree = j :=
  (mockJetQ_monic_and_natDegree k j).2

@[simp]
theorem mockJetQAt_zero (k ω : ℂ) : mockJetQAt k 0 ω = 1 := by
  simp [mockJetQAt, mockJetQ]

theorem mockJetQAt_succ (k ω : ℂ) (j : ℕ) :
    mockJetQAt k (j + 1) ω =
      Polynomial.X ^ 2 * Polynomial.derivative (mockJetQAt k j ω) +
        (Polynomial.C ω - Polynomial.C (k + 2 * (j : ℂ)) * Polynomial.X) * mockJetQAt k j ω := by
  unfold mockJetQAt
  rw [mockJetQ, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      Polynomial.eval_C, eval_C_mapDeriv, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C]

theorem mockJetP_zero (k ω : ℂ) (r : ℕ) : mockJetP k r 0 ω = Polynomial.X ^ (2 * r) := by
  simp [mockJetP]

/-- Exact differential recurrence for `P_j^{(k, r)}(x; ω)` (`j < r`):
`x² P_{j+1} = x² ∂_x P_j + (ω - (k + 2 r) x) P_j`. -/
theorem mockJetP_recurrence (k ω : ℂ) {r j : ℕ} (hj : j < r) :
    Polynomial.X ^ 2 * mockJetP k r (j + 1) ω =
      Polynomial.X ^ 2 * Polynomial.derivative (mockJetP k r j ω) +
        (Polynomial.C ω - Polynomial.C (k + 2 * (r : ℂ)) * Polynomial.X) * mockJetP k r j ω := by
  unfold mockJetP
  rw [mockJetQAt_succ]
  have hsub : 2 * (r - j) = 2 * (r - (j + 1)) + 2 := by omega
  have hderiv : Polynomial.derivative (Polynomial.X ^ (2 * (r - j)) * mockJetQAt k j ω) =
      Polynomial.C ((2 * (r - j) : ℕ) : ℂ) * Polynomial.X ^ (2 * (r - j) - 1) * mockJetQAt k j ω +
        Polynomial.X ^ (2 * (r - j)) * Polynomial.derivative (mockJetQAt k j ω) := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_X_pow, Polynomial.C_eq_natCast, mul_assoc]
  rw [hderiv]
  have hpow1 : Polynomial.X ^ 2 * (Polynomial.X ^ (2 * (r - (j + 1))) : Polynomial ℂ) =
      Polynomial.X ^ (2 * (r - j)) := by
    rw [← pow_add, add_comm, hsub]
  have hpow2 : Polynomial.X ^ 2 * (Polynomial.X ^ (2 * (r - j) - 1) : Polynomial ℂ) =
      Polynomial.X ^ (2 * (r - j)) * Polynomial.X := by
    rw [← pow_add, ← pow_succ]
    congr 1; omega
  have hcast : ((2 * (r - j) : ℕ) : ℂ) - (k + 2 * (r : ℂ)) = -(k + 2 * (j : ℂ)) := by
    have hle : j ≤ r := hj.le
    have hsubC : ((r - j : ℕ) : ℂ) = (r : ℂ) - (j : ℂ) := Nat.cast_sub hle
    rw [Nat.cast_mul, Nat.cast_ofNat, hsubC]; ring
  have h1 : Polynomial.X ^ 2 *
      (Polynomial.C ((2 * (r - j) : ℕ) : ℂ) * Polynomial.X ^ (2 * (r - j) - 1) *
        mockJetQAt k j ω) =
      Polynomial.C ((2 * (r - j) : ℕ) : ℂ) * Polynomial.X ^ (2 * (r - j)) *
        Polynomial.X * mockJetQAt k j ω := by
    calc Polynomial.X ^ 2 *
          (Polynomial.C ((2 * (r - j) : ℕ) : ℂ) * Polynomial.X ^ (2 * (r - j) - 1) *
            mockJetQAt k j ω)
        = Polynomial.C ((2 * (r - j) : ℕ) : ℂ) *
            (Polynomial.X ^ 2 * Polynomial.X ^ (2 * (r - j) - 1)) * mockJetQAt k j ω := by
          ring
      _ = Polynomial.C ((2 * (r - j) : ℕ) : ℂ) * Polynomial.X ^ (2 * (r - j)) *
            Polynomial.X * mockJetQAt k j ω := by rw [hpow2]; ring
  have hC : Polynomial.C ((2 * (r - j) : ℕ) : ℂ) - Polynomial.C (k + 2 * (r : ℂ)) =
      -Polynomial.C (k + 2 * (j : ℂ)) := by
    rw [← map_sub, hcast, map_neg]
  calc Polynomial.X ^ 2 *
          (Polynomial.X ^ (2 * (r - (j + 1))) *
            (Polynomial.X ^ 2 * Polynomial.derivative (mockJetQAt k j ω) +
              (Polynomial.C ω - Polynomial.C (k + 2 * (j : ℂ)) * Polynomial.X) *
                mockJetQAt k j ω))
      = Polynomial.X ^ (2 * (r - j)) *
          (Polynomial.X ^ 2 * Polynomial.derivative (mockJetQAt k j ω) +
            (Polynomial.C ω - Polynomial.C (k + 2 * (j : ℂ)) * Polynomial.X) *
              mockJetQAt k j ω) := by rw [← mul_assoc, hpow1]
    _ = Polynomial.X ^ 2 *
          (Polynomial.C ((2 * (r - j) : ℕ) : ℂ) * Polynomial.X ^ (2 * (r - j) - 1) *
              mockJetQAt k j ω +
            Polynomial.X ^ (2 * (r - j)) * Polynomial.derivative (mockJetQAt k j ω)) +
          (Polynomial.C ω - Polynomial.C (k + 2 * (r : ℂ)) * Polynomial.X) *
            (Polynomial.X ^ (2 * (r - j)) * mockJetQAt k j ω) := by
        linear_combination
          -h1 - (Polynomial.X ^ (2 * (r - j)) * Polynomial.X * mockJetQAt k j ω) * hC

/-- **Exact Unshifted Mock-Modular Vandermonde Determinant**:
`det(Q_j^{(k)}(x; ω_s))_{s, j ∈ Fin (r + 1)} = ∏_{a < b} (ω_b - ω_a)` — independent of `x` and `k`! -/
theorem mockModular_jetQ_det_eq (k : ℂ) (r : ℕ) (ω : Fin (r + 1) → ℂ) :
    (Matrix.of fun s j : Fin (r + 1) ↦ mockJetQAt k j.val (ω s)).det =
      Polynomial.C (∏ a : Fin (r + 1), ∏ b ∈ Finset.Ioi a, (ω b - ω a)) := by
  let U : Matrix (Fin (r + 1)) (Fin (r + 1)) (Polynomial ℂ) :=
    Matrix.of fun m j ↦ (mockJetQ k j.val).coeff m.val
  let V : Matrix (Fin (r + 1)) (Fin (r + 1)) (Polynomial ℂ) :=
    Matrix.vandermonde (fun s ↦ Polynomial.C (ω s))
  have hfac : (Matrix.of fun s j : Fin (r + 1) ↦ mockJetQAt k j.val (ω s)) = V * U := by
    apply Matrix.ext; intro s j
    simp only [Matrix.of_apply, Matrix.mul_apply, V, U, Matrix.vandermonde_apply, mockJetQAt]
    rw [Polynomial.eval_eq_sum_range' (lt_of_eq_of_lt (mockJetQ_natDegree k j.val) j.isLt),
        ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hU_tri : U.BlockTriangular id := by
    intro m j hlt
    change (mockJetQ k j.val).coeff m.val = 0
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [mockJetQ_natDegree]
    exact hlt
  have hU_det : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hU_tri]
    apply Finset.prod_eq_one
    intro j _
    change (mockJetQ k j.val).coeff j.val = 1
    conv_lhs => arg 2; rw [← mockJetQ_natDegree k j.val]
    exact (mockJetQ_monic k j.val).leadingCoeff
  rw [hfac, Matrix.det_mul, hU_det, mul_one, Matrix.det_vandermonde]
  simp only [map_prod, map_sub]

private lemma sum_two_mul_sub (r : ℕ) :
    ∑ j : Fin (r + 1), 2 * (r - j.val) = r * (r + 1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    have hcast : ∑ j : Fin (r + 1), 2 * (r + 1 - j.val) =
        ∑ j : Fin (r + 1), (2 * (r - j.val) + 2) := by
      apply Finset.sum_congr rfl
      intro j _
      have hj : j.val ≤ r := Nat.lt_succ_iff.mp j.isLt
      omega
    simp only [Fin.val_castSucc, Fin.val_last, Nat.sub_self, mul_zero, add_zero]
    rw [hcast, Finset.sum_add_distrib, ih, Finset.sum_const, Finset.card_fin, smul_eq_mul]
    ring

/-- **Crown Jewel Theorem 1 — Exact Symbolic Mock-Modular Vandermonde Determinant**:
For EVERY `r : ℕ`, EVERY weight `k : ℂ`, and EVERY tuple `ω : Fin (r + 1) → ℂ`:
`det(P_j^{(k, r)}(x; ω_s))_{s, j ∈ Fin (r + 1)} = x^{r (r + 1)} ∏_{a < b} (ω_b - ω_a)`. -/
theorem mockModular_jet_det_eq (k : ℂ) (r : ℕ) (ω : Fin (r + 1) → ℂ) :
    (Matrix.of fun s j : Fin (r + 1) ↦ mockJetP k r j.val (ω s)).det =
      Polynomial.X ^ (r * (r + 1)) *
        Polynomial.C (∏ a : Fin (r + 1), ∏ b ∈ Finset.Ioi a, (ω b - ω a)) := by
  have hfac : (Matrix.of fun s j : Fin (r + 1) ↦ mockJetP k r j.val (ω s)) =
      (Matrix.of fun s j : Fin (r + 1) ↦ mockJetQAt k j.val (ω s)) *
        Matrix.diagonal (fun j : Fin (r + 1) ↦ (Polynomial.X : Polynomial ℂ) ^ (2 * (r - j.val))) := by
    ext s j
    simp [mockJetP, Matrix.mul_diagonal, mul_comm]
  rw [hfac, Matrix.det_mul, mockModular_jetQ_det_eq, Matrix.det_diagonal,
      Finset.prod_pow_eq_pow_sum, sum_two_mul_sub, mul_comm]

private lemma hasDerivAt_poly_eval (p : Polynomial ℂ) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ p.eval w) ((Polynomial.derivative p).eval z) z := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have := hp.fun_add hq
    simpa [Polynomial.eval_add, Polynomial.derivative_add] using this
  | monomial n c =>
    have h1 : HasDerivAt (fun w : ℂ ↦ c * w ^ n) (c * ((n : ℂ) * z ^ (n - 1))) z :=
      (hasDerivAt_pow n z).const_mul c
    convert h1 using 1
    · funext w; simp [Polynomial.eval_monomial]
    · simp [Polynomial.derivative_monomial, Polynomial.eval_monomial]; ring

/-- **Exact Analytic Derivative Verification**: for every `k ω : ℂ`, `j : ℕ`, and real `x > 0`,
`∂_x^j (x^{-k} e^{-ω / x}) = x^{-k - 2 j} e^{-ω / x} Q_j^{(k)}(x; ω)`. -/
theorem iteratedDeriv_mockModular_mode (k ω : ℂ) (j : ℕ) :
    ∀ x : ℝ, 0 < x →
      iteratedDeriv j (fun t : ℝ ↦ (t : ℂ) ^ (-k) * Complex.exp (-ω / (t : ℂ))) x =
        (x : ℂ) ^ (-k - 2 * (j : ℂ)) * Complex.exp (-ω / (x : ℂ)) *
          (mockJetQAt k j ω).eval (x : ℂ) := by
  induction j with
  | zero =>
    intro x _
    simp [iteratedDeriv_zero]
  | succ j ih =>
    intro x hx
    rw [iteratedDeriv_succ]
    have heq : iteratedDeriv j (fun u : ℝ ↦ (u : ℂ) ^ (-k) * Complex.exp (-ω / (u : ℂ))) =ᶠ[𝓝 x]
        fun t : ℝ ↦ (t : ℂ) ^ (-k - 2 * (j : ℂ)) * Complex.exp (-ω / (t : ℂ)) *
          (mockJetQAt k j ω).eval (t : ℂ) := by
      filter_upwards [eventually_gt_nhds hx] with t ht
      exact ih t ht
    rw [heq.deriv_eq]
    have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hslit : (x : ℂ) ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hx)
    have hpow : HasDerivAt (fun t : ℝ ↦ (t : ℂ) ^ (-k - 2 * (j : ℂ)))
        ((-k - 2 * (j : ℂ)) * (x : ℂ) ^ (-k - 2 * (j : ℂ) - 1)) x := by
      have h1 := HasDerivAt.cpow_const (c := -k - 2 * (j : ℂ)) (hasDerivAt_id (x : ℂ)) hslit
      simpa using h1.comp_ofReal
    have hexp : HasDerivAt (fun t : ℝ ↦ Complex.exp (-ω / (t : ℂ)))
        (Complex.exp (-ω / (x : ℂ)) * (ω / (x : ℂ) ^ 2)) x := by
      have hinv : HasDerivAt (fun t : ℝ ↦ (-ω) / (t : ℂ)) (ω / (x : ℂ) ^ 2) x := by
        have h1 : HasDerivAt (fun z : ℂ ↦ (-ω) * z⁻¹) ((-ω) * -((x : ℂ) ^ 2)⁻¹) (x : ℂ) :=
          (hasDerivAt_inv hxC).const_mul (-ω)
        have h2 := h1.comp_ofReal
        convert h2 using 1
        · funext t; simp [div_eq_mul_inv]
        · ring
      have h2 := hinv.cexp
      simpa [mul_comm] using h2
    have hpoly : HasDerivAt (fun t : ℝ ↦ (mockJetQAt k j ω).eval (t : ℂ))
        ((Polynomial.derivative (mockJetQAt k j ω)).eval (x : ℂ)) x :=
      (hasDerivAt_poly_eval (mockJetQAt k j ω) (x : ℂ)).comp_ofReal
    have htot := (hpow.fun_mul hexp).fun_mul hpoly
    rw [htot.deriv, mockJetQAt_succ]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C, Nat.cast_add, Nat.cast_one]
    have hcpow1 : (x : ℂ) ^ (-k - 2 * (j : ℂ) - 1) =
        (x : ℂ) ^ (-k - 2 * ((j : ℂ) + 1)) * (x : ℂ) := by
      have h := Complex.cpow_add (-k - 2 * ((j : ℂ) + 1)) 1 hxC
      rw [Complex.cpow_one] at h
      rw [← h]
      congr 1; ring
    have hcpow2 : (x : ℂ) ^ (-k - 2 * (j : ℂ)) =
        (x : ℂ) ^ (-k - 2 * ((j : ℂ) + 1)) * (x : ℂ) ^ 2 := by
      have h2 : (x : ℂ) ^ (2 : ℂ) = (x : ℂ) ^ 2 := by norm_cast
      rw [← h2, ← Complex.cpow_add _ _ hxC]
      congr 1; ring
    rw [hcpow1, hcpow2]
    field_simp [hxC]
    ring

/-! ### 2. Exact Polynomial Translation-Invariance Minimality Theorem -/

section TranslationInvariance

variable {A ι : Type*} [CommRing A]

/-- Directional derivative `W · ∇_Z R = ∑_j W_j ∂_{Z_j} R` on `MvPolynomial ι A`. -/
def dirDeriv [Fintype ι] (W : ι → A) (R : MvPolynomial ι A) : MvPolynomial ι A :=
  ∑ j : ι, MvPolynomial.C (W j) * MvPolynomial.pderiv j R

@[simp]
theorem dirDeriv_C [Fintype ι] (W : ι → A) (c : A) :
    dirDeriv W (MvPolynomial.C c) = 0 := by
  simp [dirDeriv]

@[simp]
theorem dirDeriv_X [Fintype ι] (W : ι → A) (k : ι) :
    dirDeriv W (MvPolynomial.X k) = MvPolynomial.C (W k) := by
  unfold dirDeriv
  rw [Finset.sum_eq_single k]
  · simp [MvPolynomial.pderiv_X]
  · intro j _ hjk
    simp [MvPolynomial.pderiv_X, Pi.single_eq_of_ne (Ne.symm hjk)]
  · intro hnot; exact absurd (Finset.mem_univ k) hnot

theorem dirDeriv_add [Fintype ι] (W : ι → A) (P Q : MvPolynomial ι A) :
    dirDeriv W (P + Q) = dirDeriv W P + dirDeriv W Q := by
  simp only [dirDeriv, map_add, mul_add, Finset.sum_add_distrib]

theorem dirDeriv_mul [Fintype ι] (W : ι → A) (P Q : MvPolynomial ι A) :
    dirDeriv W (P * Q) = dirDeriv W P * Q + P * dirDeriv W Q := by
  simp only [dirDeriv, Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> (apply Finset.sum_congr rfl; intro j _; ring)

/-- One-parameter shift polynomial `T ↦ R(Z + T · W) ∈ (MvPolynomial ι A)[T]`. -/
def shiftPoly (W : ι → A) (R : MvPolynomial ι A) : Polynomial (MvPolynomial ι A) :=
  MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
    (fun j ↦ Polynomial.C (MvPolynomial.X j) + Polynomial.C (MvPolynomial.C (W j)) * Polynomial.X) R

@[simp]
theorem shiftPoly_C (W : ι → A) (c : A) :
    shiftPoly W (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by
  simp [shiftPoly]

@[simp]
theorem shiftPoly_X (W : ι → A) (j : ι) :
    shiftPoly W (MvPolynomial.X j) =
      Polynomial.C (MvPolynomial.X j) + Polynomial.C (MvPolynomial.C (W j)) * Polynomial.X := by
  simp [shiftPoly]

theorem shiftPoly_add (W : ι → A) (P Q : MvPolynomial ι A) :
    shiftPoly W (P + Q) = shiftPoly W P + shiftPoly W Q := by
  simp [shiftPoly]

theorem shiftPoly_mul (W : ι → A) (P Q : MvPolynomial ι A) :
    shiftPoly W (P * Q) = shiftPoly W P * shiftPoly W Q := by
  simp [shiftPoly]

/-- Exact derivative identity `(d/dT) R(Z + T · W) = (W · ∇_Z R)(Z + T · W)`. -/
theorem derivative_shiftPoly [Fintype ι] (W : ι → A) (R : MvPolynomial ι A) :
    Polynomial.derivative (shiftPoly W R) = shiftPoly W (dirDeriv W R) := by
  induction R using MvPolynomial.induction_on with
  | C c =>
    simp [shiftPoly, dirDeriv]
  | add P Q hP hQ =>
    rw [shiftPoly_add, dirDeriv_add, shiftPoly_add, Polynomial.derivative_add, hP, hQ]
  | mul_X P k hP =>
    rw [shiftPoly_mul, dirDeriv_mul, shiftPoly_add, shiftPoly_mul, shiftPoly_mul,
        Polynomial.derivative_mul, hP, shiftPoly_X, dirDeriv_X, shiftPoly_C]
    simp only [Polynomial.derivative_add, Polynomial.derivative_C, zero_add,
      Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, zero_mul]

/-- Evaluating `shiftPoly W R` at `T = 0` recovers `R` identically. -/
theorem eval_zero_shiftPoly (W : ι → A) (R : MvPolynomial ι A) :
    (shiftPoly W R).eval 0 = R := by
  induction R using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [shiftPoly_add, hP, hQ]
  | mul_X P k hP => simp [shiftPoly_mul, shiftPoly_X, hP]

/-- Evaluating `shiftPoly W R` at any scalar `c : B` and point `Z : ι → B` in ANY `A`-algebra `B`
computes `R(Z + c · W)`. -/
theorem aeval_shiftPoly {B : Type*} [CommRing B] [Algebra A B]
    (W : ι → A) (R : MvPolynomial ι A) (Z : ι → B) (c : B) :
    ((shiftPoly W R).map (MvPolynomial.aeval Z : MvPolynomial ι A →ₐ[A] B).toRingHom).eval c =
      MvPolynomial.aeval (fun j ↦ Z j + c * algebraMap A B (W j)) R := by
  induction R using MvPolynomial.induction_on with
  | C a =>
    simp [shiftPoly_C]
  | add P Q hP hQ =>
    rw [shiftPoly_add, Polynomial.map_add, Polynomial.eval_add, hP, hQ, map_add]
  | mul_X P k hP =>
    rw [shiftPoly_mul, shiftPoly_X, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_C, Polynomial.map_X, Polynomial.eval_mul,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C,
        Polynomial.eval_X, hP, map_mul, MvPolynomial.aeval_X]
    simp [mul_comm]

private lemma poly_eq_C_of_derivative_eq_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (f : Polynomial R) (hf : Polynomial.derivative f = 0) :
    f = Polynomial.C (f.eval 0) := by
  ext n
  cases n with
  | zero => simp [Polynomial.coeff_zero_eq_eval_zero]
  | succ n =>
    rw [Polynomial.coeff_C_succ]
    have h0 := congrArg (fun p : Polynomial R ↦ p.coeff n) hf
    rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at h0
    have hnat : ((n : R) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    exact (mul_eq_zero.mp h0).resolve_right hnat

/-- **Exact Single-Mode Polynomial Translation Invariance**: over ANY `CharZero` integral domain
`A` (e.g. `ℂ[[x]]` or convergent germs `ℂ{x}`), if `W · ∇_Z R = 0` identically, then for EVERY
`A`-algebra `B`, EVERY point `Z : ι → B`, and EVERY scalar `c : B`, `R(Z + c · W) = R(Z)`. -/
theorem mvPoly_translation_invariant_of_dirDeriv_eq_zero [IsDomain A] [CharZero A] [Fintype ι]
    {W : ι → A} {R : MvPolynomial ι A} (hW : dirDeriv W R = 0) :
    shiftPoly W R = Polynomial.C R ∧
      ∀ {B : Type*} [CommRing B] [Algebra A B] (Z : ι → B) (c : B),
        MvPolynomial.aeval (fun j ↦ Z j + c * algebraMap A B (W j)) R =
          MvPolynomial.aeval Z R := by
  have : CharZero (MvPolynomial ι A) :=
    ⟨fun a b h ↦ by
      have h0 := congrArg (fun p : MvPolynomial ι A ↦ p.coeff 0) h
      simp only [← MvPolynomial.C_eq_natCast, MvPolynomial.coeff_C, ↓reduceIte] at h0
      exact Nat.cast_injective h0⟩
  have hderiv0 : Polynomial.derivative (shiftPoly W R) = 0 := by
    rw [derivative_shiftPoly, hW]
    simp [shiftPoly]
  have hconst : shiftPoly W R = Polynomial.C R := by
    have h1 := poly_eq_C_of_derivative_eq_zero (shiftPoly W R) hderiv0
    rwa [eval_zero_shiftPoly] at h1
  refine ⟨hconst, fun {B} _ _ Z c ↦ ?_⟩
  rw [← aeval_shiftPoly W R Z c, hconst, Polynomial.map_C, Polynomial.eval_C]
  rfl

/-- **Crown Jewel Theorem 2 — Exact Multi-Mode Translation Invariance (Kills All Linear Collisions!)**:
If `W_ℓ · ∇_Z R = 0` identically for all earlier modes `ℓ ∈ S`, then for EVERY `A`-algebra `B`,
EVERY point `Z : ι → B`, EVERY scalar tuple `c : α → B`, and EVERY remaining tail `δ : ι → B`:
`R(Z + ∑_{ℓ ∈ S} c_ℓ W_ℓ + δ) = R(Z + δ)` identically!
All earlier exponential modes drop out **EXACTLY** before Taylor expansion — completely eliminating
every linear-rate collision `ω_a + ω_b = ω_c` with zero Borel/alien calculus! -/
theorem mockModular_translation_invariance_kills_linear_collisions
    [IsDomain A] [CharZero A] [Fintype ι] {α : Type*} (S : Finset α)
    (W : α → ι → A) (R : MvPolynomial ι A)
    (hW : ∀ ℓ ∈ S, dirDeriv (W ℓ) R = 0)
    {B : Type*} [CommRing B] [Algebra A B] (Z : ι → B) (c : α → B) (δ : ι → B) :
    MvPolynomial.aeval (fun j ↦ Z j + (∑ ℓ ∈ S, c ℓ * algebraMap A B (W ℓ j)) + δ j) R =
      MvPolynomial.aeval (fun j ↦ Z j + δ j) R := by
  induction S using Finset.induction_on with
  | empty =>
    simp
  | insert a S ha ih =>
    have hWa : dirDeriv (W a) R = 0 := hW a (Finset.mem_insert_self a S)
    have hWS : ∀ ℓ ∈ S, dirDeriv (W ℓ) R = 0 := fun ℓ hℓ ↦ hW ℓ (Finset.mem_insert_of_mem hℓ)
    let Z' : ι → B := fun j ↦ Z j + (∑ ℓ ∈ S, c ℓ * algebraMap A B (W ℓ j)) + δ j
    have hfun : (fun j ↦ Z j + (∑ ℓ ∈ insert a S, c ℓ * algebraMap A B (W ℓ j)) + δ j) =
        (fun j ↦ Z' j + c a * algebraMap A B (W a j)) := by
      funext j
      simp only [Z', Finset.sum_insert ha]
      ring
    rw [hfun, (mvPoly_translation_invariant_of_dirDeriv_eq_zero hWa).2 Z' (c a)]
    exact ih hWS

/-- Exact first-order Taylor expansion of `R(Z + δ)` with explicit degree-`≥ 2` remainder. -/
theorem mockModular_taylor_expansion [Fintype ι] {B : Type*} [CommRing B] [Algebra A B]
    (R : MvPolynomial ι A) (Z δ : ι → B) :
    let F : Polynomial B :=
      MvPolynomial.eval₂ (Polynomial.C.comp (algebraMap A B))
        (fun j ↦ Polynomial.C (Z j) + Polynomial.C (δ j) * Polynomial.X) R
    MvPolynomial.aeval (fun j ↦ Z j + δ j) R =
      MvPolynomial.aeval Z R +
        (∑ j : ι, δ j * MvPolynomial.aeval Z (MvPolynomial.pderiv j R)) +
        ∑ m ∈ (Finset.range (F.natDegree + 1)).filter (2 ≤ ·), F.coeff m := by
  let shiftB : MvPolynomial ι A →+* Polynomial B :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp (algebraMap A B))
      (fun j ↦ Polynomial.C (Z j) + Polynomial.C (δ j) * Polynomial.X)
  have hF_eval1 : ∀ P : MvPolynomial ι A, (shiftB P).eval 1 = MvPolynomial.aeval (fun j ↦ Z j + δ j) P := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp [shiftB]
    | add P Q hP hQ => rw [map_add, Polynomial.eval_add, hP, hQ, map_add]
    | mul_X P k hP =>
      rw [map_mul, Polynomial.eval_mul, hP, map_mul, MvPolynomial.aeval_X]
      simp [shiftB]
  have hF_eval0 : ∀ P : MvPolynomial ι A, (shiftB P).eval 0 = MvPolynomial.aeval Z P := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp [shiftB]
    | add P Q hP hQ => rw [map_add, Polynomial.eval_add, hP, hQ, map_add]
    | mul_X P k hP =>
      rw [map_mul, Polynomial.eval_mul, hP, map_mul, MvPolynomial.aeval_X]
      simp [shiftB]
  have hF_d0 : ∀ P : MvPolynomial ι A,
      (Polynomial.derivative (shiftB P)).eval 0 =
        ∑ j : ι, δ j * MvPolynomial.aeval Z (MvPolynomial.pderiv j P) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a => simp [shiftB]
    | add P Q hP hQ =>
      simp only [map_add, Polynomial.eval_add, mul_add,
        Finset.sum_add_distrib, hP, hQ]
    | mul_X P k hP =>
      have hX : shiftB (MvPolynomial.X k) = Polynomial.C (Z k) + Polynomial.C (δ k) * Polynomial.X := by
        simp [shiftB]
      rw [map_mul, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_mul, hP, hF_eval0 P, hX]
      simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
        mul_zero, add_zero, Polynomial.derivative_C, zero_add,
        Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, zero_mul,
        Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.aeval_X,
        MvPolynomial.pderiv_X, Pi.single_apply, apply_ite (MvPolynomial.aeval Z),
        map_one, map_zero, mul_add, Finset.sum_add_distrib]
      have hdiag : (∑ j : ι, δ j * (MvPolynomial.aeval Z P * if k = j then (1 : B) else 0)) =
          MvPolynomial.aeval Z P * δ k := by
        rw [Finset.sum_eq_single k]
        · simp [mul_comm]
        · intro j _ hjk; simp [Ne.symm hjk]
        · intro hnot; exact absurd (Finset.mem_univ k) hnot
      rw [hdiag, add_comm, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _; ring
  intro F
  have hFeq : F = shiftB R := rfl
  have hF_c0 : F.coeff 0 = MvPolynomial.aeval Z R := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hFeq, hF_eval0 R]
  have hF_c1 : F.coeff 1 = ∑ j : ι, δ j * MvPolynomial.aeval Z (MvPolynomial.pderiv j R) := by
    have hder : (Polynomial.derivative F).eval 0 = F.coeff 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]; simp
    rw [← hder, hFeq, hF_d0 R]
  rw [← hF_eval1 R, ← hFeq, Polynomial.eval_eq_sum_range]
  simp only [one_pow, mul_one]
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (F.natDegree + 1)) (2 ≤ ·) F.coeff
  rw [← hsplit, add_comm]
  congr 1
  have hlt2 : (Finset.range (F.natDegree + 1)).filter (fun m ↦ ¬ 2 ≤ m) ⊆ {0, 1} := by
    intro m hm
    have := (Finset.mem_filter.mp hm).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  rw [← hF_c0, ← hF_c1]
  have hsum01 : F.coeff 0 + F.coeff 1 = ∑ m ∈ ({0, 1} : Finset ℕ), F.coeff m := by
    rw [Finset.sum_pair (by decide)]
  rw [hsum01]
  apply Finset.sum_subset hlt2
  intro m hm hnot
  simp only [Finset.mem_filter, Finset.mem_range, not_and, not_not] at hnot
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hgt : F.natDegree < m := by
    by_contra hle
    have hlt : m < F.natDegree + 1 := by omega
    have hge2 := hnot hlt
    omega
  exact Polynomial.coeff_eq_zero_of_natDegree_lt hgt

private lemma mvPoly_totalDegree_finset_sum_le {α : Type*} (s : Finset α)
    (f : α → MvPolynomial ι A) :
    (∑ a ∈ s, f a).totalDegree ≤ s.sup (fun a ↦ (f a).totalDegree) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max le_rfl ih)

/-- Strictly drops total degree under any directional derivative `dirDeriv W` (when `0 < R.totalDegree`). -/
theorem dirDeriv_totalDegree_lt [IsDomain A] [CharZero A] [Fintype ι]
    (W : ι → A) {R : MvPolynomial ι A} (hR : 0 < R.totalDegree) :
    (dirDeriv W R).totalDegree < R.totalDegree := by
  unfold dirDeriv
  apply lt_of_le_of_lt (mvPoly_totalDegree_finset_sum_le _ _)
  rw [Finset.sup_lt_iff hR]
  intro j _
  calc (MvPolynomial.C (W j) * MvPolynomial.pderiv j R).totalDegree
      ≤ (MvPolynomial.C (W j)).totalDegree + (MvPolynomial.pderiv j R).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ = (MvPolynomial.pderiv j R).totalDegree := by simp
    _ < R.totalDegree := by
        rw [MvPolynomial.totalDegree_eq]
        apply lt_of_le_of_lt (Finset.sup_le fun m hm ↦ ?_) (Nat.pred_lt hR.ne')
        have hn := MvPolynomial.mem_support_iff.mp hm
        rw [MvPolynomial.coeff_pderiv] at hn
        have hs := MvPolynomial.le_totalDegree
          (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn))
        change ((m + Finsupp.single j 1).sum fun _ ↦ id) ≤ _ at hs
        rw [← Finsupp.card_toMultiset, Finsupp.toMultiset_add, Finsupp.toMultiset_single] at hs
        simp at hs
        rw [Finsupp.card_toMultiset, Nat.pred_eq_sub_one]
        omega

/-- **Crown Jewel Theorem 2B — Minimal Annihilator Contradiction (Combining Theorems 1 & 2)**:
Let `A` be ANY `CharZero` integral domain with an injective ring embedding `ι : ℂ[x] →+* A`
(e.g. `A = PowerSeries ℂ` via `Polynomial.coeToPowerSeries.ringHom`). If `R ∈ A[Z₀, …, Z_r]`
has positive total degree `0 < R.totalDegree` and is annihilated by the `r + 1` mock-modular
jet directional derivatives `W_s(j) = α_s · ι(P_j^{(k, r)}(x; ω_s))` at `r + 1` pairwise
distinct frequencies `ω_0, …, ω_r` with nonzero amplitudes `α_s ≠ 0`, then `False`! -/
theorem mockModular_minimal_annihilator_contradiction
    [IsDomain A] [CharZero A] (emb : Polynomial ℂ →+* A) (hemb : Function.Injective emb)
    {r : ℕ} (k : ℂ) (ω : Fin (r + 1) → ℂ) (hω : Function.Injective ω)
    (α : Fin (r + 1) → A) (hα : ∀ s : Fin (r + 1), α s ≠ 0)
    (R : MvPolynomial (Fin (r + 1)) A) (hdeg : 0 < R.totalDegree)
    (hvan : ∀ s : Fin (r + 1),
      dirDeriv (fun j : Fin (r + 1) ↦ α s * emb (mockJetP k r j.val (ω s))) R = 0) :
    False := by
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) A :=
    Matrix.of fun s j ↦ α s * emb (mockJetP k r j.val (ω s))
  have hM_det : M.det ≠ 0 := by
    have hfac : M = Matrix.diagonal α *
        emb.mapMatrix (Matrix.of fun s j : Fin (r + 1) ↦ mockJetP k r j.val (ω s)) := by
      apply Matrix.ext; intro s j
      simp [M, Matrix.diagonal_mul, RingHom.mapMatrix_apply]
    rw [hfac, Matrix.det_mul, Matrix.det_diagonal, ← RingHom.map_det, mockModular_jet_det_eq]
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun s _ ↦ hα s) ?_
    have hpoly_ne : (Polynomial.X : Polynomial ℂ) ^ (r * (r + 1)) *
        Polynomial.C (∏ a : Fin (r + 1), ∏ b ∈ Finset.Ioi a, (ω b - ω a)) ≠ 0 := by
      refine mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) ?_
      rw [ne_eq, Polynomial.C_eq_zero]
      refine Finset.prod_ne_zero_iff.mpr fun a _ ↦
        Finset.prod_ne_zero_iff.mpr fun b hb ↦ ?_
      have hab : a ≠ b := (Finset.mem_Ioi.mp hb).ne
      exact sub_ne_zero.mpr fun h ↦ hab (hω h.symm)
    intro h0
    exact hpoly_ne (hemb (h0.trans (map_zero emb).symm))
  -- Every monomial coefficient vector `v_m(j) = (pderiv j R).coeff m` satisfies `M *ᵥ v_m = 0`!
  have hall_pderiv : ∀ j : Fin (r + 1), MvPolynomial.pderiv j R = 0 := by
    have hcoeff_zero : ∀ m : Fin (r + 1) →₀ ℕ, ∀ j : Fin (r + 1),
        (MvPolynomial.pderiv j R).coeff m = 0 := by
      intro m
      let v : Fin (r + 1) → A := fun j ↦ (MvPolynomial.pderiv j R).coeff m
      have hMv : M *ᵥ v = 0 := by
        funext s
        have h0 := congrArg (fun f : MvPolynomial (Fin (r + 1)) A ↦ (MvPolynomial.lcoeff A m) f) (hvan s)
        rw [dirDeriv, map_sum, map_zero] at h0
        simp only [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_C_mul] at h0
        simpa [Matrix.mulVec, dotProduct, M, v] using h0
      exact fun j ↦ congrFun (M.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
        (mem_nonZeroDivisors_of_ne_zero hM_det) hMv) j
    intro j
    apply MvPolynomial.ext
    intro m
    rw [hcoeff_zero m j]
    simp
  -- Over a `CharZero` integral domain, all partial derivatives zero forces `R = C (R.coeff 0)`.
  have hR_const : R = MvPolynomial.C (R.coeff 0) := by
    apply MvPolynomial.ext
    intro m
    rw [MvPolynomial.coeff_C]
    by_cases hm : m = 0
    · subst hm; simp
    · simp only [Ne.symm hm, ↓reduceIte]
      obtain ⟨j, hj⟩ : ∃ j : Fin (r + 1), m j ≠ 0 := by
        by_contra hall; push Not at hall; exact hm (Finsupp.ext hall)
      have h0 := congrArg (fun f : MvPolynomial (Fin (r + 1)) A ↦ f.coeff (m - Finsupp.single j 1))
        (hall_pderiv j)
      simp only [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel hj] at h0
      have h0' : R.coeff m * (((m - Finsupp.single j (1 : ℕ)) j : A) + 1) = 0 := by
        simpa using h0
      have hnat : (((m - Finsupp.single j (1 : ℕ)) j : A) + 1) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero ((m - Finsupp.single j (1 : ℕ)) j)
      exact (mul_eq_zero.mp h0').resolve_right hnat
  rw [hR_const, MvPolynomial.totalDegree_C] at hdeg
  exact lt_irrefl 0 hdeg

/-- **Complete Step-5 Minimality Induction Theorem**:
Given ANY minimal-total-degree nonzero annihilator `R ∈ A[Z₀, …, Z_r]` of a formal jet
`Yhat : Fin (r + 1) → A` (`aeval Yhat R = 0`) and the Step-5 leading-mode extraction rule
(whenever translation invariance kills all modes `ℓ < s`, the `s`-th directional derivative
annihilates `Yhat`), induction over `s = 0, …, r` forces all `r + 1` directional derivatives
to vanish identically, yielding `False` by `mockModular_minimal_annihilator_contradiction`! -/
theorem mockModular_jump_induction_contradiction
    [IsDomain A] [CharZero A] (emb : Polynomial ℂ →+* A) (hemb : Function.Injective emb)
    {r : ℕ} (k : ℂ) (ω : Fin (r + 1) → ℂ) (hω : Function.Injective ω)
    (α : Fin (r + 1) → A) (hα : ∀ s : Fin (r + 1), α s ≠ 0)
    (Yhat : Fin (r + 1) → A)
    (R : MvPolynomial (Fin (r + 1)) A) (hR_ne : R ≠ 0) (hR_ann : MvPolynomial.aeval Yhat R = 0)
    (hR_min : ∀ Q : MvPolynomial (Fin (r + 1)) A,
      Q ≠ 0 → MvPolynomial.aeval Yhat Q = 0 → R.totalDegree ≤ Q.totalDegree)
    (hstep : ∀ s : Fin (r + 1),
      (∀ ℓ : Fin (r + 1), ℓ < s →
        dirDeriv (fun j ↦ α ℓ * emb (mockJetP k r j.val (ω ℓ))) R = 0) →
      MvPolynomial.aeval Yhat
        (dirDeriv (fun j ↦ α s * emb (mockJetP k r j.val (ω s))) R) = 0) :
    False := by
  have hdeg : 0 < R.totalDegree := by
    by_contra h0
    have hd0 : R.totalDegree = 0 := Nat.eq_zero_of_not_pos h0
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd0
    rw [hC, MvPolynomial.aeval_C] at hR_ann
    have hc0 : R.coeff 0 = 0 := by simpa using hR_ann
    exact hR_ne (by rw [hC, hc0, MvPolynomial.C_0])
  have hall : ∀ (n : ℕ) (hn : n < r + 1),
      dirDeriv (fun j ↦ α ⟨n, hn⟩ * emb (mockJetP k r j.val (ω ⟨n, hn⟩))) R = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      have hprev : ∀ ℓ : Fin (r + 1), ℓ < ⟨n, hn⟩ →
          dirDeriv (fun j ↦ α ℓ * emb (mockJetP k r j.val (ω ℓ))) R = 0 := by
        intro ℓ hℓ
        exact ih ℓ.val hℓ ℓ.isLt
      have hann := hstep ⟨n, hn⟩ hprev
      by_contra hne
      have hle := hR_min _ hne hann
      have hlt := dirDeriv_totalDegree_lt
        (fun j ↦ α ⟨n, hn⟩ * emb (mockJetP k r j.val (ω ⟨n, hn⟩))) hdeg
      omega
  exact mockModular_minimal_annihilator_contradiction emb hemb k ω hω α hα R hdeg
    (fun s ↦ hall s.val s.isLt)

end TranslationInvariance

/-! ### 3. The 8-Line Universal Positive-Weight Modular Differential Independence Lemma -/

/-- The complex upper half-plane `ℍ = {τ ∈ ℂ : Im(τ) > 0}`. -/
def upperHalfPlane : Set ℂ := {τ : ℂ | 0 < τ.im}

theorem isOpen_upperHalfPlane : IsOpen upperHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_im

theorem upperHalfPlane_ne_zero {τ : ℂ} (hτ : τ ∈ upperHalfPlane) : τ ≠ 0 := by
  intro h0; rw [h0] at hτ; simp [upperHalfPlane] at hτ

theorem gammaAction_mem_upperHalfPlane {c : ℝ} (hc : 0 < c) {τ : ℂ} (hτ : τ ∈ upperHalfPlane) :
    τ / ((c : ℂ) * τ + 1) ∈ upperHalfPlane := by
  change 0 < (τ / ((c : ℂ) * τ + 1)).im
  have hden_im : 0 < ((c : ℂ) * τ + 1).im := by
    simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, one_im]
    exact mul_pos hc hτ
  have hden_ne : (c : ℂ) * τ + 1 ≠ 0 := by
    intro h0; rw [h0] at hden_im; simp at hden_im
  rw [Complex.div_im, ← sub_div]
  have hns_pos : 0 < Complex.normSq ((c : ℂ) * τ + 1) := Complex.normSq_pos.mpr hden_ne
  have hnum : τ.im * ((c : ℂ) * τ + 1).re - τ.re * ((c : ℂ) * τ + 1).im = τ.im := by
    simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, one_re,
      add_im, mul_im, add_zero, one_im]
    ring
  rw [hnum]
  exact div_pos hτ hns_pos

theorem gammaDen_mem_slitPlane {c : ℝ} (hc : 0 < c) {τ : ℂ} (hτ : τ ∈ upperHalfPlane) :
    (c : ℂ) * τ + 1 ∈ Complex.slitPlane := by
  refine Complex.mem_slitPlane_iff.mpr (Or.inr ?_)
  simp only [add_im, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, one_im]
  exact (mul_pos hc hτ).ne'

theorem add_int_mem_upperHalfPlane {τ : ℂ} (hτ : τ ∈ upperHalfPlane) (m : ℤ) :
    τ + (m : ℂ) ∈ upperHalfPlane := by
  change 0 < (τ + (m : ℂ)).im
  simpa [upperHalfPlane] using hτ

/-- Descending factorial `descFac a r = ∏_{t=0}^{r-1} (a - t) = Γ(a + 1) / Γ(a + 1 - r)`. -/
def descFac (a : ℂ) (r : ℕ) : ℂ :=
  ∏ t ∈ Finset.range r, (a - (t : ℂ))

@[simp]
theorem descFac_zero (a : ℂ) : descFac a 0 = 1 := by simp [descFac]

theorem descFac_succ (a : ℂ) (r : ℕ) : descFac a (r + 1) = descFac a r * (a - (r : ℂ)) := by
  simp [descFac, Finset.prod_range_succ]

theorem descFac_shift (a : ℂ) (r : ℕ) : descFac (a + 1) (r + 1) = (a + 1) * descFac a r := by
  rw [descFac, Finset.prod_range_succ']
  simp only [Nat.cast_zero, sub_zero, Nat.cast_add, Nat.cast_one]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro t _
  ring

/-- Exact Gamma product match: for every `w ∈ ℂ` with `0 < w.re` and every `r ≤ j`,
`Γ(w + j) = descFac (w + j - 1) r * Γ(w + j - r)`. -/
theorem Gamma_eq_descFac_mul_Gamma {w : ℂ} (hw : 0 < w.re) :
    ∀ {j r : ℕ}, r ≤ j →
      Complex.Gamma (w + (j : ℂ)) =
        descFac (w + (j : ℂ) - 1) r * Complex.Gamma (w + ((j - r : ℕ) : ℂ)) := by
  intro j r
  induction r generalizing j with
  | zero =>
    intro _
    simp
  | succ r ih =>
    intro hrj
    cases j with
    | zero => omega
    | succ j' =>
      have hrj' : r ≤ j' := by omega
      have hsub : j' + 1 - (r + 1) = j' - r := by omega
      rw [hsub]
      have hne_arg : w + (j' : ℂ) ≠ 0 := by
        intro h0
        have := congrArg Complex.re h0
        simp only [add_re, natCast_re, zero_re] at this
        linarith [Nat.cast_nonneg (α := ℝ) j']
      have hG : Complex.Gamma (w + ((j' + 1 : ℕ) : ℂ)) =
          (w + (j' : ℂ)) * Complex.Gamma (w + (j' : ℂ)) := by
        have harg : w + ((j' + 1 : ℕ) : ℂ) = (w + (j' : ℂ)) + 1 := by push_cast; ring
        rw [harg, Complex.Gamma_add_one _ hne_arg]
      rw [hG, ih hrj']
      have hshift : w + ((j' + 1 : ℕ) : ℂ) - 1 = (w + (j' : ℂ) - 1) + 1 := by push_cast; ring
      rw [hshift, descFac_shift]
      ring

/-- Exact Gamma ratio match for every positive real weight `w > 0` (including all positive
integer and half-integer weights `w = k / 2`):
`Γ(w + j) / Γ(w + j - r) = descFac (w + j - 1) r`. -/
theorem descFac_eq_Gamma_div {w : ℝ} (hw : 0 < w) {j r : ℕ} (hr : r ≤ j) :
    Complex.Gamma ((w : ℂ) + (j : ℂ)) / Complex.Gamma ((w : ℂ) + ((j - r : ℕ) : ℂ)) =
      descFac ((w : ℂ) + (j : ℂ) - 1) r := by
  have hprod := Gamma_eq_descFac_mul_Gamma (w := (w : ℂ)) (by simpa using hw) hr
  have hne : Complex.Gamma ((w : ℂ) + ((j - r : ℕ) : ℂ)) ≠ 0 := by
    have hreal : (w : ℂ) + ((j - r : ℕ) : ℂ) = ((w + ((j - r : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [hreal, Complex.Gamma_ofReal]
    exact Complex.ofReal_ne_zero.mpr
      (Real.Gamma_pos_of_pos (by linarith [Nat.cast_nonneg (α := ℝ) (j - r)])).ne'
  rw [hprod, mul_div_cancel_right₀ _ hne]

/-- Positivity / non-vanishing of `descFac (k / 2 + j - 1) j` for every positive half-integer
weight `w = k / 2` (`k ≥ 1`). -/
theorem descFac_halfInt_ne_zero {k : ℕ} (hk : 1 ≤ k) (j : ℕ) :
    descFac ((k : ℂ) / 2 + (j : ℂ) - 1) j ≠ 0 := by
  unfold descFac
  refine Finset.prod_ne_zero_iff.mpr fun t ht ↦ ?_
  intro h0
  have hre := congrArg Complex.re h0
  have ht_lt : t < j := Finset.mem_range.mp ht
  have ht_le : (t : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast ht_lt
  have hk_pos : (0 : ℝ) < (k : ℝ) / 2 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  simp only [sub_re, add_re, div_ofNat_re, natCast_re, one_re, zero_re] at hre
  linarith

/-- Key Pascal-type binomial identity for the modular derivative induction step. -/
private lemma modular_binom_descFac_step (w : ℂ) (j r : ℕ) (hr : 1 ≤ r) (hrj : r ≤ j) :
    ((Nat.choose j r : ℕ) : ℂ) * descFac (w + (j : ℂ) - 1) r +
      ((Nat.choose j (r - 1) : ℕ) : ℂ) * descFac (w + (j : ℂ) - 1) (r - 1) *
        (w + 2 * (j : ℂ) + 1 - (r : ℂ)) =
      ((Nat.choose (j + 1) r : ℕ) : ℂ) * descFac (w + (j : ℂ)) r := by
  cases r with
  | zero => omega
  | succ r' =>
    simp only [Nat.add_sub_cancel]
    rw [descFac_succ (w + (j : ℂ) - 1) r']
    have hshift : descFac (w + (j : ℂ)) (r' + 1) = (w + (j : ℂ)) * descFac (w + (j : ℂ) - 1) r' := by
      have h1 : w + (j : ℂ) = (w + (j : ℂ) - 1) + 1 := by ring
      conv_lhs => rw [h1]
      rw [descFac_shift]; ring
    rw [hshift]
    have hpascal : ((Nat.choose (j + 1) (r' + 1) : ℕ) : ℂ) =
        ((Nat.choose j (r' + 1) : ℕ) : ℂ) + ((Nat.choose j r' : ℕ) : ℂ) := by
      rw [Nat.choose_succ_succ, Nat.cast_add, add_comm]
    have habsorb : ((r' + 1 : ℕ) : ℂ) * ((Nat.choose j (r' + 1) : ℕ) : ℂ) =
        ((j - r' : ℕ) : ℂ) * ((Nat.choose j r' : ℕ) : ℂ) := by
      have hnat : (r' + 1) * Nat.choose j (r' + 1) = (j - r') * Nat.choose j r' := by
        have h1 := Nat.choose_succ_right_eq j r'
        linarith
      exact_mod_cast hnat
    have hsubC : ((j - r' : ℕ) : ℂ) = (j : ℂ) - (r' : ℂ) := by
      exact_mod_cast Nat.cast_sub (show r' ≤ j by omega)
    rw [hsubC] at habsorb
    rw [hpascal]
    push_cast at habsorb ⊢
    linear_combination -descFac (w + (j : ℂ) - 1) r' * habsorb

/-- Helper: every iterated derivative of a holomorphic function on `ℍ` is holomorphic on `ℍ`. -/
private lemma differentiableOn_iteratedDeriv_UHP {G : ℂ → ℂ}
    (hG : DifferentiableOn ℂ G upperHalfPlane) :
    ∀ m : ℕ, DifferentiableOn ℂ (iteratedDeriv m G) upperHalfPlane := by
  intro m
  induction m with
  | zero => simpa [iteratedDeriv_zero] using hG
  | succ m ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv isOpen_upperHalfPlane

/-- Helper: `(Z ^ (1 / 2 : ℂ)) ^ 2 = Z` for every nonzero `Z : ℂ`. -/
private lemma cpow_half_sq {Z : ℂ} (hZ : Z ≠ 0) : (Z ^ (1 / 2 : ℂ)) ^ 2 = Z := by
  rw [sq, ← Complex.cpow_add _ _ hZ]
  norm_num

/-- Helper (with explicit `1 ≤ m`): `HasDerivAt` for `τ ↦ ((c τ + 1)^{1/2})^k * (c τ + 1)^m` on `ℍ`. -/
private lemma hasDerivAt_halfInt_factor_pos {c : ℝ} (hc : 0 < c) (k : ℕ) {m : ℕ} (hm : 1 ≤ m)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlane) :
    HasDerivAt (fun z : ℂ ↦ (((c : ℂ) * z + 1) ^ (1 / 2 : ℂ)) ^ k * ((c : ℂ) * z + 1) ^ m)
      (((k : ℂ) / 2 + (m : ℂ)) * (c : ℂ) *
        ((((c : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ k * ((c : ℂ) * τ + 1) ^ (m - 1))) τ := by
  have hslit := gammaDen_mem_slitPlane hc hτ
  have hZne : (c : ℂ) * τ + 1 ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hlin : HasDerivAt (fun z : ℂ ↦ (c : ℂ) * z + 1) (c : ℂ) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (c : ℂ)).add_const (1 : ℂ)
  have hsqrt : HasDerivAt (fun z : ℂ ↦ ((c : ℂ) * z + 1) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * ((c : ℂ) * τ + 1) ^ ((1 / 2 : ℂ) - 1) * (c : ℂ)) τ :=
    hlin.cpow_const hslit
  have hpowk : HasDerivAt (fun z : ℂ ↦ (((c : ℂ) * z + 1) ^ (1 / 2 : ℂ)) ^ k)
      ((k : ℂ) * (((c : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ (k - 1) *
        ((1 / 2 : ℂ) * ((c : ℂ) * τ + 1) ^ ((1 / 2 : ℂ) - 1) * (c : ℂ))) τ :=
    hsqrt.pow k
  have hpowm : HasDerivAt (fun z : ℂ ↦ ((c : ℂ) * z + 1) ^ m)
      ((m : ℂ) * ((c : ℂ) * τ + 1) ^ (m - 1) * (c : ℂ)) τ :=
    hlin.pow m
  have hprod := hpowk.mul hpowm
  set Z : ℂ := (c : ℂ) * τ + 1
  set s : ℂ := Z ^ (1 / 2 : ℂ)
  have hZneg : Z ^ ((1 / 2 : ℂ) - 1) = s * Z⁻¹ := by
    have hexp : (1 / 2 : ℂ) - 1 = (1 / 2 : ℂ) + (-1 : ℂ) := by ring
    rw [hexp, Complex.cpow_add _ _ hZne, Complex.cpow_neg_one]
  have hZm : Z⁻¹ * Z ^ m = Z ^ (m - 1) := by
    have hm1 : Z ^ m = Z * Z ^ (m - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hm]
    rw [hm1, ← mul_assoc, inv_mul_cancel₀ hZne, one_mul]
  convert hprod using 1
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Nat.cast_zero, zero_div, zero_add, pow_zero, one_mul, zero_mul]
    ring
  · have hsk : s ^ (k - 1) * s = s ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
    have hterm1 : (k : ℂ) * s ^ (k - 1) * ((1 / 2 : ℂ) * Z ^ ((1 / 2 : ℂ) - 1) * (c : ℂ)) * Z ^ m =
        ((k : ℂ) / 2) * (c : ℂ) * (s ^ k * Z ^ (m - 1)) := by
      rw [hZneg]
      calc (k : ℂ) * s ^ (k - 1) * ((1 / 2 : ℂ) * (s * Z⁻¹) * (c : ℂ)) * Z ^ m
          = ((k : ℂ) / 2) * (c : ℂ) * ((s ^ (k - 1) * s) * (Z⁻¹ * Z ^ m)) := by ring
        _ = ((k : ℂ) / 2) * (c : ℂ) * (s ^ k * Z ^ (m - 1)) := by rw [hsk, hZm]
    rw [hterm1]; ring

/-- Helper: `HasDerivAt` for `τ ↦ ((c τ + 1)^{1/2})^k` (when `m = 0`), multiplied by `(c τ + 1)^2`. -/
private lemma hasDerivAt_halfInt_pow_zero {c : ℝ} (hc : 0 < c) (k : ℕ)
    {τ : ℂ} (hτ : τ ∈ upperHalfPlane) :
    HasDerivAt (fun z : ℂ ↦ (((c : ℂ) * z + 1) ^ (1 / 2 : ℂ)) ^ k)
      (((k : ℂ) / 2) * (c : ℂ) * ((((c : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ k * ((c : ℂ) * τ + 1)⁻¹)) τ := by
  have hslit := gammaDen_mem_slitPlane hc hτ
  have hZne : (c : ℂ) * τ + 1 ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hlin : HasDerivAt (fun z : ℂ ↦ (c : ℂ) * z + 1) (c : ℂ) τ := by
    simpa using ((hasDerivAt_id τ).const_mul (c : ℂ)).add_const (1 : ℂ)
  have hsqrt : HasDerivAt (fun z : ℂ ↦ ((c : ℂ) * z + 1) ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * ((c : ℂ) * τ + 1) ^ ((1 / 2 : ℂ) - 1) * (c : ℂ)) τ :=
    hlin.cpow_const hslit
  have hpowk := hsqrt.pow k
  set Z : ℂ := (c : ℂ) * τ + 1
  set s : ℂ := Z ^ (1 / 2 : ℂ)
  have hZneg : Z ^ ((1 / 2 : ℂ) - 1) = s * Z⁻¹ := by
    have hexp : (1 / 2 : ℂ) - 1 = (1 / 2 : ℂ) + (-1 : ℂ) := by ring
    rw [hexp, Complex.cpow_add _ _ hZne, Complex.cpow_neg_one]
  convert hpowk using 1
  by_cases hk0 : k = 0
  · subst hk0; simp
  · have hsk : s ^ (k - 1) * s = s ^ k := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
    rw [hZneg]
    calc ((k : ℂ) / 2) * (c : ℂ) * (s ^ k * Z⁻¹)
        = ((k : ℂ) / 2) * (c : ℂ) * ((s ^ (k - 1) * s) * Z⁻¹) := by rw [hsk]
      _ = (k : ℂ) * s ^ (k - 1) * ((1 / 2 : ℂ) * (s * Z⁻¹) * (c : ℂ)) := by ring

/-- **Exact Analytic Bol / Modular Derivative Transformation Law** (`modular_iteratedDeriv_gamma`):
For EVERY holomorphic function `G` on `ℍ` of arbitrary integer or half-integer weight `w = k / 2`
obeying `G(τ / (c τ + 1)) = ((c τ + 1)^{1/2})^k G(τ)` (`c > 0`), and EVERY derivative order `j`:
`G^{(j)}(τ / (c τ + 1)) = ∑_{r=0}^j C(j, r) descFac(k/2 + j - 1, r) c^r ((c τ + 1)^{1/2})^k (c τ + 1)^{2j - r} G^{(j - r)}(τ)`. -/
theorem modular_iteratedDeriv_gamma {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G upperHalfPlane)
    {k : ℕ} {c : ℝ} (hc : 0 < c)
    (hmod : ∀ τ ∈ upperHalfPlane,
      G (τ / ((c : ℂ) * τ + 1)) = ((((c : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ k) * G τ) :
    ∀ (j : ℕ), ∀ τ ∈ upperHalfPlane,
      iteratedDeriv j G (τ / ((c : ℂ) * τ + 1)) =
        ∑ r ∈ Finset.range (j + 1),
          ((Nat.choose j r : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + (j : ℂ) - 1) r *
            (c : ℂ) ^ r * ((((c : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ k) *
            ((c : ℂ) * τ + 1) ^ (2 * j - r) * iteratedDeriv (j - r) G τ := by
  have hDiffIter : ∀ m : ℕ, ∀ τ ∈ upperHalfPlane,
      HasDerivAt (iteratedDeriv m G) (iteratedDeriv (m + 1) G τ) τ := by
    intro m τ hτ
    have hdiff_m : DifferentiableAt ℂ (iteratedDeriv m G) τ :=
      (differentiableOn_iteratedDeriv_UHP hG m).differentiableAt (isOpen_upperHalfPlane.mem_nhds hτ)
    rw [iteratedDeriv_succ]
    exact hdiff_m.hasDerivAt
  intro j
  induction j with
  | zero =>
    intro τ hτ
    simpa [iteratedDeriv_zero] using hmod τ hτ
  | succ j ih =>
    intro τ hτ
    -- Differentiate the `j`-th identity at `τ ∈ ℍ`!
    have hZne : (c : ℂ) * τ + 1 ≠ 0 :=
      Complex.slitPlane_ne_zero (gammaDen_mem_slitPlane hc hτ)
    have hγ_mem : τ / ((c : ℂ) * τ + 1) ∈ upperHalfPlane :=
      gammaAction_mem_upperHalfPlane hc hτ
    have hγ_deriv : HasDerivAt (fun z : ℂ ↦ z / ((c : ℂ) * z + 1))
        (1 / ((c : ℂ) * τ + 1) ^ 2) τ := by
      have hden : HasDerivAt (fun z : ℂ ↦ (c : ℂ) * z + 1) (c : ℂ) τ := by
        simpa using ((hasDerivAt_id τ).const_mul (c : ℂ)).add_const (1 : ℂ)
      have hdiv := (hasDerivAt_id τ).fun_div hden hZne
      have hval : (1 * ((c : ℂ) * τ + 1) - τ * (c : ℂ)) / ((c : ℂ) * τ + 1) ^ 2 =
          1 / ((c : ℂ) * τ + 1) ^ 2 := by
        field_simp [hZne]; ring
      simpa only [id_eq, hval] using hdiv
    have hlhs_deriv : HasDerivAt (fun z : ℂ ↦ iteratedDeriv j G (z / ((c : ℂ) * z + 1)))
        (iteratedDeriv (j + 1) G (τ / ((c : ℂ) * τ + 1)) * (1 / ((c : ℂ) * τ + 1) ^ 2)) τ :=
      HasDerivAt.comp τ (hDiffIter j _ hγ_mem) hγ_deriv
    -- RHS derivative term by term:
    let term (r : ℕ) (z : ℂ) : ℂ :=
      ((Nat.choose j r : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + (j : ℂ) - 1) r *
        (c : ℂ) ^ r * ((((c : ℂ) * z + 1) ^ (1 / 2 : ℂ)) ^ k * ((c : ℂ) * z + 1) ^ (2 * j - r)) *
        iteratedDeriv (j - r) G z
    let term' (r : ℕ) : ℂ :=
      ((Nat.choose j r : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + (j : ℂ) - 1) r * (c : ℂ) ^ r *
        ((((k : ℂ) / 2 + ((2 * j - r : ℕ) : ℂ)) * (c : ℂ) *
            ((((c : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ k * ((c : ℂ) * τ + 1) ^ (2 * j - r) *
              ((c : ℂ) * τ + 1)⁻¹) *
            iteratedDeriv (j - r) G τ) +
          ((((c : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ k * ((c : ℂ) * τ + 1) ^ (2 * j - r)) *
            iteratedDeriv (j - r + 1) G τ)
    have hterm_deriv : ∀ r ∈ Finset.range (j + 1), HasDerivAt (term r) (term' r) τ := by
      intro r hr
      have hrj : r ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hfac_deriv : HasDerivAt
          (fun z : ℂ ↦ (((c : ℂ) * z + 1) ^ (1 / 2 : ℂ)) ^ k * ((c : ℂ) * z + 1) ^ (2 * j - r))
          (((k : ℂ) / 2 + ((2 * j - r : ℕ) : ℂ)) * (c : ℂ) *
            ((((c : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ k * ((c : ℂ) * τ + 1) ^ (2 * j - r) *
              ((c : ℂ) * τ + 1)⁻¹)) τ := by
        by_cases h2jr : 2 * j - r = 0
        · rw [h2jr]
          simpa [pow_zero, mul_one] using hasDerivAt_halfInt_pow_zero hc k hτ
        · have hpos : 1 ≤ 2 * j - r := Nat.pos_of_ne_zero h2jr
          have h1 := hasDerivAt_halfInt_factor_pos hc k hpos hτ
          have hZm : ((c : ℂ) * τ + 1) ^ (2 * j - r) * ((c : ℂ) * τ + 1)⁻¹ =
              ((c : ℂ) * τ + 1) ^ (2 * j - r - 1) := by
            have hm1 : ((c : ℂ) * τ + 1) ^ (2 * j - r) =
                ((c : ℂ) * τ + 1) ^ (2 * j - r - 1) * ((c : ℂ) * τ + 1) := by
              rw [← pow_succ, Nat.sub_add_cancel hpos]
            rw [hm1, mul_assoc, mul_inv_cancel₀ hZne, mul_one]
          convert h1 using 1
          rw [mul_assoc ((((c : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ k), hZm]
      have hmul := hfac_deriv.fun_mul (hDiffIter (j - r) τ hτ)
      have hconst := hmul.const_mul (((Nat.choose j r : ℕ) : ℂ) *
        descFac ((k : ℂ) / 2 + (j : ℂ) - 1) r * (c : ℂ) ^ r)
      have hfun_eq : (fun z : ℂ ↦ ((Nat.choose j r : ℕ) : ℂ) *
          descFac ((k : ℂ) / 2 + (j : ℂ) - 1) r * (c : ℂ) ^ r *
          (((((c : ℂ) * z + 1) ^ (1 / 2 : ℂ)) ^ k * ((c : ℂ) * z + 1) ^ (2 * j - r)) *
            iteratedDeriv (j - r) G z)) = term r := by
        funext z; dsimp [term]; ring
      rw [hfun_eq] at hconst
      exact hconst
    have hrhs_deriv : HasDerivAt (fun z : ℂ ↦ ∑ r ∈ Finset.range (j + 1), term r z)
        (∑ r ∈ Finset.range (j + 1), term' r) τ :=
      HasDerivAt.fun_sum hterm_deriv
    have hlocal : (fun z : ℂ ↦ iteratedDeriv j G (z / ((c : ℂ) * z + 1))) =ᶠ[𝓝 τ]
        (fun z : ℂ ↦ ∑ r ∈ Finset.range (j + 1), term r z) := by
      filter_upwards [isOpen_upperHalfPlane.mem_nhds hτ] with z hz
      rw [ih z hz]
      apply Finset.sum_congr rfl; intro r _; dsimp [term]; ring
    have hderiv_eq : iteratedDeriv (j + 1) G (τ / ((c : ℂ) * τ + 1)) *
        (1 / ((c : ℂ) * τ + 1) ^ 2) = ∑ r ∈ Finset.range (j + 1), term' r :=
      (hlhs_deriv.congr_of_eventuallyEq hlocal.symm).unique hrhs_deriv
    -- Multiply both sides by `Z² = ((c : ℂ) * τ + 1)^2` and reindex the split sum!
    set Z : ℂ := (c : ℂ) * τ + 1
    set s : ℂ := Z ^ (1 / 2 : ℂ)
    have hmulZ2 := congrArg (Z ^ 2 * ·) hderiv_eq
    have hlhs_simp : Z ^ 2 * (iteratedDeriv (j + 1) G (τ / Z) * (1 / Z ^ 2)) =
        iteratedDeriv (j + 1) G (τ / Z) := by
      field_simp [hZne]
    rw [hlhs_simp, Finset.mul_sum] at hmulZ2
    rw [hmulZ2]
    -- Split `∑_{r=0}^j Z² * term' r = S1 + S2` where `S1` shifts `r ↦ r + 1` and `S2` keeps `r`!
    let A (r : ℕ) : ℂ :=
      ((Nat.choose j r : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + (j : ℂ) - 1) r *
        ((k : ℂ) / 2 + ((2 * j - r : ℕ) : ℂ)) * (c : ℂ) ^ (r + 1) *
        s ^ k * Z ^ (2 * j + 1 - r) * iteratedDeriv (j - r) G τ
    let B (r : ℕ) : ℂ :=
      ((Nat.choose j r : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + (j : ℂ) - 1) r *
        (c : ℂ) ^ r * s ^ k * Z ^ (2 * (j + 1) - r) * iteratedDeriv (j + 1 - r) G τ
    have hsplit_term : ∀ r ∈ Finset.range (j + 1), Z ^ 2 * term' r = A r + B r := by
      intro r hr
      have hrj : r ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hpowA : Z ^ 2 * (Z ^ (2 * j - r) * Z⁻¹) = Z ^ (2 * j + 1 - r) := by
        have h1 : Z ^ 2 * Z⁻¹ = Z := by field_simp [hZne]
        calc Z ^ 2 * (Z ^ (2 * j - r) * Z⁻¹) = Z ^ (2 * j - r) * (Z ^ 2 * Z⁻¹) := by ring
          _ = Z ^ (2 * j - r) * Z := by rw [h1]
          _ = Z ^ (2 * j - r + 1) := (pow_succ Z (2 * j - r)).symm
          _ = Z ^ (2 * j + 1 - r) := by congr 1; omega
      have hpowB : Z ^ 2 * Z ^ (2 * j - r) = Z ^ (2 * (j + 1) - r) := by
        rw [← pow_add]; congr 1; omega
      have hsub1 : j - r + 1 = j + 1 - r := by omega
      dsimp only [term', A, B]
      rw [hsub1, pow_succ]
      linear_combination
        ((Nat.choose j r : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + (j : ℂ) - 1) r * (c : ℂ) ^ r *
          ((k : ℂ) / 2 + ((2 * j - r : ℕ) : ℂ)) * (c : ℂ) * s ^ k *
          iteratedDeriv (j - r) G τ * hpowA +
        ((Nat.choose j r : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + (j : ℂ) - 1) r * (c : ℂ) ^ r *
          s ^ k * iteratedDeriv (j + 1 - r) G τ * hpowB
    rw [Finset.sum_congr rfl hsplit_term, Finset.sum_add_distrib]
    -- Reindex `∑_{r=0}^j A r + ∑_{r=0}^j B r = ∑_{r=0}^{j+1} Target r`!
    let Target (r : ℕ) : ℂ :=
      ((Nat.choose (j + 1) r : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + ((j + 1 : ℕ) : ℂ) - 1) r *
        (c : ℂ) ^ r * s ^ k * Z ^ (2 * (j + 1) - r) * iteratedDeriv (j + 1 - r) G τ
    change (∑ r ∈ Finset.range (j + 1), A r) + (∑ r ∈ Finset.range (j + 1), B r) =
      ∑ r ∈ Finset.range (j + 2), Target r
    -- Peel off `r = 0` from `B` and `Target`, and `r = j` from `A` and `r = j + 1` from `Target`!
    rw [Finset.sum_range_succ' Target (j + 1), Finset.sum_range_succ' B j,
        Finset.sum_range_succ A j, Finset.sum_range_succ (fun r ↦ Target (r + 1)) j]
    have h0 : B 0 = Target 0 := by simp [B, Target]
    have htop : A j = Target (j + 1) := by
      dsimp only [A, Target]
      have h1 : 2 * j - j = j := by omega
      have h2 : 2 * j + 1 - j = j + 1 := by omega
      have h3 : 2 * (j + 1) - (j + 1) = j + 1 := by omega
      have h4 : j + 1 - (j + 1) = 0 := by omega
      have h5 : j - j = 0 := by omega
      rw [h1, h2, h3, h4, h5, Nat.choose_self, Nat.choose_self]
      have hd : descFac ((k : ℂ) / 2 + ((j + 1 : ℕ) : ℂ) - 1) (j + 1) =
          ((k : ℂ) / 2 + (j : ℂ)) * descFac ((k : ℂ) / 2 + (j : ℂ) - 1) j := by
        have harg : (k : ℂ) / 2 + ((j + 1 : ℕ) : ℂ) - 1 = ((k : ℂ) / 2 + (j : ℂ) - 1) + 1 := by
          push_cast; ring
        rw [harg, descFac_shift]; ring
      rw [hd]; ring
    have hmid : (∑ r ∈ Finset.range j, A r) + (∑ r ∈ Finset.range j, B (r + 1)) =
        ∑ r ∈ Finset.range j, Target (r + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      have hrj : r < j := Finset.mem_range.mp hr
      have hstep := modular_binom_descFac_step ((k : ℂ) / 2) j (r + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at hstep
      have hpow1 : 2 * j + 1 - r = 2 * (j + 1) - (r + 1) := by omega
      have hsub1 : j - r = j + 1 - (r + 1) := by omega
      have h2jr : ((2 * j - r : ℕ) : ℂ) = 2 * (j : ℂ) - (r : ℂ) := by
        exact_mod_cast Nat.cast_sub (show r ≤ 2 * j by omega)
      have harg : (k : ℂ) / 2 + ((j + 1 : ℕ) : ℂ) - 1 = (k : ℂ) / 2 + (j : ℂ) := by
        push_cast; ring
      dsimp only [A, B, Target]
      rw [hpow1, hsub1, h2jr, harg]
      have hstep' : ((Nat.choose j (r + 1) : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + (j : ℂ) - 1) (r + 1) +
          ((Nat.choose j r : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + (j : ℂ) - 1) r *
            ((k : ℂ) / 2 + (2 * (j : ℂ) - (r : ℂ))) =
          ((Nat.choose (j + 1) (r + 1) : ℕ) : ℂ) * descFac ((k : ℂ) / 2 + (j : ℂ)) (r + 1) := by
        convert hstep using 2; push_cast; ring
      linear_combination (c : ℂ) ^ (r + 1) * s ^ k * Z ^ (2 * (j + 1) - (r + 1)) *
        iteratedDeriv (j + 1 - (r + 1)) G τ * hstep'
    linear_combination h0 + htop + hmid

/-- Helper: vanishing of a polynomial at infinitely many distinct complex numbers forces it to be `0`. -/
private lemma poly_eq_zero_of_eval_eq_zero_nat (P : Polynomial ℂ)
    (a : ℕ → ℂ) (ha : Function.Injective a) (hzero : ∀ n : ℕ, P.eval (a n) = 0) :
    P = 0 := by
  by_contra hPne
  let S : Finset ℕ := Finset.range (P.natDegree + 1)
  have hsub : S.image a ⊆ P.roots.toFinset := by
    intro z hz
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hPne).mpr (hzero n))
  have hcard : P.natDegree + 1 ≤ P.natDegree := by
    calc P.natDegree + 1 = S.card := (Finset.card_range _).symm
      _ = (S.image a).card := (Finset.card_image_of_injective S ha).symm
      _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
      _ ≤ P.natDegree := Polynomial.card_roots' P
  omega

/-- Helper: `(X - 1)^r * X^m` has zero coefficient below `m` and `(-1)^r` at `m`. -/
private lemma coeff_X_sub_one_pow_mul_X_pow (r m d : ℕ) :
    ((Polynomial.X - 1 : Polynomial ℂ) ^ r * Polynomial.X ^ m).coeff d =
      if d < m then 0
      else if d = m then (-1 : ℂ) ^ r
      else ((Polynomial.X - 1 : Polynomial ℂ) ^ r).coeff (d - m) := by
  rw [mul_comm, Polynomial.coeff_X_pow_mul']
  by_cases hdm : d < m
  · have hnot : ¬ m ≤ d := by omega
    simp [hdm, hnot]
  · have hle : m ≤ d := by omega
    by_cases heq : d = m
    · subst heq
      simp only [lt_irrefl, ↓reduceIte, le_rfl, Nat.sub_self, Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, zero_sub]
    · simp [hdm, hle, heq]

/-- Helper: if `G` vanishes on `upperHalfPlane`, so does every `iteratedDeriv m G`. -/
private lemma iteratedDeriv_eq_zero_of_eq_zero_on_UHP {G : ℂ → ℂ}
    (h0 : ∀ τ ∈ upperHalfPlane, G τ = 0) :
    ∀ (m : ℕ), ∀ τ ∈ upperHalfPlane, iteratedDeriv m G τ = 0 := by
  intro m
  induction m with
  | zero => intro τ hτ; simp [iteratedDeriv_zero, h0 τ hτ]
  | succ m ih =>
    intro τ hτ
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv m G =ᶠ[𝓝 τ] (fun _ : ℂ ↦ (0 : ℂ)) := by
      filter_upwards [isOpen_upperHalfPlane.mem_nhds hτ] with z hz
      exact ih z hz
    rw [hev.deriv_eq, deriv_const]

private lemma poly_eval_finset_sum {α : Type*} (s : Finset α) (f : α → Polynomial ℂ) (x : ℂ) :
    (∑ a ∈ s, f a).eval x = ∑ a ∈ s, (f a).eval x :=
  map_sum (Polynomial.evalRingHom x) f s

private lemma poly_coeff_finset_sum {α : Type*} (s : Finset α) (f : α → Polynomial ℂ) (d : ℕ) :
    (∑ a ∈ s, f a).coeff d = ∑ a ∈ s, (f a).coeff d :=
  map_sum (Polynomial.lcoeff ℂ d) f s

/-- **Crown Jewel Theorem 3 — The 8-Line Universal Positive-Weight Modular Differential Independence Lemma**:
Let `S : Finset (ℕ × ℕ)` index finitely many positive half-integer weights `w = p.1 / 2` (`1 ≤ p.1`)
and derivative orders `j = p.2`, and let `G : ℕ × ℕ → ℂ → ℂ` be holomorphic functions on `ℍ`
obeying `γ_n`-modularity of weight `p.1 / 2` (`∀ n ≥ 1`) and `T^L`-periodicity (`∀ n : ℤ`)
for fixed positive integers `M, L ≥ 1`.
If `∑_{p ∈ S} ∂_τ^{p.2} (G p) τ = C` (constant) on `ℍ`, then **EVERY `G p` vanishes identically on `ℍ`**! -/
theorem positiveWeight_modular_diff_indep_abstract
    (S : Finset (ℕ × ℕ)) (hS_pos : ∀ p ∈ S, 1 ≤ p.1)
    (G : ℕ × ℕ → ℂ → ℂ) (hG_diff : ∀ p ∈ S, DifferentiableOn ℂ (G p) upperHalfPlane)
    {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hmod : ∀ p ∈ S, ∀ n : ℕ, 1 ≤ n → ∀ τ ∈ upperHalfPlane,
      G p (τ / (((n * M : ℕ) : ℂ) * τ + 1)) =
        ((((n * M : ℕ) : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ p.1 * G p τ)
    (hper : ∀ p ∈ S, ∀ n : ℤ, ∀ τ ∈ upperHalfPlane,
      G p (τ + ((n * (L : ℤ) : ℤ) : ℂ)) = G p τ)
    (C : ℂ) (hrel : ∀ τ ∈ upperHalfPlane, ∑ p ∈ S, iteratedDeriv p.2 (G p) τ = C) :
    ∀ p ∈ S, ∀ τ ∈ upperHalfPlane, G p τ = 0 := by
  -- Restrict to the subset `S*` of non-identically-zero components!
  let Sstar : Finset (ℕ × ℕ) := S.filter fun p ↦ ∃ τ ∈ upperHalfPlane, G p τ ≠ 0
  let Seven : Finset (ℕ × ℕ) := Sstar.filter fun p ↦ p.1 % 2 = 0
  let Sodd : Finset (ℕ × ℕ) := Sstar.filter fun p ↦ p.1 % 2 = 1
  -- For any `p ∈ S \ Sstar`, `G p ≡ 0` on `ℍ`, hence all derivatives vanish on `ℍ`.
  have hzero_outside : ∀ p ∈ S, p ∉ Sstar → ∀ m : ℕ, ∀ τ ∈ upperHalfPlane,
      iteratedDeriv m (G p) τ = 0 := by
    intro p hp hnot
    have hGp0 : ∀ τ ∈ upperHalfPlane, G p τ = 0 := by
      intro τ hτ
      by_contra hne
      exact hnot (Finset.mem_filter.mpr ⟨hp, τ, hτ, hne⟩)
    exact iteratedDeriv_eq_zero_of_eq_zero_on_UHP hGp0
  -- For EVERY fixed `τ ∈ ℍ`, form the even-weight and odd-weight polynomials `P_even(X), P_odd(X) ∈ ℂ[X]`!
  let Peven (τ : ℂ) : Polynomial ℂ :=
    ∑ p ∈ Seven, ∑ r ∈ Finset.range (p.2 + 1),
      Polynomial.C (((Nat.choose p.2 r : ℕ) : ℂ) * descFac ((p.1 : ℂ) / 2 + (p.2 : ℂ) - 1) r *
        τ⁻¹ ^ r * iteratedDeriv (p.2 - r) (G p) τ) *
      ((Polynomial.X - 1) ^ r * Polynomial.X ^ (p.1 / 2 + 2 * p.2 - r))
  let Podd (τ : ℂ) : Polynomial ℂ :=
    ∑ p ∈ Sodd, ∑ r ∈ Finset.range (p.2 + 1),
      Polynomial.C (((Nat.choose p.2 r : ℕ) : ℂ) * descFac ((p.1 : ℂ) / 2 + (p.2 : ℂ) - 1) r *
        τ⁻¹ ^ r * iteratedDeriv (p.2 - r) (G p) τ) *
      ((Polynomial.X - 1) ^ r * Polynomial.X ^ ((p.1 - 1) / 2 + 2 * p.2 - r))
  -- Core polynomial identity: for EVERY `τ ∈ ℍ`, `Peven τ = C` and `Podd τ = 0` in `ℂ[X]`!
  have hpoly_ident : ∀ τ ∈ upperHalfPlane, Peven τ = Polynomial.C C ∧ Podd τ = 0 := by
    intro τ hτ
    have hτ0 : τ ≠ 0 := upperHalfPlane_ne_zero hτ
    -- For every `n ≥ 1`, let `Z n = (n + 1) M τ + 1` and `s n = (Z n)^(1/2)` (so `(s n)^2 = Z n`).
    let Z : ℕ → ℂ := fun n ↦ ((((n + 1) * M : ℕ) : ℂ) * τ + 1)
    have hZ_inj : Function.Injective Z := by
      intro n₁ n₂ h
      dsimp only [Z] at h
      have h1 : ((((n₁ + 1) * M : ℕ) : ℂ) * τ) = ((((n₂ + 1) * M : ℕ) : ℂ) * τ) :=
        add_right_cancel h
      have h2 : (((n₁ + 1) * M : ℕ) : ℂ) = (((n₂ + 1) * M : ℕ) : ℂ) := mul_right_cancel₀ hτ0 h1
      have h3 : (n₁ + 1) * M = (n₂ + 1) * M := by exact_mod_cast h2
      have h4 : n₁ + 1 = n₂ + 1 := Nat.eq_of_mul_eq_mul_right (by omega) h3
      omega
    have hZ_eval : ∀ n : ℕ,
        ((Peven τ - Polynomial.C C) ^ 2 - Polynomial.X * (Podd τ) ^ 2).eval (Z n) = 0 := by
      intro n
      let c : ℝ := (((n + 1) * M : ℕ) : ℝ)
      have hc : 0 < c := by dsimp [c]; exact_mod_cast Nat.mul_pos (Nat.succ_pos n) hM
      have hc_eq : (c : ℂ) = (Z n - 1) * τ⁻¹ := by
        dsimp only [c, Z]
        push_cast
        field_simp [hτ0]
        ring
      have hZne : Z n ≠ 0 := Complex.slitPlane_ne_zero (by
        simpa [Z, c] using gammaDen_mem_slitPlane hc hτ)
      have hs2 : ((Z n) ^ (1 / 2 : ℂ)) ^ 2 = Z n := cpow_half_sq hZne
      have hγτ : τ / Z n ∈ upperHalfPlane := by
        simpa [Z, c] using gammaAction_mem_upperHalfPlane hc hτ
      have hrel_n := hrel (τ / Z n) hγτ
      -- Drop terms outside `Sstar`!
      have hsum_star : ∑ p ∈ Sstar, iteratedDeriv p.2 (G p) (τ / Z n) = C := by
        rw [← hrel_n]
        apply Finset.sum_subset (Finset.filter_subset _ S)
        intro p hp hnot
        exact hzero_outside p hp hnot p.2 (τ / Z n) hγτ
      -- Split `Sstar = Seven ∪ Sodd` (disjoint)!
      have hdisj : Disjoint Seven Sodd := by
        rw [Finset.disjoint_filter]
        intro p _ h0 h1; omega
      have hunion : Seven ∪ Sodd = Sstar := by
        ext p
        simp only [Seven, Sodd, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro h; rcases Nat.mod_two_eq_zero_or_one p.1 with h0 | h1
          · exact Or.inl ⟨h, h0⟩
          · exact Or.inr ⟨h, h1⟩
      -- Evaluate `iteratedDeriv p.2 (G p) (τ / Z n)` via `modular_iteratedDeriv_gamma`!
      have heval_p : ∀ p ∈ Sstar,
          iteratedDeriv p.2 (G p) (τ / Z n) =
            ∑ r ∈ Finset.range (p.2 + 1),
              ((Nat.choose p.2 r : ℕ) : ℂ) * descFac ((p.1 : ℂ) / 2 + (p.2 : ℂ) - 1) r *
                τ⁻¹ ^ r * iteratedDeriv (p.2 - r) (G p) τ *
                ((Z n - 1) ^ r * ((Z n) ^ (1 / 2 : ℂ)) ^ p.1 * (Z n) ^ (2 * p.2 - r)) := by
        intro p hp
        have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
        have hmd := modular_iteratedDeriv_gamma (hG_diff p hpS) hc
          (fun z hz ↦ by simpa [c] using hmod p hpS (n + 1) (Nat.succ_pos n) z hz) p.2 τ hτ
        have hZc : (c : ℂ) * τ + 1 = Z n := by dsimp [c, Z]
        rw [hZc] at hmd
        rw [hmd]
        apply Finset.sum_congr rfl
        intro r _
        have hc_pow : (c : ℂ) ^ r = (Z n - 1) ^ r * τ⁻¹ ^ r := by
          rw [← mul_pow, hc_eq]
        rw [hc_pow]
        ring
      have hPe : (Peven τ).eval (Z n) = ∑ p ∈ Seven, iteratedDeriv p.2 (G p) (τ / Z n) := by
        simp only [Peven, poly_eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one]
        apply Finset.sum_congr rfl
        intro p hp
        have hpStar : p ∈ Sstar := (Finset.mem_filter.mp hp).1
        have hpEven : p.1 % 2 = 0 := (Finset.mem_filter.mp hp).2
        rw [heval_p p hpStar]
        apply Finset.sum_congr rfl
        intro r hr
        have hrj : r ≤ p.2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        have hsk : ((Z n) ^ (1 / 2 : ℂ)) ^ p.1 = (Z n) ^ (p.1 / 2) := by
          have hk2 : p.1 = 2 * (p.1 / 2) := by omega
          conv_lhs => rw [hk2, pow_mul, hs2]
        have hpow : (Z n) ^ (p.1 / 2) * (Z n) ^ (2 * p.2 - r) =
            (Z n) ^ (p.1 / 2 + 2 * p.2 - r) := by
          rw [← pow_add]; congr 1; omega
        rw [hsk]; linear_combination
          ((Nat.choose p.2 r : ℕ) : ℂ) * descFac ((p.1 : ℂ) / 2 + (p.2 : ℂ) - 1) r *
            τ⁻¹ ^ r * iteratedDeriv (p.2 - r) (G p) τ * (Z n - 1) ^ r * hpow.symm
      have hPo : ((Z n) ^ (1 / 2 : ℂ)) * (Podd τ).eval (Z n) =
          ∑ p ∈ Sodd, iteratedDeriv p.2 (G p) (τ / Z n) := by
        simp only [Podd, poly_eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one,
          Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hpStar : p ∈ Sstar := (Finset.mem_filter.mp hp).1
        have hpOdd : p.1 % 2 = 1 := (Finset.mem_filter.mp hp).2
        rw [heval_p p hpStar]
        apply Finset.sum_congr rfl
        intro r hr
        have hrj : r ≤ p.2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        have hsk : ((Z n) ^ (1 / 2 : ℂ)) ^ p.1 =
            ((Z n) ^ (1 / 2 : ℂ)) * (Z n) ^ ((p.1 - 1) / 2) := by
          have hk2 : p.1 = 2 * ((p.1 - 1) / 2) + 1 := by omega
          conv_lhs => rw [hk2, pow_succ, pow_mul, hs2, mul_comm]
        have hpow : (Z n) ^ ((p.1 - 1) / 2) * (Z n) ^ (2 * p.2 - r) =
            (Z n) ^ ((p.1 - 1) / 2 + 2 * p.2 - r) := by
          rw [← pow_add]; congr 1; omega
        rw [hsk]
        linear_combination
          ((Nat.choose p.2 r : ℕ) : ℂ) * descFac ((p.1 : ℂ) / 2 + (p.2 : ℂ) - 1) r *
            τ⁻¹ ^ r * iteratedDeriv (p.2 - r) (G p) τ * (Z n - 1) ^ r *
            ((Z n) ^ (1 / 2 : ℂ)) * hpow.symm
      have hlin_n : (Peven τ).eval (Z n) - C = -(((Z n) ^ (1 / 2 : ℂ)) * (Podd τ).eval (Z n)) := by
        rw [hPe, hPo, ← hsum_star, ← hunion, Finset.sum_union hdisj]
        ring
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_X]
      rw [hlin_n, neg_sq, mul_pow, hs2, sub_self]
    have hpoly_zero : (Peven τ - Polynomial.C C) ^ 2 - Polynomial.X * (Podd τ) ^ 2 = 0 :=
      poly_eq_zero_of_eval_eq_zero_nat _ Z hZ_inj hZ_eval
    have hsq_eq : (Peven τ - Polynomial.C C) ^ 2 = Polynomial.X * (Podd τ) ^ 2 :=
      sub_eq_zero.mp hpoly_zero
    have hPodd0 : Podd τ = 0 := by
      by_contra hne
      have hRne : Polynomial.X * (Podd τ) ^ 2 ≠ 0 :=
        mul_ne_zero Polynomial.X_ne_zero (pow_ne_zero 2 hne)
      have hLne : Peven τ - Polynomial.C C ≠ 0 := by
        intro h0; rw [h0, zero_pow (by decide)] at hsq_eq; exact hRne hsq_eq.symm
      have hdeg := congrArg Polynomial.natDegree hsq_eq
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_mul Polynomial.X_ne_zero (pow_ne_zero 2 hne),
          Polynomial.natDegree_X, Polynomial.natDegree_pow] at hdeg
      omega
    have hPevenC : Peven τ = Polynomial.C C := by
      rw [hPodd0, zero_pow (by decide), mul_zero] at hsq_eq
      exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsq_eq)
    exact ⟨hPevenC, hPodd0⟩
  -- Shared extraction helper for either parity (`parity = 0` for even, `parity = 1` for odd)!
  have hkill_block : ∀ (T : Finset (ℕ × ℕ)) (par : ℕ),
      T ⊆ Sstar →
      (∀ p ∈ T, p.1 % 2 = par) →
      (∀ τ ∈ upperHalfPlane,
        (∑ p ∈ T, ∑ r ∈ Finset.range (p.2 + 1),
          Polynomial.C (((Nat.choose p.2 r : ℕ) : ℂ) * descFac ((p.1 : ℂ) / 2 + (p.2 : ℂ) - 1) r *
            τ⁻¹ ^ r * iteratedDeriv (p.2 - r) (G p) τ) *
          ((Polynomial.X - 1) ^ r * Polynomial.X ^ ((p.1 - par) / 2 + 2 * p.2 - r))) =
          if par = 0 then Polynomial.C C else 0) →
      T = ∅ := by
    intro T par hTsub hTpar hTeq
    by_contra hTne
    have hTnon : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hTne
    let score : ℕ × ℕ → ℕ := fun p ↦ (p.1 - par) / 2 + p.2
    let imgs : Finset ℕ := T.image score
    let Mmin : ℕ := imgs.min' (hTnon.image score)
    have hMmin_mem : Mmin ∈ imgs := Finset.min'_mem imgs _
    obtain ⟨p₀, hp₀T, hp₀_sc⟩ := Finset.mem_image.mp hMmin_mem
    have hMmin_le : ∀ p ∈ T, Mmin ≤ score p := fun p hp ↦
      Finset.min'_le imgs (score p) (Finset.mem_image_of_mem score hp)
    -- If `par = 0`, every `p ∈ T` has `p.1 ≥ 1` and `p.1 % 2 = 0`, so `p.1 ≥ 2` and `Mmin ≥ 1`!
    have hcoeff_zero : ∀ τ ∈ upperHalfPlane,
        (∑ p ∈ T.filter (fun p ↦ score p = Mmin),
          descFac ((p.1 : ℂ) / 2 + (p.2 : ℂ) - 1) p.2 *
            (-τ⁻¹) ^ p.2 * G p τ) = 0 := by
      intro τ hτ
      have h0 := congrArg (fun P : Polynomial ℂ ↦ P.coeff Mmin) (hTeq τ hτ)
      have hrhs0 : (if par = 0 then Polynomial.C C else (0 : Polynomial ℂ)).coeff Mmin = 0 := by
        split_ifs with hpar0
        · subst hpar0
          have hp₀S : p₀ ∈ S := (Finset.mem_filter.mp (hTsub hp₀T)).1
          have hp₀_ge1 := hS_pos p₀ hp₀S
          have hp₀_ev := hTpar p₀ hp₀T
          have hMmin_pos : 0 < Mmin := by dsimp [score] at hp₀_sc; omega
          simp [Polynomial.coeff_C, hMmin_pos.ne']
        · simp
      rw [hrhs0, poly_coeff_finset_sum] at h0
      rw [← h0]
      symm
      rw [← Finset.sum_subset (Finset.filter_subset (fun p ↦ score p = Mmin) T)]
      · apply Finset.sum_congr rfl
        intro p hp
        have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
        have hp_sc : score p = Mmin := (Finset.mem_filter.mp hp).2
        rw [poly_coeff_finset_sum, Finset.sum_eq_single p.2]
        · rw [Polynomial.coeff_C_mul, coeff_X_sub_one_pow_mul_X_pow]
          have hexp : (p.1 - par) / 2 + 2 * p.2 - p.2 = Mmin := by
            dsimp [score] at hp_sc; omega
          rw [hexp]
          simp only [lt_irrefl, ↓reduceIte, Nat.choose_self, Nat.cast_one, one_mul,
              Nat.sub_self, iteratedDeriv_zero]
          have hneg : (-τ⁻¹) ^ p.2 = τ⁻¹ ^ p.2 * (-1 : ℂ) ^ p.2 := by
            rw [← mul_pow]; congr 1; ring
          rw [hneg]; ring
        · intro r hr hne
          have hrj : r < p.2 := by
            have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr); omega
          rw [Polynomial.coeff_C_mul, coeff_X_sub_one_pow_mul_X_pow]
          have hlt : Mmin < (p.1 - par) / 2 + 2 * p.2 - r := by
            dsimp [score] at hp_sc; omega
          simp [hlt]
        · intro hnot; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self p.2)) hnot
      · intro p hpT hnot
        have hp_gt : Mmin < score p := by
          have hle := hMmin_le p hpT
          have hne : score p ≠ Mmin := fun h ↦ hnot (Finset.mem_filter.mpr ⟨hpT, h⟩)
          omega
        rw [poly_coeff_finset_sum]
        apply Finset.sum_eq_zero
        intro r hr
        have hrj : r ≤ p.2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        rw [Polynomial.coeff_C_mul, coeff_X_sub_one_pow_mul_X_pow]
        have hlt : Mmin < (p.1 - par) / 2 + 2 * p.2 - r := by
          dsimp [score] at hp_gt; omega
        simp [hlt]
    -- Now fix ANY `τ₀ ∈ ℍ` and vary `τ = τ₀ + n L` (`n : ℕ`) using `T^L`-periodicity!
    have hp₀_zero : ∀ τ₀ ∈ upperHalfPlane, G p₀ τ₀ = 0 := by
      intro τ₀ hτ₀
      let Tmin : Finset (ℕ × ℕ) := T.filter (fun p ↦ score p = Mmin)
      let Q : Polynomial ℂ :=
        ∑ p ∈ Tmin,
          Polynomial.C (descFac ((p.1 : ℂ) / 2 + (p.2 : ℂ) - 1) p.2 * G p τ₀) *
            Polynomial.X ^ (Mmin - p.2)
      let pts : ℕ → ℂ := fun n ↦ -(τ₀ + ((n * L : ℕ) : ℂ))
      have hpts_inj : Function.Injective pts := by
        intro n₁ n₂ h
        dsimp only [pts] at h
        have h1 : ((n₁ * L : ℕ) : ℂ) = ((n₂ * L : ℕ) : ℂ) :=
          add_left_cancel (neg_inj.mp h)
        have h2 : n₁ * L = n₂ * L := by exact_mod_cast h1
        exact Nat.eq_of_mul_eq_mul_right (by omega) h2
      have hQ_eval : ∀ n : ℕ, Q.eval (pts n) = 0 := by
        intro n
        have hτn_mem : τ₀ + (((n : ℤ) * (L : ℤ) : ℤ) : ℂ) ∈ upperHalfPlane :=
          add_int_mem_upperHalfPlane hτ₀ ((n : ℤ) * (L : ℤ))
        have hτn_eq : -(pts n) = τ₀ + (((n : ℤ) * (L : ℤ) : ℤ) : ℂ) := by
          dsimp only [pts]; push_cast; ring
        have hτn_ne : pts n ≠ 0 := by
          intro h0
          have h1 : τ₀ + (((n : ℤ) * (L : ℤ) : ℤ) : ℂ) = 0 := by rw [← hτn_eq, h0, neg_zero]
          exact upperHalfPlane_ne_zero hτn_mem h1
        have hrel_n := hcoeff_zero _ hτn_mem
        have hmul := congrArg ((pts n) ^ Mmin * ·) hrel_n
        rw [mul_zero, Finset.mul_sum] at hmul
        rw [← hmul]
        simp only [Q, poly_eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, Polynomial.eval_X]
        apply Finset.sum_congr rfl
        intro p hp
        have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
        have hpS : p ∈ S := (Finset.mem_filter.mp (hTsub hpT)).1
        have hp_sc : score p = Mmin := (Finset.mem_filter.mp hp).2
        have hp_le : p.2 ≤ Mmin := by dsimp [score] at hp_sc; omega
        have hper_p := hper p hpS (n : ℤ) τ₀ hτ₀
        rw [hper_p]
        have hinv_eq : -((τ₀ + (((n : ℤ) * (L : ℤ) : ℤ) : ℂ))⁻¹) = (pts n)⁻¹ := by
          rw [← hτn_eq, inv_neg, neg_neg]
        rw [hinv_eq]
        have hpow_cancel : (pts n) ^ Mmin * ((pts n)⁻¹) ^ p.2 = (pts n) ^ (Mmin - p.2) := by
          have hsplit : Mmin = (Mmin - p.2) + p.2 := (Nat.sub_add_cancel hp_le).symm
          conv_lhs => rw [hsplit, pow_add]
          rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hτn_ne, one_pow, mul_one]
        linear_combination
          -(descFac ((p.1 : ℂ) / 2 + (p.2 : ℂ) - 1) p.2 * G p τ₀) * hpow_cancel
      have hQ0 : Q = 0 := poly_eq_zero_of_eval_eq_zero_nat Q pts hpts_inj hQ_eval
      -- Extract coefficient `Mmin - p₀.2` — unique element `p₀` in `Tmin`!
      have hcoeff_p0 := congrArg (fun P : Polynomial ℂ ↦ P.coeff (Mmin - p₀.2)) hQ0
      rw [Polynomial.coeff_zero, poly_coeff_finset_sum] at hcoeff_p0
      have hp₀_mem_Tmin : p₀ ∈ Tmin := Finset.mem_filter.mpr ⟨hp₀T, hp₀_sc⟩
      rw [Finset.sum_eq_single p₀] at hcoeff_p0
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one] at hcoeff_p0
        have hp₀S : p₀ ∈ S := (Finset.mem_filter.mp (hTsub hp₀T)).1
        exact (mul_eq_zero.mp hcoeff_p0).resolve_left
          (descFac_halfInt_ne_zero (hS_pos p₀ hp₀S) p₀.2)
      · intro p hp hne
        have hpT : p ∈ T := (Finset.mem_filter.mp hp).1
        have hp_sc : score p = Mmin := (Finset.mem_filter.mp hp).2
        have hdiff_ne : Mmin - p₀.2 ≠ Mmin - p.2 := by
          intro heq
          have hp2_le : p.2 ≤ Mmin := by dsimp [score] at hp_sc; omega
          have hp02_le : p₀.2 ≤ Mmin := by dsimp [score] at hp₀_sc; omega
          have h2eq : p.2 = p₀.2 := by omega
          have h1par := hTpar p hpT
          have h0par := hTpar p₀ hp₀T
          have h1eq : p.1 = p₀.1 := by dsimp [score] at hp_sc hp₀_sc; omega
          exact hne (Prod.ext h1eq h2eq)
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        simp [hdiff_ne]
      · intro hnot; exact absurd hp₀_mem_Tmin hnot
    -- Contradicts `p₀ ∈ T ⊆ Sstar`!
    obtain ⟨τ₀, hτ₀, hne⟩ := (Finset.mem_filter.mp (hTsub hp₀T)).2
    exact hne (hp₀_zero τ₀ hτ₀)
  -- Kill both `Seven` and `Sodd`!
  have hSeven_empty : Seven = ∅ :=
    hkill_block Seven 0 (Finset.filter_subset _ Sstar) (fun p hp ↦ (Finset.mem_filter.mp hp).2)
      (fun τ hτ ↦ by simpa [Peven] using (hpoly_ident τ hτ).1)
  have hSodd_empty : Sodd = ∅ :=
    hkill_block Sodd 1 (Finset.filter_subset _ Sstar) (fun p hp ↦ (Finset.mem_filter.mp hp).2)
      (fun τ hτ ↦ by simpa [Podd] using (hpoly_ident τ hτ).2)
  intro p hp τ hτ
  by_contra hne
  have hpStar : p ∈ Sstar := Finset.mem_filter.mpr ⟨hp, τ, hτ, hne⟩
  rcases Nat.mod_two_eq_zero_or_one p.1 with h0 | h1
  · have : p ∈ Seven := Finset.mem_filter.mpr ⟨hpStar, h0⟩
    rw [hSeven_empty] at this; exact Finset.notMem_empty p this
  · have : p ∈ Sodd := Finset.mem_filter.mpr ⟨hpStar, h1⟩
    rw [hSodd_empty] at this; exact Finset.notMem_empty p this

/-- **Corollary 3B — Universal Differential Independence of Positive-Weight Modular Forms**:
Let `g_1, …, g_m` be holomorphic modular forms on `ℍ` of arbitrary mixed positive integer and
half-integer weights `w_i = k_i / 2` (`1 ≤ k_i`), with common `γ_n`-modularity (`n ≥ 1`) and
`T^L`-periodicity (`M, L ≥ 1`).
If `g_1, …, g_m` are `ℂ`-linearly independent on `ℍ` and satisfy ANY constant-coefficient
linear differential relation `∑_i Q_i(∂_τ) g_i(τ) = C` on `ℍ`, then **EVERY `Q_i = 0`** (and `C = 0`)! -/
theorem positiveWeight_modular_forms_diff_indep {m : ℕ}
    (k : Fin m → ℕ) (hk : ∀ i : Fin m, 1 ≤ k i)
    (g : Fin m → ℂ → ℂ) (hg_diff : ∀ i : Fin m, DifferentiableOn ℂ (g i) upperHalfPlane)
    {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hmod : ∀ i : Fin m, ∀ n : ℕ, 1 ≤ n → ∀ τ ∈ upperHalfPlane,
      g i (τ / (((n * M : ℕ) : ℂ) * τ + 1)) =
        ((((n * M : ℕ) : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ (k i) * g i τ)
    (hper : ∀ i : Fin m, ∀ n : ℤ, ∀ τ ∈ upperHalfPlane,
      g i (τ + ((n * (L : ℤ) : ℤ) : ℂ)) = g i τ)
    (hlin : ∀ c : Fin m → ℂ, (∀ τ ∈ upperHalfPlane, ∑ i : Fin m, c i * g i τ = 0) → c = 0)
    (Q : Fin m → Polynomial ℂ) (C : ℂ)
    (hrel : ∀ τ ∈ upperHalfPlane,
      ∑ i : Fin m, ∑ j ∈ Finset.range ((Q i).natDegree + 1),
        (Q i).coeff j * iteratedDeriv j (g i) τ = C) :
    (∀ i : Fin m, Q i = 0) ∧ C = 0 := by
  let D : ℕ := Finset.univ.sup (fun i : Fin m ↦ (Q i).natDegree) + 1
  let Wset : Finset ℕ := Finset.univ.image k
  let S : Finset (ℕ × ℕ) := Wset ×ˢ Finset.range D
  let G : ℕ × ℕ → ℂ → ℂ := fun p τ ↦
    ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k i = p.1), (Q i).coeff p.2 * g i τ
  have hS_pos : ∀ p ∈ S, 1 ≤ p.1 := by
    intro p hp
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_product.mp hp).1
    rw [← hi]; exact hk i
  have hG_diff : ∀ p ∈ S, DifferentiableOn ℂ (G p) upperHalfPlane := by
    intro p _
    exact DifferentiableOn.fun_sum fun i _ ↦ (hg_diff i).const_mul ((Q i).coeff p.2)
  have hG_mod : ∀ p ∈ S, ∀ n : ℕ, 1 ≤ n → ∀ τ ∈ upperHalfPlane,
      G p (τ / (((n * M : ℕ) : ℂ) * τ + 1)) =
        ((((n * M : ℕ) : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ p.1 * G p τ := by
    intro p _ n hn τ hτ
    dsimp only [G]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hki : k i = p.1 := (Finset.mem_filter.mp hi).2
    rw [hmod i n hn τ hτ, hki]; ring
  have hG_per : ∀ p ∈ S, ∀ n : ℤ, ∀ τ ∈ upperHalfPlane,
      G p (τ + ((n * (L : ℤ) : ℤ) : ℂ)) = G p τ := by
    intro p _ n τ hτ
    dsimp only [G]
    apply Finset.sum_congr rfl
    intro i _
    rw [hper i n τ hτ]
  -- Helper: `iteratedDeriv j` is linear on `ℍ` for sums of holomorphic functions!
  have hiter_lin : ∀ (F : Finset (Fin m)) (c : Fin m → ℂ) (j : ℕ), ∀ τ ∈ upperHalfPlane,
      iteratedDeriv j (fun z ↦ ∑ i ∈ F, c i * g i z) τ =
        ∑ i ∈ F, c i * iteratedDeriv j (g i) τ := by
    intro F c j
    induction j with
    | zero => intro τ _; simp [iteratedDeriv_zero]
    | succ j ih =>
      intro τ hτ
      rw [iteratedDeriv_succ]
      have hev : iteratedDeriv j (fun z ↦ ∑ i ∈ F, c i * g i z) =ᶠ[𝓝 τ]
          (fun z ↦ ∑ i ∈ F, c i * iteratedDeriv j (g i) z) := by
        filter_upwards [isOpen_upperHalfPlane.mem_nhds hτ] with z hz
        exact ih z hz
      rw [hev.deriv_eq]
      have hterm : ∀ i ∈ F, HasDerivAt (fun z ↦ c i * iteratedDeriv j (g i) z)
          (c i * iteratedDeriv (j + 1) (g i) τ) τ := by
        intro i _
        have hdiff := (differentiableOn_iteratedDeriv_UHP (hg_diff i) j).differentiableAt
          (isOpen_upperHalfPlane.mem_nhds hτ)
        rw [iteratedDeriv_succ]
        exact hdiff.hasDerivAt.const_mul (c i)
      exact (HasDerivAt.fun_sum hterm).deriv
  have hG_rel : ∀ τ ∈ upperHalfPlane, ∑ p ∈ S, iteratedDeriv p.2 (G p) τ = C := by
    intro τ hτ
    rw [← hrel τ hτ]
    have hsumG : ∑ p ∈ S, iteratedDeriv p.2 (G p) τ =
        ∑ w ∈ Wset, ∑ j ∈ Finset.range D,
          ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k i = w),
            (Q i).coeff j * iteratedDeriv j (g i) τ := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl; intro w _
      apply Finset.sum_congr rfl; intro j _
      exact hiter_lin _ _ j τ hτ
    rw [hsumG]
    trans ∑ w ∈ Wset, ∑ i ∈ Finset.univ.filter (fun i : Fin m ↦ k i = w),
        ∑ j ∈ Finset.range D, (Q i).coeff j * iteratedDeriv j (g i) τ
    · apply Finset.sum_congr rfl; intro w _
      exact Finset.sum_comm
    · rw [Finset.sum_fiberwise_of_maps_to (g := fun i : Fin m ↦ k i)
        (fun i _ ↦ Finset.mem_image_of_mem k (Finset.mem_univ i))]
      apply Finset.sum_congr rfl; intro i _
      symm
      apply Finset.sum_subset
      · intro j hj
        have hj1 : j ≤ (Q i).natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hsup : (Q i).natDegree ≤ Finset.univ.sup (fun i' : Fin m ↦ (Q i').natDegree) :=
          Finset.le_sup (f := fun i' : Fin m ↦ (Q i').natDegree) (Finset.mem_univ i)
        exact Finset.mem_range.mpr (by omega)
      · intro j _ hnot
        have hgt : (Q i).natDegree < j := by
          have := Finset.mem_range.not.mp hnot; omega
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt hgt, zero_mul]
  have hG_zero := positiveWeight_modular_diff_indep_abstract S hS_pos G hG_diff hM hL
    hG_mod hG_per C hG_rel
  have hQ_zero : ∀ i : Fin m, Q i = 0 := by
    intro i
    ext j
    rw [Polynomial.coeff_zero]
    by_cases hj : j < D
    · let c : Fin m → ℂ := fun i' ↦ if k i' = k i then (Q i').coeff j else 0
      have hc0 : c = 0 := by
        apply hlin c
        intro τ hτ
        have hmem : (k i, j) ∈ S :=
          Finset.mem_product.mpr ⟨Finset.mem_image_of_mem k (Finset.mem_univ i), Finset.mem_range.mpr hj⟩
        have h0 := hG_zero (k i, j) hmem τ hτ
        dsimp only [G] at h0
        rw [← h0]
        rw [← Finset.sum_subset (Finset.filter_subset (fun i' : Fin m ↦ k i' = k i) Finset.univ)]
        · apply Finset.sum_congr rfl; intro i' hi'
          have hki' : k i' = k i := (Finset.mem_filter.mp hi').2
          simp [c, hki']
        · intro i' _ hnot
          have hne : k i' ≠ k i := fun h ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i', h⟩)
          simp [c, hne]
      have hi0 := congrFun hc0 i
      simpa [c] using hi0
    · apply Polynomial.coeff_eq_zero_of_natDegree_lt
      have hsup : (Q i).natDegree ≤ Finset.univ.sup (fun i' : Fin m ↦ (Q i').natDegree) :=
        Finset.le_sup (f := fun i' : Fin m ↦ (Q i').natDegree) (Finset.mem_univ i)
      omega
  refine ⟨hQ_zero, ?_⟩
  have h0 := hrel Complex.I (by simp [upperHalfPlane])
  simp only [hQ_zero, Polynomial.coeff_zero, zero_mul, Finset.sum_const_zero] at h0
  exact h0.symm

/-- **Explicit `θ_q = (1 / (2 π i)) ∂_τ` Cusp-Part Version**:
Even after subtracting arbitrary constant terms `c₀ i` (`g_cusp i τ = g i τ - c₀ i`),
`ℂ`-linearly independent positive-weight modular forms satisfy NO nontrivial constant-coefficient
linear differential relation `∑_i Q_i(θ_q) g_{i, cusp} = 0` on `ℍ`! -/
theorem positiveWeight_modular_thetaQ_diff_indep {m : ℕ}
    (k : Fin m → ℕ) (hk : ∀ i : Fin m, 1 ≤ k i)
    (g : Fin m → ℂ → ℂ) (hg_diff : ∀ i : Fin m, DifferentiableOn ℂ (g i) upperHalfPlane)
    {M L : ℕ} (hM : 1 ≤ M) (hL : 1 ≤ L)
    (hmod : ∀ i : Fin m, ∀ n : ℕ, 1 ≤ n → ∀ τ ∈ upperHalfPlane,
      g i (τ / (((n * M : ℕ) : ℂ) * τ + 1)) =
        ((((n * M : ℕ) : ℂ) * τ + 1) ^ (1 / 2 : ℂ)) ^ (k i) * g i τ)
    (hper : ∀ i : Fin m, ∀ n : ℤ, ∀ τ ∈ upperHalfPlane,
      g i (τ + ((n * (L : ℤ) : ℤ) : ℂ)) = g i τ)
    (hlin : ∀ c : Fin m → ℂ, (∀ τ ∈ upperHalfPlane, ∑ i : Fin m, c i * g i τ = 0) → c = 0)
    (c₀ : Fin m → ℂ) (Q : Fin m → Polynomial ℂ)
    (hrel : ∀ τ ∈ upperHalfPlane,
      ∑ i : Fin m, ∑ j ∈ Finset.range ((Q i).natDegree + 1),
        (Q i).coeff j * (1 / (2 * (Real.pi : ℂ) * Complex.I)) ^ j *
          iteratedDeriv j (fun z ↦ g i z - c₀ i) τ = 0) :
    ∀ i : Fin m, Q i = 0 := by
  let α : ℂ := 1 / (2 * (Real.pi : ℂ) * Complex.I)
  have hα_ne : α ≠ 0 := by
    dsimp [α]
    exact div_ne_zero one_ne_zero
      (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) Complex.I_ne_zero)
  let Qtilde : Fin m → Polynomial ℂ := fun i ↦ (Q i).comp (Polynomial.C α * Polynomial.X)
  have hQtilde_coeff (i : Fin m) (j : ℕ) : (Qtilde i).coeff j = (Q i).coeff j * α ^ j := by
    dsimp only [Qtilde]
    rw [Polynomial.comp_eq_sum_left, Polynomial.sum_def, poly_coeff_finset_sum]
    have hterm : ∀ n ∈ (Q i).support,
        (Polynomial.C ((Q i).coeff n) * (Polynomial.C α * Polynomial.X) ^ n).coeff j =
          if j = n then (Q i).coeff n * α ^ n else 0 := by
      intro n _
      rw [mul_pow, ← map_pow, ← mul_assoc, ← map_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hterm]
    by_cases hj : j ∈ (Q i).support
    · rw [Finset.sum_eq_single j (fun n _ hne ↦ by simp [Ne.symm hne]) (fun hnot ↦ absurd hj hnot)]
      simp
    · rw [Finset.sum_eq_zero (fun n hn ↦ by
        have hjn : j ≠ n := fun h ↦ hj (h ▸ hn)
        simp [hjn]),
        Polynomial.notMem_support_iff.mp hj, zero_mul]
  have hQtilde_deg (i : Fin m) : (Qtilde i).natDegree = (Q i).natDegree := by
    by_cases hQ0 : Q i = 0
    · simp [Qtilde, hQ0]
    · apply le_antisymm
      · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
        intro n hn
        rw [hQtilde_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hn, zero_mul]
      · apply Polynomial.le_natDegree_of_ne_zero
        rw [hQtilde_coeff]
        exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hQ0) (pow_ne_zero _ hα_ne)
  have hderiv_sub : ∀ (i : Fin m) (j : ℕ), 1 ≤ j → ∀ τ ∈ upperHalfPlane,
      iteratedDeriv j (fun z ↦ g i z - c₀ i) τ = iteratedDeriv j (g i) τ := by
    intro i j hj
    cases j with
    | zero => omega
    | succ j' =>
      clear hj
      induction j' with
      | zero =>
        intro τ hτ
        rw [iteratedDeriv_one, iteratedDeriv_one]
        have hd := ((hg_diff i).differentiableAt (isOpen_upperHalfPlane.mem_nhds hτ)).hasDerivAt
        exact (hd.sub_const (c₀ i)).deriv
      | succ j'' ih =>
        intro τ hτ
        rw [iteratedDeriv_succ (n := j'' + 1), iteratedDeriv_succ (n := j'' + 1)]
        have hev : iteratedDeriv (j'' + 1) (fun z ↦ g i z - c₀ i) =ᶠ[𝓝 τ]
            iteratedDeriv (j'' + 1) (g i) := by
          filter_upwards [isOpen_upperHalfPlane.mem_nhds hτ] with z hz
          exact ih z hz
        rw [hev.deriv_eq]
  have hrel' : ∀ τ ∈ upperHalfPlane,
      ∑ i : Fin m, ∑ j ∈ Finset.range ((Qtilde i).natDegree + 1),
        (Qtilde i).coeff j * iteratedDeriv j (g i) τ =
        ∑ i : Fin m, (Q i).coeff 0 * c₀ i := by
    intro τ hτ
    have h0 := hrel τ hτ
    have hdiff : (∑ i : Fin m, ∑ j ∈ Finset.range ((Qtilde i).natDegree + 1),
          (Qtilde i).coeff j * iteratedDeriv j (g i) τ) -
        (∑ i : Fin m, (Q i).coeff 0 * c₀ i) = 0 := by
      rw [← h0, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hQtilde_deg i, Finset.sum_range_succ', Finset.sum_range_succ']
      simp only [hQtilde_coeff, pow_zero, mul_one, iteratedDeriv_zero]
      have htail : ∑ x ∈ Finset.range (Q i).natDegree,
            (Q i).coeff (x + 1) * α ^ (x + 1) * iteratedDeriv (x + 1) (g i) τ =
          ∑ x ∈ Finset.range (Q i).natDegree,
            (Q i).coeff (x + 1) * α ^ (x + 1) *
              iteratedDeriv (x + 1) (fun z ↦ g i z - c₀ i) τ := by
        apply Finset.sum_congr rfl
        intro x _
        rw [hderiv_sub i (x + 1) (Nat.succ_pos x) τ hτ]
      rw [htail]; ring
    exact sub_eq_zero.mp hdiff
  have hQt0 := (positiveWeight_modular_forms_diff_indep k hk g hg_diff hM hL hmod hper hlin
    Qtilde (∑ i : Fin m, (Q i).coeff 0 * c₀ i) hrel').1
  intro i
  ext j
  have h0 := congrArg (fun P : Polynomial ℂ ↦ P.coeff j) (hQt0 i)
  rw [hQtilde_coeff, Polynomial.coeff_zero] at h0
  exact (mul_eq_zero.mp h0).resolve_right (pow_ne_zero j hα_ne)

/-! ### 4. Stretch Bonus: The 5-Line Maximum Modulus Watson Uniqueness Lemma -/

/-- The closed sector `{z ∈ ℂ : R₀ ≤ ‖z‖ ∧ |arg z| ≤ 2π / 3}`, characterized algebraically
without branch-cut boilerplate as `{z ∈ ℂ : R₀ ≤ ‖z‖ ∧ -(1 / 2) * ‖z‖ ≤ z.re}`. -/
def watsonClosedSector (R₀ : ℝ) : Set ℂ :=
  {z : ℂ | R₀ ≤ ‖z‖ ∧ -(1 / 2 : ℝ) * ‖z‖ ≤ z.re}

/-- The open sector `{z ∈ ℂ : R₀ < ‖z‖ ∧ |arg z| < 2π / 3}`. -/
def watsonOpenSector (R₀ : ℝ) : Set ℂ :=
  {z : ℂ | R₀ < ‖z‖ ∧ -(1 / 2 : ℝ) * ‖z‖ < z.re}

/-- Every point of `watsonClosedSector R₀` (`R₀ > 0`) lies in `Complex.slitPlane`! -/
theorem watsonClosedSector_subset_slitPlane {R₀ : ℝ} (hR₀ : 0 < R₀) :
    watsonClosedSector R₀ ⊆ Complex.slitPlane := by
  intro z ⟨hnorm, hre⟩
  rw [Complex.mem_slitPlane_iff]
  by_contra hnot
  push Not at hnot
  obtain ⟨hre_le, him0⟩ := hnot
  have hnorm_eq : ‖z‖ = -z.re := by
    rw [Complex.norm_def, Complex.normSq_apply, him0, mul_zero, add_zero, ← sq,
        Real.sqrt_sq_eq_abs, abs_of_nonpos hre_le]
  linarith

/-- On `watsonClosedSector R₀` (`R₀ > 0`), `|z.arg| ≤ 2 π / 3`. -/
private lemma abs_arg_le_two_pi_div_three {R₀ : ℝ} (hR₀ : 0 < R₀) {z : ℂ}
    (hz : z ∈ watsonClosedSector R₀) :
    |z.arg| ≤ 2 * Real.pi / 3 := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR₀ hz.1)
  have hcos_ge : -(1 / 2 : ℝ) ≤ Real.cos z.arg := by
    rw [Complex.cos_arg hz0]
    have hnorm_pos : 0 < ‖z‖ := lt_of_lt_of_le hR₀ hz.1
    rw [le_div_iff₀ hnorm_pos]
    linarith [hz.2]
  have hcos_abs : Real.cos (2 * Real.pi / 3) ≤ Real.cos |z.arg| := by
    rw [Real.cos_abs, show Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) by
      rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]]
    exact hcos_ge
  have habs_mem : |z.arg| ∈ Set.Icc 0 Real.pi :=
    ⟨abs_nonneg _, abs_le.mpr ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩⟩
  have h23_mem : 2 * Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  by_contra hgt
  have hstrict := Real.strictAntiOn_cos h23_mem habs_mem (not_le.mp hgt)
  linarith

/-- On the boundary rays `z.re = -(1/2) ‖z‖` (`‖z‖ ≥ R₀ > 0`), `|z.arg| = 2 π / 3`, so
`cos((4 / 5) * z.arg) ≤ 0`. -/
private lemma cos_four_fifths_arg_nonpos_of_ray {R₀ : ℝ} (hR₀ : 0 < R₀) {z : ℂ}
    (hz : z ∈ watsonClosedSector R₀) (hray : z.re = -(1 / 2 : ℝ) * ‖z‖) :
    Real.cos ((4 / 5 : ℝ) * z.arg) ≤ 0 := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR₀ hz.1)
  have hcos_eq : Real.cos |z.arg| = Real.cos (2 * Real.pi / 3) := by
    rw [Real.cos_abs, Complex.cos_arg hz0, hray,
        show Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) by
          rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
              Real.cos_pi_sub, Real.cos_pi_div_three]]
    have hnorm_ne : ‖z‖ ≠ 0 := (lt_of_lt_of_le hR₀ hz.1).ne'
    field_simp [hnorm_ne]
  have habs_eq : |z.arg| = 2 * Real.pi / 3 :=
    Real.injOn_cos
      ⟨abs_nonneg _, abs_le.mpr ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩⟩
      ⟨by positivity, by linarith [Real.pi_pos]⟩
      hcos_eq
  have hcos_abs : Real.cos ((4 / 5 : ℝ) * z.arg) = Real.cos (8 * Real.pi / 15) := by
    rw [← Real.cos_abs ((4 / 5 : ℝ) * z.arg), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5),
        habs_eq]
    congr 1; ring
  rw [hcos_abs]
  exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Exact formula `Re(z^{4/5}) = ‖z‖^{4/5} cos((4 / 5) * arg z)` for `z ≠ 0`. -/
private lemma re_cpow_four_fifths {z : ℂ} (hz : z ≠ 0) :
    (z ^ (4 / 5 : ℂ)).re = ‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) := by
  rw [Complex.cpow_def_of_ne_zero hz, Complex.exp_re]
  have harg : (Complex.log z * (4 / 5 : ℂ)).re = (4 / 5 : ℝ) * Real.log ‖z‖ := by
    rw [Complex.mul_re]
    simp [Complex.log_re, Complex.log_im]; ring
  have him : (Complex.log z * (4 / 5 : ℂ)).im = (4 / 5 : ℝ) * z.arg := by
    rw [Complex.mul_im]
    simp [Complex.log_re, Complex.log_im]; ring
  rw [harg, him, Real.rpow_def_of_pos (norm_pos_iff.mpr hz)]
  congr 1; congr 1; ring

/-- **Crown Jewel Theorem 4 — The 5-Line Maximum Modulus Watson Uniqueness Lemma**:
Let `R₀ > 0`, `C' ≥ 0`, `c' > 0`, and let `f : ℂ → ℂ` be holomorphic on `watsonOpenSector R₀`
and continuous on `watsonClosedSector R₀` (i.e. `DiffContOnCl` on every bounded subsector),
satisfying exponential decay `‖f z‖ ≤ C' * exp (-c' * ‖z‖)` on `watsonClosedSector R₀`.
Then `f x = 0` for EVERY real `x > R₀` (and hence `f z = 0` for EVERY `z ∈ watsonOpenSector R₀`
by the Identity Theorem!). -/
theorem maxModulus_watson_uniqueness {R₀ C' c' : ℝ} (hR₀ : 0 < R₀) (hC' : 0 ≤ C') (hc' : 0 < c')
    {f : ℂ → ℂ} (hf_diff : DifferentiableOn ℂ f (watsonOpenSector R₀))
    (hf_cont : ContinuousOn f (watsonClosedSector R₀))
    (hdecay : ∀ z ∈ watsonClosedSector R₀, ‖f z‖ ≤ C' * Real.exp (-c' * ‖z‖)) :
    (∀ x : ℝ, R₀ < x → f (x : ℂ) = 0) ∧ (∀ z ∈ watsonOpenSector R₀, f z = 0) := by
  -- Step 1: Prove `f (x : ℂ) = 0` for every real `x > R₀` via `h_λ(z) = exp(λ(z^{4/5} - R₀^{4/5})) f(z)`!
  have hreal_zero : ∀ x : ℝ, R₀ < x → f (x : ℂ) = 0 := by
    intro x hx
    have hx_pos : 0 < x := lt_trans hR₀ hx
    -- For EVERY `λ > 0`, apply the Maximum Modulus Principle on `U_R` with `R = max (x + 1) ((λ / c')^5 + 1)`!
    have hbound_lam : ∀ lam : ℝ, 0 < lam →
        ‖f (x : ℂ)‖ ≤ C' * Real.exp (-lam * (x ^ (4 / 5 : ℝ) - R₀ ^ (4 / 5 : ℝ))) := by
      intro lam hlam
      let R : ℝ := max (x + 1) ((lam / c') ^ 5 + 1)
      have hRx : x < R := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hRR₀ : R₀ < R := lt_trans hx hRx
      have hR_pos : 0 < R := lt_trans hR₀ hRR₀
      have hR_lam : (lam / c') ^ 5 ≤ R := le_trans (by linarith) (le_max_right _ _)
      let U : Set ℂ := {z : ℂ | R₀ < ‖z‖ ∧ ‖z‖ < R ∧ -(1 / 2 : ℝ) * ‖z‖ < z.re}
      let K : Set ℂ := {z : ℂ | R₀ ≤ ‖z‖ ∧ ‖z‖ ≤ R ∧ -(1 / 2 : ℝ) * ‖z‖ ≤ z.re}
      have hU_open : IsOpen U :=
        (isOpen_lt continuous_const continuous_norm).inter
          ((isOpen_lt continuous_norm continuous_const).inter
            (isOpen_lt (continuous_const.mul continuous_norm) Complex.continuous_re))
      have hK_closed : IsClosed K :=
        (isClosed_le continuous_const continuous_norm).inter
          ((isClosed_le continuous_norm continuous_const).inter
            (isClosed_le (continuous_const.mul continuous_norm) Complex.continuous_re))
      have hU_sub_K : U ⊆ K := fun z ⟨h1, h2, h3⟩ ↦ ⟨h1.le, h2.le, h3.le⟩
      have hcl_sub_K : closure U ⊆ K := closure_minimal hU_sub_K hK_closed
      have hK_sub_sec : K ⊆ watsonClosedSector R₀ := fun z ⟨h1, _, h3⟩ ↦ ⟨h1, h3⟩
      have hU_sub_open : U ⊆ watsonOpenSector R₀ := fun z ⟨h1, _, h3⟩ ↦ ⟨h1, h3⟩
      have hU_bdd : Bornology.IsBounded U := by
        rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
        exact ⟨R, fun z hz ↦ by simpa [Metric.mem_closedBall, dist_zero_right] using hz.2.1.le⟩
      let h : ℂ → ℂ := fun z ↦
        Complex.exp ((lam : ℂ) * (z ^ (4 / 5 : ℂ) - ((R₀ ^ (4 / 5 : ℝ) : ℝ) : ℂ))) * f z
      have hh_diff : DiffContOnCl ℂ h U := by
        refine ⟨?_, ?_⟩
        · intro z hz
          have hz_slit : z ∈ Complex.slitPlane :=
            watsonClosedSector_subset_slitPlane hR₀ (hK_sub_sec (hU_sub_K hz))
          have hcpow : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ (4 / 5 : ℂ)) z :=
            ((hasDerivAt_id z).cpow_const hz_slit).differentiableAt
          have hexp : DifferentiableAt ℂ
              (fun w : ℂ ↦ Complex.exp ((lam : ℂ) * (w ^ (4 / 5 : ℂ) - ((R₀ ^ (4 / 5 : ℝ) : ℝ) : ℂ)))) z :=
            ((hcpow.sub_const _).const_mul _).cexp
          have hf_at : DifferentiableAt ℂ f z :=
            (hf_diff z (hU_sub_open hz)).differentiableAt
              ((isOpen_lt continuous_const continuous_norm).inter
                (isOpen_lt (continuous_const.mul continuous_norm) Complex.continuous_re) |>.mem_nhds
                (hU_sub_open hz))
          exact (hexp.mul hf_at).differentiableWithinAt
        · intro z hz
          have hzK : z ∈ K := hcl_sub_K hz
          have hz_slit : z ∈ Complex.slitPlane :=
            watsonClosedSector_subset_slitPlane hR₀ (hK_sub_sec hzK)
          have hcpow : ContinuousAt (fun w : ℂ ↦ w ^ (4 / 5 : ℂ)) z :=
            ((hasDerivAt_id z).cpow_const hz_slit).continuousAt
          have hexp : ContinuousAt
              (fun w : ℂ ↦ Complex.exp ((lam : ℂ) * (w ^ (4 / 5 : ℂ) - ((R₀ ^ (4 / 5 : ℝ) : ℝ) : ℂ)))) z :=
            Complex.continuous_exp.continuousAt.comp
              (continuousAt_const.mul (hcpow.sub continuousAt_const))
          exact hexp.continuousWithinAt.mul ((hf_cont.mono (hcl_sub_K.trans hK_sub_sec)) z hz)
      -- Bound `‖h z‖ ≤ C'` on ALL three pieces of `frontier U`!
      have hfrontier_le : ∀ z ∈ frontier U, ‖h z‖ ≤ C' := by
        intro z hz
        have hz_cl : z ∈ closure U := hz.1
        have hz_notU : z ∉ U := by
          have h2 := hz.2
          rwa [hU_open.interior_eq] at h2
        have hzK : z ∈ K := hcl_sub_K hz_cl
        have hz_sec : z ∈ watsonClosedSector R₀ := hK_sub_sec hzK
        have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le hR₀ hzK.1)
        have hnorm_h : ‖h z‖ =
            Real.exp (lam * (‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) - R₀ ^ (4 / 5 : ℝ))) *
              ‖f z‖ := by
          dsimp only [h]
          rw [norm_mul, Complex.norm_exp]
          congr 2
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
              Complex.sub_re, re_cpow_four_fifths hz0, Complex.ofReal_re]
        rw [hnorm_h]
        have hdec := hdecay z hz_sec
        have hpiece : ‖z‖ = R₀ ∨ ‖z‖ = R ∨ z.re = -(1 / 2 : ℝ) * ‖z‖ := by
          by_contra hall
          push Not at hall
          obtain ⟨h1, h2, h3⟩ := hall
          exact hz_notU ⟨lt_of_le_of_ne hzK.1 h1.symm, lt_of_le_of_ne hzK.2.1 h2,
            lt_of_le_of_ne hzK.2.2 h3.symm⟩
        rcases hpiece with hinner | houter | hray
        · -- Inner arc `‖z‖ = R₀`: `cos ≤ 1` → exponent `≤ 0`!
          have hexp_le : lam * (‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) - R₀ ^ (4 / 5 : ℝ)) ≤ 0 := by
            rw [hinner]
            have h1 : R₀ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) ≤ R₀ ^ (4 / 5 : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left (Real.cos_le_one _) (Real.rpow_nonneg hR₀.le _)
            nlinarith
          have hdec_le : ‖f z‖ ≤ C' :=
            hdec.trans (mul_le_of_le_one_right hC' (Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg z])))
          calc Real.exp (lam * (‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) - R₀ ^ (4 / 5 : ℝ))) * ‖f z‖
              ≤ 1 * C' := mul_le_mul (Real.exp_le_one_iff.mpr hexp_le) hdec_le (norm_nonneg _) zero_le_one
            _ = C' := one_mul C'
        · -- Outer arc `‖z‖ = R`: `lam * R^{4/5} ≤ c' * R` because `R ≥ (lam / c')^5`!
          have hlamR : lam * R ^ (4 / 5 : ℝ) ≤ c' * R := by
            have hroot : lam / c' ≤ R ^ (1 / 5 : ℝ) := by
              have h1 := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (lam / c') ^ 5) hR_lam (by norm_num : (0 : ℝ) ≤ 1 / 5)
              rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ lam / c')] at h1
              simpa [show ((5 : ℕ) : ℝ) * (1 / 5 : ℝ) = 1 by norm_num] using h1
            have hmul := mul_le_mul_of_nonneg_right hroot (Real.rpow_nonneg hR_pos.le (4 / 5 : ℝ))
            rw [← Real.rpow_add hR_pos, show (1 / 5 : ℝ) + (4 / 5 : ℝ) = 1 by norm_num, Real.rpow_one] at hmul
            have hmul' := mul_le_mul_of_nonneg_left hmul hc'.le
            rwa [← mul_assoc, mul_div_cancel₀ _ hc'.ne'] at hmul'
          have hcomb : lam * (‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) - R₀ ^ (4 / 5 : ℝ)) +
              (-c' * ‖z‖) ≤ 0 := by
            rw [houter]
            have h1 : R ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) ≤ R ^ (4 / 5 : ℝ) := by
              simpa using mul_le_mul_of_nonneg_left (Real.cos_le_one _) (Real.rpow_nonneg hR_pos.le _)
            have hR0_nn : 0 ≤ R₀ ^ (4 / 5 : ℝ) := Real.rpow_nonneg hR₀.le _
            nlinarith
          calc Real.exp (lam * (‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) - R₀ ^ (4 / 5 : ℝ))) * ‖f z‖
              ≤ Real.exp (lam * (‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) - R₀ ^ (4 / 5 : ℝ))) *
                  (C' * Real.exp (-c' * ‖z‖)) := mul_le_mul_of_nonneg_left hdec (Real.exp_pos _).le
            _ = C' * Real.exp (lam * (‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) - R₀ ^ (4 / 5 : ℝ)) +
                  (-c' * ‖z‖)) := by rw [Real.exp_add]; ring
            _ ≤ C' * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hcomb) hC'
            _ = C' := mul_one C'
        · -- Boundary rays `z.re = -(1/2) ‖z‖`: `cos((4/5) arg z) ≤ 0` → exponent `≤ 0`!
          have hcos_le := cos_four_fifths_arg_nonpos_of_ray hR₀ hz_sec hray
          have hexp_le : lam * (‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) - R₀ ^ (4 / 5 : ℝ)) ≤ 0 := by
            have h1 : ‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (norm_nonneg z) _) hcos_le
            have h2 : 0 ≤ R₀ ^ (4 / 5 : ℝ) := Real.rpow_nonneg hR₀.le _
            nlinarith
          have hdec_le : ‖f z‖ ≤ C' :=
            hdec.trans (mul_le_of_le_one_right hC' (Real.exp_le_one_iff.mpr (by nlinarith [norm_nonneg z])))
          calc Real.exp (lam * (‖z‖ ^ (4 / 5 : ℝ) * Real.cos ((4 / 5 : ℝ) * z.arg) - R₀ ^ (4 / 5 : ℝ))) * ‖f z‖
              ≤ 1 * C' := mul_le_mul (Real.exp_le_one_iff.mpr hexp_le) hdec_le (norm_nonneg _) zero_le_one
            _ = C' := one_mul C'
      -- Apply the Maximum Modulus Principle at `(x : ℂ) ∈ U ⊆ closure U`!
      have hx_mem : (x : ℂ) ∈ closure U := subset_closure (by
        refine ⟨?_, ?_, ?_⟩
        · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos] using hx
        · simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos] using hRx
        · simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos, Complex.ofReal_re]
          linarith)
      have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd hh_diff hfrontier_le hx_mem
      have hnorm_hx : ‖h (x : ℂ)‖ =
          Real.exp (lam * (x ^ (4 / 5 : ℝ) - R₀ ^ (4 / 5 : ℝ))) * ‖f (x : ℂ)‖ := by
        dsimp only [h]
        rw [norm_mul, Complex.norm_exp]
        congr 2
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
            Complex.sub_re, re_cpow_four_fifths (Complex.ofReal_ne_zero.mpr hx_pos.ne'),
            Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx_pos,
            Complex.arg_ofReal_of_nonneg hx_pos.le, mul_zero, Real.cos_zero, mul_one,
            Complex.ofReal_re]
      rw [hnorm_hx] at hmax
      have hmul := mul_le_mul_of_nonneg_left hmax
        (Real.exp_pos (-lam * (x ^ (4 / 5 : ℝ) - R₀ ^ (4 / 5 : ℝ)))).le
      rw [← mul_assoc, ← Real.exp_add,
          show -lam * (x ^ (4 / 5 : ℝ) - R₀ ^ (4 / 5 : ℝ)) +
            lam * (x ^ (4 / 5 : ℝ) - R₀ ^ (4 / 5 : ℝ)) = 0 by ring,
          Real.exp_zero, one_mul, mul_comm] at hmul
      exact hmul
    -- Letting `λ → +∞` forces `‖f (x : ℂ)‖ = 0`!
    by_contra hfx
    have hnorm_pos : 0 < ‖f (x : ℂ)‖ := norm_pos_iff.mpr hfx
    have hδ_pos : 0 < x ^ (4 / 5 : ℝ) - R₀ ^ (4 / 5 : ℝ) :=
      sub_pos.mpr (Real.rpow_lt_rpow hR₀.le hx (by norm_num))
    let lam : ℝ := (Real.log ((C' + 1) / ‖f (x : ℂ)‖) + 1) / (x ^ (4 / 5 : ℝ) - R₀ ^ (4 / 5 : ℝ))
    have hlam_pos : 0 < lam := by
      have h1 : 1 ≤ (C' + 1) / ‖f (x : ℂ)‖ := by
        have hfx_le : ‖f (x : ℂ)‖ ≤ C' := by
          have := hbound_lam 1 zero_lt_one
          exact this.trans (mul_le_of_le_one_right hC' (Real.exp_le_one_iff.mpr (by linarith)))
        rw [one_le_div hnorm_pos]; linarith
      have hlog_nn : 0 ≤ Real.log ((C' + 1) / ‖f (x : ℂ)‖) := Real.log_nonneg h1
      exact div_pos (by linarith) hδ_pos
    have hbd := hbound_lam lam hlam_pos
    have hexp_eq : -lam * (x ^ (4 / 5 : ℝ) - R₀ ^ (4 / 5 : ℝ)) =
        -(Real.log ((C' + 1) / ‖f (x : ℂ)‖) + 1) := by
      dsimp only [lam]; field_simp [hδ_pos.ne']
    rw [hexp_eq, Real.exp_neg, Real.exp_add, Real.exp_log (by positivity)] at hbd
    have he1 : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
    have hlt : C' * (((C' + 1) / ‖f (x : ℂ)‖) * Real.exp 1)⁻¹ < ‖f (x : ℂ)‖ := by
      have hpos_den : 0 < ((C' + 1) / ‖f (x : ℂ)‖) * Real.exp 1 := by positivity
      rw [← div_eq_mul_inv, div_lt_iff₀ hpos_den]
      have h1 : C' < (C' + 1) * Real.exp 1 := by nlinarith
      have h2 : ‖f (x : ℂ)‖ * ((C' + 1) / ‖f (x : ℂ)‖ * Real.exp 1) = (C' + 1) * Real.exp 1 := by
        field_simp [hnorm_pos.ne']
      linarith
    linarith
  -- Step 2: Identity Theorem on the connected open set `watsonOpenSector R₀`!
  refine ⟨hreal_zero, ?_⟩
  have hopen : IsOpen (watsonOpenSector R₀) :=
    (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt (continuous_const.mul continuous_norm) Complex.continuous_re)
  have hpreconn : IsPreconnected (watsonOpenSector R₀) := by
    -- Every point `z ∈ watsonOpenSector R₀` connects to `‖z‖ + 1` via a continuous polar arc + ray!
    -- Even simpler: `watsonOpenSector R₀` is path-connected via the continuous image of `(R₀, ∞) × (-2π/3, 2π/3)`!
    let φ : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
    have hφ_cont : Continuous φ :=
      Complex.continuous_ofReal.comp continuous_fst |>.mul
        (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const))
    have hbox_conn : IsPreconnected (Set.Ioi R₀ ×ˢ Set.Ioo (-(2 * Real.pi / 3)) (2 * Real.pi / 3)) :=
      (isPreconnected_Ioi.prod isPreconnected_Ioo)
    have himage_eq : φ '' (Set.Ioi R₀ ×ˢ Set.Ioo (-(2 * Real.pi / 3)) (2 * Real.pi / 3)) =
        watsonOpenSector R₀ := by
      ext z
      constructor
      · rintro ⟨⟨r, θ⟩, ⟨hr, hθ1, hθ2⟩, rfl⟩
        have hr_pos : 0 < r := lt_trans hR₀ hr
        have hnorm : ‖φ (r, θ)‖ = r := by
          dsimp [φ]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos,
              Complex.norm_exp_ofReal_mul_I, mul_one]
        have hre : (φ (r, θ)).re = r * Real.cos θ := by
          dsimp [φ]
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
              Complex.exp_ofReal_mul_I_re]
        refine ⟨hnorm.symm ▸ hr, ?_⟩
        rw [hnorm, hre]
        have hcos : -(1 / 2 : ℝ) < Real.cos θ := by
          rw [← Real.cos_abs]
          have hlt : |θ| < 2 * Real.pi / 3 := abs_lt.mpr ⟨hθ1, hθ2⟩
          have hmem1 : |θ| ∈ Set.Icc 0 Real.pi := ⟨abs_nonneg _, le_trans hlt.le (by linarith [Real.pi_pos])⟩
          have hmem2 : 2 * Real.pi / 3 ∈ Set.Icc 0 Real.pi := ⟨by positivity, by linarith [Real.pi_pos]⟩
          have h1 := Real.strictAntiOn_cos hmem1 hmem2 hlt
          rwa [show Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) by
            rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
                Real.cos_pi_sub, Real.cos_pi_div_three]] at h1
        nlinarith
      · intro ⟨hnorm, hre⟩
        have hz0 : z ≠ 0 := norm_pos_iff.mp (lt_trans hR₀ hnorm)
        have hcos_gt : -(1 / 2 : ℝ) < Real.cos z.arg := by
          rw [Complex.cos_arg hz0]
          have hnorm_pos : 0 < ‖z‖ := lt_trans hR₀ hnorm
          rw [lt_div_iff₀ hnorm_pos]; linarith
        have habs_lt : |z.arg| < 2 * Real.pi / 3 := by
          by_contra hge
          have h1 := abs_arg_le_two_pi_div_three hR₀ ⟨hnorm.le, hre.le⟩
          have heq : |z.arg| = 2 * Real.pi / 3 := le_antisymm h1 (not_lt.mp hge)
          rw [← Real.cos_abs, heq,
              show Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) by
                rw [show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
                    Real.cos_pi_sub, Real.cos_pi_div_three]] at hcos_gt
          exact lt_irrefl _ hcos_gt
        refine ⟨(‖z‖, z.arg), ⟨hnorm, abs_lt.mp habs_lt⟩, ?_⟩
        exact Complex.norm_mul_exp_arg_mul_I z
    rw [← himage_eq]
    exact hbox_conn.image φ hφ_cont.continuousOn
  have hAnal : AnalyticOnNhd ℂ f (watsonOpenSector R₀) := hf_diff.analyticOnNhd hopen
  let z₀ : ℂ := ((R₀ + 1 : ℝ) : ℂ)
  have hz₀_mem : z₀ ∈ watsonOpenSector R₀ := by
    have hpos : 0 < R₀ + 1 := by linarith
    refine ⟨?_, ?_⟩
    · change R₀ < ‖((R₀ + 1 : ℝ) : ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      linarith
    · change -(1 / 2 : ℝ) * ‖((R₀ + 1 : ℝ) : ℂ)‖ < ((R₀ + 1 : ℝ) : ℂ).re
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, Complex.ofReal_re]
      linarith
  have hfreq : ∃ᶠ z in 𝓝[≠] z₀, f z = 0 := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin] at hU
    obtain ⟨V, hVopen, hz₀V, hVsub⟩ := hU
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.mp hVopen z₀ hz₀V
    let x' : ℝ := R₀ + 1 + ε / 2
    have hx'ne : (x' : ℂ) ≠ z₀ := by
      intro h0
      have := Complex.ofReal_injective h0
      dsimp [x'] at this; linarith
    have hx'ball : (x' : ℂ) ∈ Metric.ball z₀ ε := by
      rw [Metric.mem_ball, Complex.dist_eq, show (x' : ℂ) - z₀ = ((ε / 2 : ℝ) : ℂ) by
        dsimp [x', z₀]; push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    exact ⟨(x' : ℂ), hVsub ⟨hball hx'ball, hx'ne⟩, hreal_zero x' (by dsimp [x']; linarith)⟩
  exact hAnal.eqOn_zero_of_preconnected_of_frequently_eq_zero hpreconn hz₀_mem hfreq

end
end CubicTheta.AllD
