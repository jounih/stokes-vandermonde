module

public import PakPrimes.MockThetaAndHurwitz
public import Mathlib.Data.Finset.Sort

/-! # False Theta Differential Transcendence, 5-Tuple Mock/False Joint Independence & D-Algebraic Controls

End-to-end Tier-1 Lean 4.36.0 formalization (fully proved, strictly
`[propext, Classical.choice, Quot.sound]`) of:

1. **General Multi-Function Simple-Pole Joint Differential Independence Engine over `ℂ(u)`**:
   (`JointSimplePoleFamily`, `joint_stokes_vandermonde_no_ade`, `joint_stokes_vandermonde_no_rat_ade`,
   `joint_laplaceTransform_no_rat_ade`, `joint_mordellIntegral_no_rat_ade`)
   For any finite family `φ : Fin K → ℂ → ℂ` of Borel kernels sharing a common ray `θ₀ : ℝ`
   with pairwise disjoint, strictly increasing, unbounded simple-pole lattices `e^{i θ₀} ω i m`
   (`res i m ≠ 0`) and flanking-ray `ExpType` bounds, the tuple of formal Laplace series — and
   hence the tuple of analytic Laplace or Mordell integrals — satisfies NO nonzero joint
   rational-coefficient algebraic differential equation over `ℂ(u)`.
2. **False Theta Borel & Mordell Differential Transcendence Witnesses**:
   - Entire even-sinc engine `sinhSqrt z = ∑' n, z^n / (2n + 1)!` (`w * sinhSqrt (w^2) = sinh w`),
   - Weight-`3/2` false theta `∑ n q^{n²}` Mordell integral `∫_0^∞ e^{-u x²} (x² / sinh x) dx`
     (`falseThetaSinhMordell_no_rat_ade`),
   - Kontsevich / `χ₁₂` false-theta Mordell integral `∫_0^∞ e^{-u x²} (sinh(2x) / (2 cosh(3x))) dx`
     (`kontsevichFalseMordell_no_rat_ade`),
   - Literal Rogers false theta `ψ(t) = ∑' n, (-1)^n e^{-(n + 1/2)² t}` Stieltjes integral
     `∫_0^∞ ψ(t) / (u + t) dt = L[∑' n, (-1)^n / (z + (n + 1/2)²)](u)` via exact Fubini
     (`rogersFalseThetaStieltjes_no_rat_ade`),
   - Positive-ray (`θ₀ = 0`) Rogers false-theta Borel kernel `1 / cos(√z)`
     (`rogersCosBorel_formal_no_rat_ade`).
3. **Flagship 5-Function Joint Differential Independence over `ℂ(u)`**:
   (`five_mock_false_mordell_joint_no_rat_ade`)
   Unconditional joint differential independence over `ℂ(u)` of the 5-tuple
   `(mordellCoshIntegral, mockThetaOmegaMordell, mockThetaFMordell, falseThetaSinhMordell, kontsevichFalseMordell)`
   via pairwise disjoint reduced pole denominators `{2, 3 (odd), 3 (even), 1, 6}`.
4. **Explicit True-Theta / Modular, Borel-Kernel, & Quadrant-III Controls**:
   - `ramanujan_chazy_ode`: Ramanujan's ODEs imply Chazy's order-3 autonomous ODE
     `2 D³ E₂ - 2 E₂ D² E₂ + 3 (D E₂)² = 0` in any commutative differential ring.
   - `trueGaussianMordell_is_d_algebraic`: True Gaussian Mordell integral
     `∫_0^∞ e^{-u x²} x e^{-x²} dx = 1 / (2 (u + 1))` satisfies `Y₁ + 2 Y₀² = 0`.
   - `sechSqrt_kernel_is_d_algebraic`: `φ(ξ) = 1 / cosh(√ξ)` satisfies `4 ξ (φ')² - φ² + φ⁴ = 0`
     on `(0, ∞)` (D-algebraic kernel → D-transcendental Mordell integral).
   - `rogers_false_theta_qdiff_control`: Bivariate Rogers false theta `Ψ(x, q)` satisfies
     the exact 1st-order linear `q`-difference equation `Ψ(x, q) = 1 - x q Ψ(q x, q)`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.FalseThetaDichotomy

open Complex Real Filter MeasureTheory Set MvPolynomial Matrix
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
open PakPrimes.MockModularWeightOne PakPrimes.MockThetaAndHurwitz
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. General Multi-Function Simple-Pole Joint Differential Independence Engine over `ℂ(u)` -/

/-- Complex-analytic hypotheses for a `K`-tuple of simple-pole Borel transforms `φ : Fin K → ℂ → ℂ`
along a common rotated ray `e^{i θ₀}` with pairwise disjoint, strictly increasing, unbounded
pole lattices `e^{i θ₀} ω i m` (`res i m ≠ 0`) and common flanking-ray `ExpType` bounds. -/
structure JointSimplePoleFamily
    (K : ℕ) (φ : Fin K → ℂ → ℂ) (θ₀ : ℝ) (ω : Fin K → ℕ → ℝ) (res : Fin K → ℕ → ℂ) where
  α₀ : ℝ
  θ : ℝ
  ε : ℝ
  hθ_pos : 0 < θ
  hθ_lt : θ < α₀
  hα₀_lt : α₀ < Real.pi / 2
  hε_pos : 0 < ε
  ω_pos : ∀ i : Fin K, 0 < ω i 0
  ω_mono : ∀ i : Fin K, StrictMono (ω i)
  ω_unbounded : ∀ i : Fin K, ∀ B : ℝ, ∃ m : ℕ, B < ω i m
  ω_disjoint : ∀ i₁ i₂ : Fin K, i₁ ≠ i₂ → ∀ m₁ m₂ : ℕ, ω i₁ m₁ ≠ ω i₂ m₂
  res_ne_zero : ∀ i : Fin K, ∀ m : ℕ, res i m ≠ 0
  analyticOn : ∀ i : Fin K, AnalyticOnNhd ℂ (φ i) (rotatedPuncturedWedge θ₀ α₀ ε (ω i))
  pole_res : ∀ i : Fin K, ∀ m : ℕ, ∃ L : ℂ,
    Filter.Tendsto
      (fun z : ℂ => φ i z - res i m / (z - Complex.exp (I * (θ₀ : ℂ)) * (ω i m : ℂ)))
      (𝓝[≠] (Complex.exp (I * (θ₀ : ℂ)) * (ω i m : ℂ))) (𝓝 L)
  expType_plus : ∀ i : Fin K, ExpType (Minor.pull (Complex.exp (I * ((θ₀ + θ : ℝ) : ℂ))) (φ i))
  expType_minus : ∀ i : Fin K, ExpType (Minor.pull (Complex.exp (I * ((θ₀ - θ : ℝ) : ℂ))) (φ i))

/-- Formal evaluation of a joint non-autonomous differential polynomial
`P ∈ ℂ[u][Y_{i, j}]` at `S : Fin K → PowerSeries ℂ` inside `LaurentSeries ℂ`. -/
@[expose] def jointFormalEvalPoly {K r : ℕ} (S : Fin K → PowerSeries ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) : LaurentSeries ℂ :=
  MvPolynomial.eval₂ polyToLaurent
    (fun ij : Fin K × Fin (r + 1) => ((d_u^[ij.2.val] (S ij.1) : PowerSeries ℂ) : LaurentSeries ℂ)) P

/-- Formal evaluation of a joint rational-coefficient differential polynomial
`P ∈ ℂ(u)[Y_{i, j}]` at `S : Fin K → PowerSeries ℂ` inside `LaurentSeries ℂ`. -/
@[expose] def jointFormalEvalRat {K r : ℕ} (S : Fin K → PowerSeries ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (RatFunc ℂ)) : LaurentSeries ℂ :=
  MvPolynomial.eval₂ ratToLaurent
    (fun ij : Fin K × Fin (r + 1) => ((d_u^[ij.2.val] (S ij.1) : PowerSeries ℂ) : LaurentSeries ℂ)) P

/-- Evaluation of the `Polynomial ℂ` coefficients of a joint differential polynomial at `u : ℂ`. -/
@[expose] def jointEvalU {K r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) (u : ℂ) :
    MvPolynomial (Fin K × Fin (r + 1)) ℂ :=
  MvPolynomial.map (Polynomial.evalRingHom u) P

/-- Evaluation of the `RatFunc ℂ` coefficients of a joint differential polynomial at `u : ℂ`. -/
@[expose] def jointEvalRatU {K r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (RatFunc ℂ)) (u : ℂ) :
    MvPolynomial (Fin K × Fin (r + 1)) ℂ :=
  ∑ α ∈ P.support, MvPolynomial.monomial α (ratEval (P.coeff α) u)

/-! #### 1A. Coefficient Clearing (`revPolyJ`, `jointFormalEvalW`) and Rotation Reduction -/

private lemma uLaurent_pow' (k : ℕ) :
    uLaurent ^ k = HahnSeries.single (-(k : ℤ)) (1 : ℂ) := by
  induction k with
  | zero => simp [uLaurent]
  | succ k ih =>
    rw [pow_succ, ih, uLaurent, HahnSeries.single_mul_single, one_mul]
    have hidx : -(k : ℤ) + (-1 : ℤ) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hidx]

private def revPolyJ (N : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k)

private lemma poly_finset_sum_coeffJ {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (m : ℕ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  simpa only [Polynomial.lcoeff_apply] using map_sum (Polynomial.lcoeff ℂ m) f s

private lemma revPolyJ_eval_inv {N : ℕ} (p : Polynomial ℂ) (hp : p.natDegree ≤ N)
    {u : ℂ} (hu : u ≠ 0) :
    (revPolyJ N p).eval u⁻¹ = u⁻¹ ^ N * p.eval u := by
  have hsum : p = ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k :=
    Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
  conv_rhs => rw [hsum]
  change Polynomial.evalRingHom u⁻¹ (revPolyJ N p) = u⁻¹ ^ N * Polynomial.evalRingHom u _
  simp only [revPolyJ, map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    map_pow, Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have heq : u⁻¹ ^ (N - k) = u⁻¹ ^ N * u ^ k := by
    calc u⁻¹ ^ (N - k) = u⁻¹ ^ (N - k) * (u⁻¹ ^ k * u ^ k) := by
          rw [← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]
      _ = (u⁻¹ ^ (N - k) * u⁻¹ ^ k) * u ^ k := by ring
      _ = u⁻¹ ^ N * u ^ k := by rw [← pow_add, Nat.sub_add_cancel hk_le]
  rw [heq]; ring

private lemma single_mul_polyToLaurentJ {N : ℕ} (p : Polynomial ℂ) (hp : p.natDegree ≤ N) :
    HahnSeries.single (N : ℤ) (1 : ℂ) * polyToLaurent p =
      (((revPolyJ N p : Polynomial ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  have hsum : p = ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k :=
    Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
  conv_lhs => rw [hsum]
  have halg : ∀ c : ℂ, algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := fun c =>
    HahnSeries.ofPowerSeries_C c
  have hL : HahnSeries.single (N : ℤ) (1 : ℂ) *
      polyToLaurent (∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k) =
      ∑ k ∈ Finset.range (N + 1), HahnSeries.single (N : ℤ) (1 : ℂ) *
        (HahnSeries.C (p.coeff k) * uLaurent ^ k) := by
    simp only [polyToLaurent, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul,
      map_pow, Polynomial.aeval_C, Polynomial.aeval_X, halg, Finset.mul_sum]
  have hR : (((revPolyJ N p : Polynomial ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ∑ k ∈ Finset.range (N + 1),
        HahnSeries.C (p.coeff k) *
          ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ (N - k) := by
    unfold revPolyJ
    change HahnSeries.ofPowerSeries ℤ ℂ
      (Polynomial.coeToPowerSeries.ringHom
        (∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k))) = _
    simp only [map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, HahnSeries.ofPowerSeries_C, Polynomial.coe_X]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [uLaurent_pow' k]
  have hX : ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ (N - k) =
      HahnSeries.single ((N - k : ℕ) : ℤ) (1 : ℂ) := by
    rw [← PowerSeries.coe_pow, HahnSeries.ofPowerSeries_X_pow]
  rw [hX, ← mul_assoc, mul_comm (HahnSeries.single (N : ℤ) 1) (HahnSeries.C (p.coeff k)),
    mul_assoc, HahnSeries.single_mul_single, one_mul]
  have hidx : (N : ℤ) + -(k : ℤ) = ((N - k : ℕ) : ℤ) := by omega
  rw [hidx, HahnSeries.C_apply, HahnSeries.single_mul_single]

private lemma polyToLaurent_injectiveJ : Function.Injective polyToLaurent := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  have hsingle := single_mul_polyToLaurentJ p le_rfl
  rw [hp, mul_zero] at hsingle
  have hps : ((revPolyJ p.natDegree p : Polynomial ℂ) : PowerSeries ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ) (hsingle.symm.trans (map_zero _).symm)
  have hpoly : revPolyJ p.natDegree p = 0 := Polynomial.coe_inj.mp hps
  have hcoeff0 : (revPolyJ p.natDegree p).coeff 0 = 0 := by rw [hpoly]; simp
  rw [revPolyJ, poly_finset_sum_coeffJ] at hcoeff0
  have hterm : ∀ k ∈ Finset.range (p.natDegree + 1),
      (Polynomial.C (p.coeff k) * Polynomial.X ^ (p.natDegree - k)).coeff 0 =
        if k = p.natDegree then p.coeff p.natDegree else 0 := by
    intro k hk
    have hk_le : k ≤ p.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    by_cases hkp : k = p.natDegree
    · subst hkp; simp
    · have hne : p.natDegree - k ≠ 0 := by omega
      simp [hkp, Ne.symm hne]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq'] at hcoeff0
  simp only [Finset.mem_range, Nat.lt_succ_self, ↓reduceIte] at hcoeff0
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hcoeff0)

private def maxUDegJ {ι : Type*} (P : MvPolynomial ι (Polynomial ℂ)) : ℕ :=
  P.support.sup fun α => (P.coeff α).natDegree

private lemma natDegree_le_maxUDegJ {ι : Type*} (P : MvPolynomial ι (Polynomial ℂ))
    (α : ι →₀ ℕ) : (P.coeff α).natDegree ≤ maxUDegJ P := by
  by_cases hα : α ∈ P.support
  · exact Finset.le_sup (f := fun α => (P.coeff α).natDegree) hα
  · rw [MvPolynomial.notMem_support_iff.mp hα, Polynomial.natDegree_zero]
    exact Nat.zero_le _

private def revMvPolyJ {ι : Type*} (N : ℕ) (P : MvPolynomial ι (Polynomial ℂ)) :
    MvPolynomial ι (Polynomial ℂ) :=
  ∑ α ∈ P.support, MvPolynomial.monomial α (revPolyJ N (P.coeff α))

private lemma revMvPolyJ_coeff {ι : Type*} (N : ℕ) (P : MvPolynomial ι (Polynomial ℂ))
    (α : ι →₀ ℕ) :
    (revMvPolyJ N P).coeff α = revPolyJ N (P.coeff α) := by
  classical
  unfold revMvPolyJ
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, Finset.sum_eq_zero]
    · simp [revPolyJ]
    · intro β hβ
      have hne : β ≠ α := fun h => hα (h ▸ hβ)
      simp [hne]

private lemma jointEvalU_revMvPolyJ {K r N : ℕ}
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hN : ∀ α, (P.coeff α).natDegree ≤ N) {u : ℂ} (hu : u ≠ 0) :
    jointEvalU (revMvPolyJ N P) u⁻¹ = (u⁻¹ ^ N) • jointEvalU P u := by
  classical
  ext α
  simp only [jointEvalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, revMvPolyJ_coeff,
    MvPolynomial.coeff_smul, smul_eq_mul]
  exact revPolyJ_eval_inv (P.coeff α) (hN α) hu

private def jointFormalEvalW {K r : ℕ} (S : Fin K → PowerSeries ℂ)
    (Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) : PowerSeries ℂ :=
  MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom
    (fun ij : Fin K × Fin (r + 1) => d_u^[ij.2.val] (S ij.1)) Q

private lemma jointFormalEvalW_eq_zero_iff_poly {K r : ℕ} (S : Fin K → PowerSeries ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) {N : ℕ}
    (hN : ∀ α, (P.coeff α).natDegree ≤ N) :
    jointFormalEvalW S (revMvPolyJ N P) = 0 ↔ jointFormalEvalPoly S P = 0 := by
  have hlink : HahnSeries.single (N : ℤ) (1 : ℂ) * jointFormalEvalPoly S P =
      ((jointFormalEvalW S (revMvPolyJ N P) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    have hP_sum : P = ∑ α ∈ P.support, MvPolynomial.monomial α (P.coeff α) := MvPolynomial.as_sum P
    conv_lhs => arg 2; rw [hP_sum]
    unfold jointFormalEvalPoly jointFormalEvalW revMvPolyJ
    rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
    simp_rw [MvPolynomial.eval₂_monomial]
    change ∑ α ∈ P.support, HahnSeries.single (N : ℤ) 1 *
        (polyToLaurent (P.coeff α) * α.prod fun ij e =>
          ((d_u^[ij.2.val] (S ij.1) : PowerSeries ℂ) : LaurentSeries ℂ) ^ e) =
      HahnSeries.ofPowerSeries ℤ ℂ
        (∑ α ∈ P.support, Polynomial.coeToPowerSeries.ringHom (revPolyJ N (P.coeff α)) *
          α.prod fun ij e => (d_u^[ij.2.val] (S ij.1)) ^ e)
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hpow_eq : (α.prod fun ij e => ((d_u^[ij.2.val] (S ij.1) : PowerSeries ℂ) : LaurentSeries ℂ) ^ e) =
        ((α.prod fun ij e => (d_u^[ij.2.val] (S ij.1)) ^ e : PowerSeries ℂ) : LaurentSeries ℂ) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [hpow_eq, ← mul_assoc, single_mul_polyToLaurentJ (P.coeff α) (hN α),
      map_mul, Polynomial.coeToPowerSeries.ringHom_apply]
  have hsingle_ne : (HahnSeries.single (N : ℤ) (1 : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (fun x : LaurentSeries ℂ => x.coeff (N : ℤ)) h0
    simp at this
  constructor
  · intro hw
    rw [hw, PowerSeries.coe_zero] at hlink
    exact (mul_eq_zero.mp hlink).resolve_left hsingle_ne
  · intro hp
    rw [hp, mul_zero] at hlink
    exact HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ) (hlink.symm.trans (map_zero _).symm)

/-! #### 1B. Scaling & Rotation Reduction (`θ₀` → `0`) -/

private def scaleSubstJ (μ : ℂ) : PowerSeries ℂ →+* PowerSeries ℂ where
  toFun S := PowerSeries.mk fun n => μ ^ n * PowerSeries.coeff n S
  map_one' := by
    ext n; cases n <;> simp
  map_mul' S T := by
    ext n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hp, pow_add]; ring
  map_zero' := by ext n; simp
  map_add' S T := by ext n; simp only [PowerSeries.coeff_mk, map_add, mul_add]

@[simp] private lemma scaleSubstJ_coeff (μ : ℂ) (S : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (scaleSubstJ μ S) = μ ^ n * PowerSeries.coeff n S := by
  change PowerSeries.coeff n (PowerSeries.mk fun k => μ ^ k * PowerSeries.coeff k S) = _
  exact PowerSeries.coeff_mk n _

private lemma coeff_comp_C_mul_XJ (p : Polynomial ℂ) (μ : ℂ) (k : ℕ) :
    (p.comp (Polynomial.C μ * Polynomial.X)).coeff k = μ ^ k * p.coeff k := by
  induction p using Polynomial.induction_on' with
  | add a b ha hb => simp only [Polynomial.add_comp, Polynomial.coeff_add, ha, hb, mul_add]
  | monomial i c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
      Polynomial.X_pow_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow]
    split_ifs with hik
    · subst hik; ring
    · simp

private lemma scaleSubstJ_coe_poly (μ : ℂ) (p : Polynomial ℂ) :
    scaleSubstJ μ (p : PowerSeries ℂ) =
      ((p.comp (Polynomial.C μ * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) := by
  ext n
  rw [scaleSubstJ_coeff, Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_comp_C_mul_XJ]

private lemma scaleSubstJ_revPoly (μ : ℂ) (hμ : μ ≠ 0) {N : ℕ} (p : Polynomial ℂ) :
    scaleSubstJ μ ((revPolyJ N p : Polynomial ℂ) : PowerSeries ℂ) =
      PowerSeries.C (μ ^ N) * ((revPolyJ N (p.comp (Polynomial.C μ⁻¹ * Polynomial.X)) : Polynomial ℂ) : PowerSeries ℂ) := by
  rw [scaleSubstJ_coe_poly, ← Polynomial.coe_C, ← Polynomial.coe_mul, Polynomial.coe_inj]
  ext m
  rw [coeff_comp_C_mul_XJ, Polynomial.coeff_C_mul]
  simp only [revPolyJ, poly_finset_sum_coeffJ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow, coeff_comp_C_mul_XJ]
  split_ifs with hmk
  · subst hmk
    have hpow : μ ^ (N - k) = μ ^ N * μ⁻¹ ^ k := by
      rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero k hμ), ← pow_add,
        Nat.sub_add_cancel hk_le]
    rw [hpow]; ring
  · ring

private lemma d_u_C_mulJ (c : ℂ) (S : PowerSeries ℂ) :
    d_u (PowerSeries.C c * S) = PowerSeries.C c * d_u S := by
  simp only [d_u, Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul]; ring

private lemma d_u_scaleSubstJ {μ : ℂ} (hμ : μ ≠ 0) (S : PowerSeries ℂ) :
    d_u (scaleSubstJ μ S) = PowerSeries.C μ⁻¹ * scaleSubstJ μ (d_u S) := by
  ext n
  rcases n with _ | _ | m
  · change -(PowerSeries.coeff 0 (PowerSeries.X ^ 2 * PowerSeries.derivative (scaleSubstJ μ S))) =
      PowerSeries.coeff 0 (PowerSeries.C μ⁻¹ * scaleSubstJ μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
    rw [PowerSeries.coeff_C_mul, scaleSubstJ_coeff, map_neg, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow_mul']
    simp
  · change -(PowerSeries.coeff 1 (PowerSeries.X ^ 2 * PowerSeries.derivative (scaleSubstJ μ S))) =
      PowerSeries.coeff 1 (PowerSeries.C μ⁻¹ * scaleSubstJ μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
    rw [PowerSeries.coeff_C_mul, scaleSubstJ_coeff, map_neg, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow_mul']
    simp
  · change -(PowerSeries.coeff (m + 2) (PowerSeries.X ^ 2 * PowerSeries.derivative (scaleSubstJ μ S))) =
      PowerSeries.coeff (m + 2) (PowerSeries.C μ⁻¹ * scaleSubstJ μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
    rw [PowerSeries.coeff_C_mul, scaleSubstJ_coeff, map_neg, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow_mul']
    split_ifs with hle2
    · simp only [Nat.add_sub_cancel, PowerSeries.coeff_derivative, scaleSubstJ_coeff]
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ']
      field_simp [hμ]; ring
    · omega

private lemma iteratedDeriv_comp_const_mul_zeroJ {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    (μ : ℂ) (k : ℕ) :
    iteratedDeriv k (fun z => φ (μ * z)) 0 = μ ^ k * iteratedDeriv k φ 0 := by
  have hnear : ∀ m : ℕ, ∀ᶠ z in 𝓝 (0 : ℂ),
      iteratedDeriv m (fun w => φ (μ * w)) z = μ ^ m * iteratedDeriv m φ (μ * z) := by
    intro m
    induction m with
    | zero => exact Filter.Eventually.of_forall fun _ => by simp
    | succ m ih =>
      have hdm_anal : AnalyticAt ℂ (iteratedDeriv m φ) 0 := by
        clear ih
        induction m generalizing φ with
        | zero => simpa using hφ
        | succ t iht => rw [iteratedDeriv_succ']; exact iht hφ.deriv
      have hcont : ContinuousAt (fun z : ℂ => μ * z) 0 := continuousAt_const.mul continuousAt_id
      have hdm_diff : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (iteratedDeriv m φ) (μ * z) := by
        have this' := hdm_anal.eventually_analyticAt
        rw [show (0 : ℂ) = μ * 0 by ring] at this'
        exact (hcont.tendsto.eventually this').mono fun z hz => hz.differentiableAt
      filter_upwards [ih.eventually_nhds, hdm_diff] with z hzeq hzdiff
      rw [iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq hzeq]
      have hchain : HasDerivAt (fun w => μ ^ m * iteratedDeriv m φ (μ * w))
          (μ ^ m * (deriv (iteratedDeriv m φ) (μ * z) * μ)) z :=
        (hzdiff.hasDerivAt.comp z (((hasDerivAt_id z).const_mul μ).congr_deriv (mul_one μ))).const_mul (μ ^ m)
      rw [hchain.deriv, iteratedDeriv_succ]; ring
  simpa using (hnear k).self_of_nhds

private lemma d_u_iter_formalSeries_rotJ {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    {μ : ℂ} (hμ : μ ≠ 0) (j : ℕ) :
    d_u^[j] (formalSeries (fun z => φ (μ * z))) =
      PowerSeries.C (μ⁻¹ ^ (j + 1)) * scaleSubstJ μ (d_u^[j] (formalSeries φ)) := by
  have h0 : formalSeries (fun z => φ (μ * z)) =
      PowerSeries.C μ⁻¹ * scaleSubstJ μ (formalSeries φ) := by
    ext n
    cases n with
    | zero => simp [formalSeries]
    | succ k =>
      simp only [formalSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, scaleSubstJ_coeff]
      rw [iteratedDeriv_comp_const_mul_zeroJ hφ μ k, pow_succ']
      field_simp [hμ]
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      d_u_C_mulJ, d_u_scaleSubstJ hμ, ← mul_assoc, ← map_mul, ← pow_succ]

private def jointRotPoly (K r : ℕ) (μ : ℂ) :
    MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) →+*
      MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Polynomial.compRingHom (Polynomial.C μ⁻¹ * Polynomial.X)))
    (fun ij : Fin K × Fin (r + 1) =>
      MvPolynomial.C (Polynomial.C (μ ^ (ij.2.val + 1))) * MvPolynomial.X ij)

private lemma prod_support_pow_eq_univJ {ι : Type*} [Fintype ι] (α : ι →₀ ℕ) (f : ι → ℂ) :
    (∏ ij ∈ α.support, f ij ^ α ij) = ∏ ij : ι, f ij ^ α ij := by
  refine Finset.prod_subset (Finset.subset_univ _) fun ij _ hnot => ?_
  rw [Finsupp.notMem_support_iff.mp hnot, pow_zero]

private lemma jointRotPoly_coeff {K r : ℕ} (μ : ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) (α : Fin K × Fin (r + 1) →₀ ℕ) :
    (jointRotPoly K r μ P).coeff α =
      Polynomial.C (∏ ij ∈ α.support, (μ ^ (ij.2.val + 1)) ^ α ij) *
        (P.coeff α).comp (Polynomial.C μ⁻¹ * Polynomial.X) := by
  classical
  induction P using MvPolynomial.induction_on generalizing α with
  | C p =>
    simp only [jointRotPoly, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.coeff_C,
      Polynomial.coe_compRingHom_apply]
    split_ifs with hα
    · subst hα; simp
    · simp
  | add A B hA hB =>
    rw [map_add, show (jointRotPoly K r μ A + jointRotPoly K r μ B).coeff α =
        (jointRotPoly K r μ A).coeff α + (jointRotPoly K r μ B).coeff α from rfl,
      hA, hB, show (A + B).coeff α = A.coeff α + B.coeff α from rfl,
      Polynomial.add_comp, mul_add]
  | mul_X A k hA =>
    rw [map_mul]
    have hrot_X : jointRotPoly K r μ (MvPolynomial.X k) =
        MvPolynomial.C (Polynomial.C (μ ^ (k.2.val + 1))) * MvPolynomial.X k := by
      simp [jointRotPoly]
    rw [hrot_X, MvPolynomial.coeff_mul_X']
    have hcoeff_CX : ∀ (Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) (c : Polynomial ℂ),
        (Q * (MvPolynomial.C c * MvPolynomial.X k)).coeff α =
          if k ∈ α.support then c * Q.coeff (α - Finsupp.single k 1) else 0 := by
      intro Q c
      rw [← mul_assoc, mul_comm Q (MvPolynomial.C c), mul_assoc, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_mul_X']
      split_ifs <;> simp
    rw [hcoeff_CX]
    split_ifs with hk
    · let α' : Fin K × Fin (r + 1) →₀ ℕ := α - Finsupp.single k (1 : ℕ)
      rw [hA α']
      have hk1 : 1 ≤ α k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hk))
      have hprod_eq : ∏ ij ∈ α.support, (μ ^ (ij.2.val + 1)) ^ α ij =
          μ ^ (k.2.val + 1) * ∏ ij ∈ α'.support, (μ ^ (ij.2.val + 1)) ^ α' ij := by
        rw [prod_support_pow_eq_univJ, prod_support_pow_eq_univJ]
        rw [← Finset.mul_prod_erase Finset.univ
          (fun ij : Fin K × Fin (r + 1) => (μ ^ (ij.2.val + 1)) ^ α ij) (Finset.mem_univ k)]
        rw [← Finset.mul_prod_erase Finset.univ
          (fun ij : Fin K × Fin (r + 1) => (μ ^ (ij.2.val + 1)) ^ α' ij) (Finset.mem_univ k)]
        have hrest : ∏ ij ∈ Finset.univ.erase k, (μ ^ (ij.2.val + 1)) ^ α ij =
            ∏ ij ∈ Finset.univ.erase k, (μ ^ (ij.2.val + 1)) ^ α' ij := by
          refine Finset.prod_congr rfl fun ij hij => ?_
          have hjk : ij ≠ k := (Finset.mem_erase.mp hij).1
          simp [α', Finsupp.tsub_apply, hjk.symm]
        rw [hrest]
        simp only [α', Finsupp.tsub_apply, Finsupp.single_apply, ↓reduceIte]
        rw [← mul_assoc, ← pow_succ']
        congr 2; omega
      rw [hprod_eq, Polynomial.C_mul]; ring
    · simp

private lemma jointRotPoly_eq_zero_iff {K r : ℕ} {μ : ℂ} (hμ : μ ≠ 0)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) :
    jointRotPoly K r μ P = 0 ↔ P = 0 := by
  constructor
  · intro h0
    apply MvPolynomial.ext
    intro α
    have hα := congrArg (fun Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) => Q.coeff α) h0
    change (jointRotPoly K r μ P).coeff α = 0 at hα
    rw [jointRotPoly_coeff] at hα
    have hprod_ne : Polynomial.C (∏ ij ∈ α.support, (μ ^ (ij.2.val + 1)) ^ α ij) ≠ 0 :=
      Polynomial.C_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (pow_ne_zero _ hμ))
    have hcomp : (P.coeff α).comp (Polynomial.C μ⁻¹ * Polynomial.X) = 0 :=
      (mul_eq_zero.mp hα).resolve_left hprod_ne
    have hcomp2 := congrArg (fun q : Polynomial ℂ => q.comp (Polynomial.C μ * Polynomial.X)) hcomp
    rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
      ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hμ, Polynomial.C_1, one_mul,
      Polynomial.comp_X, Polynomial.zero_comp] at hcomp2
    exact hcomp2
  · rintro rfl; simp

private lemma maxUDegJ_jointRotPoly_le {K r : ℕ} (μ : ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) :
    maxUDegJ (jointRotPoly K r μ P) ≤ maxUDegJ P := by
  refine Finset.sup_le fun α _ => ?_
  rw [jointRotPoly_coeff]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_comp_le.trans ?_
  have hdeg1 : (Polynomial.C μ⁻¹ * Polynomial.X).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  exact (Nat.mul_le_mul_left _ hdeg1).trans (by simp [natDegree_le_maxUDegJ P α])

private lemma jointFormalEvalPoly_rot_eq_zero {K r : ℕ} {φ : Fin K → ℂ → ℂ}
    (hφ : ∀ i, AnalyticAt ℂ (φ i) 0) {μ : ℂ} (hμ : μ ≠ 0)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hP : jointFormalEvalPoly (fun i => formalSeries (φ i)) P = 0) :
    jointFormalEvalPoly (fun i => formalSeries (fun z => φ i (μ * z))) (jointRotPoly K r μ P) = 0 := by
  let N := maxUDegJ P
  have hNP : ∀ α, (P.coeff α).natDegree ≤ N := natDegree_le_maxUDegJ P
  have hNrot : ∀ α, ((jointRotPoly K r μ P).coeff α).natDegree ≤ N := fun α =>
    (natDegree_le_maxUDegJ (jointRotPoly K r μ P) α).trans (maxUDegJ_jointRotPoly_le μ P)
  rw [← jointFormalEvalW_eq_zero_iff_poly _ _ hNP] at hP
  rw [← jointFormalEvalW_eq_zero_iff_poly _ _ hNrot]
  have hid : PowerSeries.C (μ ^ N) *
        jointFormalEvalW (fun i => formalSeries (fun z => φ i (μ * z)))
          (revMvPolyJ N (jointRotPoly K r μ P)) =
      scaleSubstJ μ (jointFormalEvalW (fun i => formalSeries (φ i)) (revMvPolyJ N P)) := by
    have hext_sum : ∀ Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ),
        jointFormalEvalW (fun i => formalSeries (fun z => φ i (μ * z))) (revMvPolyJ N Q) =
          ∑ α ∈ Q.support, ((revPolyJ N (Q.coeff α) : Polynomial ℂ) : PowerSeries ℂ) *
            ∏ ij ∈ α.support, (d_u^[ij.2.val] (formalSeries (fun z => φ ij.1 (μ * z)))) ^ α ij := by
      intro Q; unfold jointFormalEvalW revMvPolyJ
      rw [MvPolynomial.eval₂_sum]
      refine Finset.sum_congr rfl fun α _ => by rw [MvPolynomial.eval₂_monomial]; rfl
    have hext_sum' : jointFormalEvalW (fun i => formalSeries (φ i)) (revMvPolyJ N P) =
        ∑ α ∈ P.support, ((revPolyJ N (P.coeff α) : Polynomial ℂ) : PowerSeries ℂ) *
          ∏ ij ∈ α.support, (d_u^[ij.2.val] (formalSeries (φ ij.1))) ^ α ij := by
      unfold jointFormalEvalW revMvPolyJ
      rw [MvPolynomial.eval₂_sum]
      refine Finset.sum_congr rfl fun α _ => by rw [MvPolynomial.eval₂_monomial]; rfl
    have hrot_term : ∀ α : Fin K × Fin (r + 1) →₀ ℕ,
        PowerSeries.C (μ ^ N) *
          (((revPolyJ N ((jointRotPoly K r μ P).coeff α) : Polynomial ℂ) : PowerSeries ℂ) *
            ∏ ij ∈ α.support, (d_u^[ij.2.val] (formalSeries (fun z => φ ij.1 (μ * z)))) ^ α ij) =
        scaleSubstJ μ
          (((revPolyJ N (P.coeff α) : Polynomial ℂ) : PowerSeries ℂ) *
            ∏ ij ∈ α.support, (d_u^[ij.2.val] (formalSeries (φ ij.1))) ^ α ij) := by
      intro α
      rw [jointRotPoly_coeff]
      have hrev_C : ∀ (c : ℂ) (q : Polynomial ℂ),
          revPolyJ N (Polynomial.C c * q) = Polynomial.C c * revPolyJ N q := by
        intro c q
        simp only [revPolyJ, Polynomial.coeff_C_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by rw [Polynomial.C_mul]; ring
      rw [hrev_C, Polynomial.coe_mul, Polynomial.coe_C]
      have hpow_rot : ∏ ij ∈ α.support,
            (d_u^[ij.2.val] (formalSeries (fun z => φ ij.1 (μ * z)))) ^ α ij =
          PowerSeries.C (∏ ij ∈ α.support, (μ⁻¹ ^ (ij.2.val + 1)) ^ α ij) *
            scaleSubstJ μ (∏ ij ∈ α.support, (d_u^[ij.2.val] (formalSeries (φ ij.1))) ^ α ij) := by
        have hterm : ∀ ij ∈ α.support,
            (d_u^[ij.2.val] (formalSeries (fun z => φ ij.1 (μ * z)))) ^ α ij =
              PowerSeries.C ((μ⁻¹ ^ (ij.2.val + 1)) ^ α ij) *
                (scaleSubstJ μ (d_u^[ij.2.val] (formalSeries (φ ij.1)))) ^ α ij := by
          intro ij _
          rw [d_u_iter_formalSeries_rotJ (hφ ij.1) hμ ij.2.val, mul_pow, ← map_pow]
        rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, ← map_prod]
        congr 1
        rw [map_prod]
        refine Finset.prod_congr rfl fun ij _ => (map_pow _ _ _).symm
      rw [hpow_rot, map_mul (scaleSubstJ μ)]
      have hC_cancel : (∏ ij ∈ α.support, (μ ^ (ij.2.val + 1)) ^ α ij) *
          (∏ ij ∈ α.support, (μ⁻¹ ^ (ij.2.val + 1)) ^ α ij) = 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun ij _ => ?_
        rw [← mul_pow, ← mul_pow, mul_inv_cancel₀ hμ, one_pow, one_pow]
      calc PowerSeries.C (μ ^ N) *
            ((PowerSeries.C (∏ ij ∈ α.support, (μ ^ (ij.2.val + 1)) ^ α ij) *
                ((revPolyJ N ((P.coeff α).comp (Polynomial.C μ⁻¹ * Polynomial.X)) : Polynomial ℂ) : PowerSeries ℂ)) *
              (PowerSeries.C (∏ ij ∈ α.support, (μ⁻¹ ^ (ij.2.val + 1)) ^ α ij) *
                scaleSubstJ μ (∏ ij ∈ α.support, (d_u^[ij.2.val] (formalSeries (φ ij.1))) ^ α ij)))
          = PowerSeries.C ((∏ ij ∈ α.support, (μ ^ (ij.2.val + 1)) ^ α ij) *
              (∏ ij ∈ α.support, (μ⁻¹ ^ (ij.2.val + 1)) ^ α ij)) *
              ((PowerSeries.C (μ ^ N) *
                ((revPolyJ N ((P.coeff α).comp (Polynomial.C μ⁻¹ * Polynomial.X)) : Polynomial ℂ) : PowerSeries ℂ)) *
                scaleSubstJ μ (∏ ij ∈ α.support, (d_u^[ij.2.val] (formalSeries (φ ij.1))) ^ α ij)) := by
            rw [map_mul]; ring
        _ = scaleSubstJ μ ((revPolyJ N (P.coeff α) : Polynomial ℂ) : PowerSeries ℂ) *
              scaleSubstJ μ (∏ ij ∈ α.support, (d_u^[ij.2.val] (formalSeries (φ ij.1))) ^ α ij) := by
            rw [hC_cancel, map_one, one_mul, scaleSubstJ_revPoly μ hμ (P.coeff α)]
    have hsupp_sub : (jointRotPoly K r μ P).support ⊆ P.support := by
      intro α hα
      rw [MvPolynomial.mem_support_iff] at hα ⊢
      intro h0; apply hα
      rw [jointRotPoly_coeff, h0, Polynomial.zero_comp, mul_zero]
    rw [hext_sum, hext_sum', map_sum, Finset.mul_sum]
    rw [Finset.sum_subset hsupp_sub]
    · exact Finset.sum_congr rfl fun α _ => hrot_term α
    · intro α _ hnot
      rw [MvPolynomial.notMem_support_iff.mp hnot]
      simp [revPolyJ]
  rw [hP, map_zero] at hid
  have hC_ne : PowerSeries.C (μ ^ N) ≠ 0 := by
    intro h0
    have h0' := congrArg (PowerSeries.coeff 0) h0
    simp [pow_ne_zero N hμ] at h0'
  exact (mul_eq_zero.mp hid).resolve_left hC_ne

/-! #### 1C. Algebraic Core: Componentwise Frequency Operator, Shift-Invariance, Taylor Bound, & Vandermonde -/

/-- Componentwise constant-coefficient frequency derivation on `MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)`:
`D_joint i ω P = ∑ j, C ((-ω)^j) • ∂_{(i, j)} P`. -/
private def D_joint (K r : ℕ) (i : Fin K) (ω : ℂ) :
    MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) →ₗ[Polynomial ℂ]
      MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ) where
  toFun P := ∑ j : Fin (r + 1), (Polynomial.C ((-ω) ^ j.val)) • MvPolynomial.pderiv (i, j) P
  map_add' P Q := by simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => by rw [(MvPolynomial.pderiv (i, j)).map_smul, smul_comm]

private lemma degree_pderiv_poly_ltJ {ι : Type*} (i : ι) (P : MvPolynomial ι (Polynomial ℂ))
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

private lemma totalDegree_poly_sum_ltJ {ι σ : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial σ (Polynomial ℂ)) {d : ℕ} (hd : 0 < d)
    (hf : ∀ i ∈ s, (f i).totalDegree < d) :
    (∑ i ∈ s, f i).totalDegree < d := by
  induction s using Finset.induction_on with
  | empty => simpa using hd
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (MvPolynomial.totalDegree_add _ _).trans_lt
      (max_lt (hf i (Finset.mem_insert_self i s))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))))

private lemma degree_D_joint_lt {K r : ℕ} (i : Fin K) (ω : ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) (h : 0 < P.totalDegree) :
    (D_joint K r i ω P).totalDegree < P.totalDegree := by
  unfold D_joint
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine totalDegree_poly_sum_ltJ Finset.univ _ h fun j _ => ?_
  exact (MvPolynomial.totalDegree_smul_le _ _).trans_lt (degree_pderiv_poly_ltJ (i, j) P h)

private lemma jointEvalU_D_joint {K r : ℕ} (i : Fin K) (ω u : ℂ)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) :
    jointEvalU (D_joint K r i ω P) u =
      ∑ j : Fin (r + 1), ((-ω) ^ j.val) • MvPolynomial.pderiv (i, j) (jointEvalU P u) := by
  unfold D_joint jointEvalU
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, Polynomial.coe_evalRingHom,
    Polynomial.eval_C, MvPolynomial.pderiv_map, MvPolynomial.smul_eq_C_mul]

private def lineSliceAny {ι : Type*} (x v : ι → ℂ) :
    MvPolynomial ι ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval fun j => Polynomial.C (x j) + Polynomial.C (v j) * Polynomial.X

private lemma lineSliceAny_eval {ι : Type*} (x v : ι → ℂ) (P : MvPolynomial ι ℂ) (a : ℂ) :
    (lineSliceAny x v P).eval a = MvPolynomial.eval (fun j => x j + a * v j) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [lineSliceAny]
  | add A B hA hB => simp only [map_add, Polynomial.eval_add, hA, hB]
  | mul_X A k hA =>
    rw [map_mul, Polynomial.eval_mul, hA]
    simp only [lineSliceAny, MvPolynomial.aeval_X, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, map_mul, MvPolynomial.eval_X]
    ring

private lemma derivative_lineSliceAny {ι : Type*} [Fintype ι] [DecidableEq ι] (x v : ι → ℂ)
    (P : MvPolynomial ι ℂ) :
    Polynomial.derivative (lineSliceAny x v P) =
      ∑ j : ι, Polynomial.C (v j) * lineSliceAny x v (MvPolynomial.pderiv j P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [lineSliceAny]
  | add A B hA hB =>
    simp only [map_add, hA, hB, mul_add, Finset.sum_add_distrib]
  | mul_X A k hA =>
    simp only [map_mul, Polynomial.derivative_mul, hA, MvPolynomial.pderiv_mul,
      MvPolynomial.pderiv_X, Pi.single_apply, map_add, mul_add, Finset.sum_add_distrib]
    have hdk : Polynomial.derivative (lineSliceAny x v (MvPolynomial.X k)) = Polynomial.C (v k) := by
      simp [lineSliceAny]
    rw [hdk]
    have h1 : (∑ j : ι, Polynomial.C (v j) * lineSliceAny x v (MvPolynomial.pderiv j A)) *
          lineSliceAny x v (MvPolynomial.X k) =
        ∑ j : ι, Polynomial.C (v j) *
          (lineSliceAny x v (MvPolynomial.pderiv j A) * lineSliceAny x v (MvPolynomial.X k)) := by
      rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ j : ι, Polynomial.C (v j) *
          (lineSliceAny x v A * lineSliceAny x v (if k = j then 1 else 0)) =
        lineSliceAny x v A * Polynomial.C (v k) := by
      trans ∑ j : ι, if k = j then lineSliceAny x v A * Polynomial.C (v k) else 0
      · refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hkj
        · subst hkj; simp [mul_comm]
        · simp
      · simp
    rw [h1, h2]

private lemma shift_invariant_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → ℂ) (P : MvPolynomial ι ℂ)
    (hP : ∑ j : ι, v j • MvPolynomial.pderiv j P = 0) (x : ι → ℂ) (a : ℂ) :
    MvPolynomial.eval (fun j => x j + a * v j) P = MvPolynomial.eval x P := by
  have hd : Polynomial.derivative (lineSliceAny x v P) = 0 := by
    rw [derivative_lineSliceAny]
    have h0 : lineSliceAny x v (∑ j : ι, v j • MvPolynomial.pderiv j P) = 0 := by
      rw [hP, map_zero]
    rw [map_sum] at h0
    refine (Eq.trans ?_ h0)
    refine Finset.sum_congr rfl fun j _ => by
      rw [MvPolynomial.smul_eq_C_mul, map_mul]; simp [lineSliceAny]
  have hc := Polynomial.eq_C_of_derivative_eq_zero hd
  have he : (lineSliceAny x v P).eval a = (lineSliceAny x v P).eval 0 := by
    rw [hc, Polynomial.eval_C, Polynomial.eval_C]
  rw [lineSliceAny_eval, lineSliceAny_eval] at he
  simpa using he

private lemma eval_shift_taylor_bound_any {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℂ) {M : ℝ} (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x v : ι → ℂ) (a : ℂ),
      (∀ j, ‖x j‖ ≤ M) → (∀ j, ‖v j‖ ≤ M) → ‖a‖ ≤ 1 →
      ‖MvPolynomial.eval (fun j => x j + a * v j) P - MvPolynomial.eval x P -
        a * ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j P) * v j‖ ≤
        C * ‖a‖ ^ 2 := by
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
  | C c => exact ⟨0, le_rfl, fun x v a _ _ _ => by simp⟩
  | add A B hA hB =>
    obtain ⟨CA, hCA, hbA⟩ := hA
    obtain ⟨CB, hCB, hbB⟩ := hB
    refine ⟨CA + CB, add_nonneg hCA hCB, fun x v a hx hv ha => ?_⟩
    have hsplit : MvPolynomial.eval (fun j => x j + a * v j) (A + B) - MvPolynomial.eval x (A + B) -
        a * ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j (A + B)) * v j =
        (MvPolynomial.eval (fun j => x j + a * v j) A - MvPolynomial.eval x A -
          a * ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j A) * v j) +
        (MvPolynomial.eval (fun j => x j + a * v j) B - MvPolynomial.eval x B -
          a * ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j B) * v j) := by
      simp only [map_add, add_mul, Finset.sum_add_distrib]; ring
    rw [hsplit, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hbA x v a hx hv ha) (hbB x v a hx hv ha))
  | mul_X A k hA =>
    obtain ⟨CA, hCA, hbA⟩ := hA
    obtain ⟨BA, hBA, hAbdd⟩ := eval_bdd A
    have hderivBdd : ∃ BD : ℝ, 0 ≤ BD ∧ ∀ x v : ι → ℂ,
        (∀ j, ‖x j‖ ≤ M) → (∀ j, ‖v j‖ ≤ M) →
        ‖∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j A) * v j‖ ≤ BD := by
      choose B hB hBbdd using fun j => eval_bdd (MvPolynomial.pderiv j A)
      refine ⟨∑ j : ι, B j * M, Finset.sum_nonneg fun j _ => mul_nonneg (hB j) hM,
        fun x v hx hv => ?_⟩
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul]
      exact mul_le_mul (hBbdd j x hx) (hv j) (norm_nonneg _) (hB j)
    obtain ⟨BD, hBD, hDbdd⟩ := hderivBdd
    refine ⟨CA * (2 * M) + BD * M, by positivity, fun x v a hx hv ha => ?_⟩
    let S := ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j A) * v j
    let RA := MvPolynomial.eval (fun j => x j + a * v j) A - MvPolynomial.eval x A - a * S
    have hsum : ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j (A * MvPolynomial.X k)) * v j =
        S * x k + MvPolynomial.eval x A * v k := by
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply, map_add, map_mul,
        MvPolynomial.eval_X, add_mul, Finset.sum_add_distrib]
      have h1 : ∑ j : ι, MvPolynomial.eval x (MvPolynomial.pderiv j A) * x k * v j = S * x k := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring
      have h2 : ∑ j : ι, MvPolynomial.eval x A *
          MvPolynomial.eval x (if k = j then 1 else 0) * v j =
          MvPolynomial.eval x A * v k := by
        trans ∑ j : ι, if k = j then MvPolynomial.eval x A * v k else 0
        · refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs with hkj
          · subst hkj; simp
          · simp
        · simp
      rw [h1, h2]
    have hid : MvPolynomial.eval (fun j => x j + a * v j) (A * MvPolynomial.X k) -
        MvPolynomial.eval x (A * MvPolynomial.X k) - a * (S * x k + MvPolynomial.eval x A * v k) =
        RA * (x k + a * v k) + a ^ 2 * (S * v k) := by
      simp only [map_mul, MvPolynomial.eval_X, RA]; ring
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

private def coeffUJ {ι : Type*} (k : ℕ) (P : MvPolynomial ι (Polynomial ℂ)) :
    MvPolynomial ι ℂ :=
  ∑ α ∈ P.support, MvPolynomial.monomial α ((P.coeff α).coeff k)

private lemma coeffUJ_coeff {ι : Type*} (k : ℕ) (P : MvPolynomial ι (Polynomial ℂ))
    (α : ι →₀ ℕ) : (coeffUJ k P).coeff α = (P.coeff α).coeff k := by
  classical
  dsimp only [coeffUJ]
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, Polynomial.coeff_zero, Finset.sum_eq_zero]
    intro β hβ
    have hne : β ≠ α := fun h => hα (h ▸ hβ)
    simp [hne]

private lemma coeffUJ_pderiv {ι : Type*} (k : ℕ) (j : ι)
    (P : MvPolynomial ι (Polynomial ℂ)) :
    coeffUJ k (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (coeffUJ k P) := by
  ext α
  rw [coeffUJ_coeff, MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv, coeffUJ_coeff]
  have hcast : (((α j : ℕ) : Polynomial ℂ) + 1) = Polynomial.C (((α j : ℕ) : ℂ) + 1) := by
    simp [map_natCast]
  rw [hcast, mul_comm, Polynomial.coeff_C_mul, mul_comm]

private lemma coeffUJ_add {ι : Type*} (k : ℕ) (A B : MvPolynomial ι (Polynomial ℂ)) :
    coeffUJ k (A + B) = coeffUJ k A + coeffUJ k B := by
  ext α; simp [coeffUJ_coeff]

private lemma coeffUJ_C_smul {ι : Type*} (k : ℕ) (c : ℂ) (P : MvPolynomial ι (Polynomial ℂ)) :
    coeffUJ k (Polynomial.C c • P) = c • coeffUJ k P := by
  ext α
  rw [coeffUJ_coeff, MvPolynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_C_mul,
    MvPolynomial.coeff_smul, smul_eq_mul, coeffUJ_coeff]

private lemma coeffUJ_sum {ι σ : Type*} (s : Finset σ) (k : ℕ)
    (f : σ → MvPolynomial ι (Polynomial ℂ)) :
    coeffUJ k (∑ i ∈ s, f i) = ∑ i ∈ s, coeffUJ k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext α; simp [coeffUJ_coeff]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, coeffUJ_add, ih, Finset.sum_insert hi]

private lemma jointEvalU_eq_sum_coeffUJ {K r : ℕ}
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) (u : ℂ) :
    jointEvalU P u = ∑ k ∈ Finset.range (maxUDegJ P + 1), u ^ k • coeffUJ k P := by
  ext α
  rw [jointEvalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, coeffUJ_coeff, smul_eq_mul]
  have hdeg : (P.coeff α).natDegree < maxUDegJ P + 1 := Nat.lt_succ_of_le (natDegree_le_maxUDegJ P α)
  have hsum := Polynomial.as_sum_range_C_mul_X_pow' (P.coeff α) hdeg
  conv_lhs => rw [hsum]
  change Polynomial.evalRingHom u _ = _
  simp only [map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    Polynomial.eval_X]
  refine Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Componentwise Vandermonde Contradiction**:
If `Pmin : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)` has `0 < Pmin.totalDegree` and for
every component `i : Fin K` there are `r + 1` distinct frequencies `ω i 0, ..., ω i r` annihilating
`D_joint K r i (ω i m) Pmin = 0`, then `False`. -/
private lemma joint_vandermonde_contradiction {K r : ℕ}
    (Pmin : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hdeg : 0 < Pmin.totalDegree)
    (ω : Fin K → ℕ → ℝ) (hmono : ∀ i, StrictMono (ω i))
    (hD : ∀ (i : Fin K) (m : ℕ), m < r + 1 → D_joint K r i (ω i m : ℂ) Pmin = 0) :
    False := by
  classical
  let S_nc : Finset (Fin K × Fin (r + 1) →₀ ℕ) := Pmin.support.filter (fun α => α ≠ 0)
  have hS_nc : S_nc.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have h0 : Pmin.totalDegree = 0 := by
      rw [MvPolynomial.totalDegree_eq]
      refine Nat.eq_zero_of_le_zero (Finset.sup_le fun α hα => ?_)
      have hα0 : α = 0 := by
        by_contra hne
        have hmem : α ∈ S_nc := Finset.mem_filter.mpr ⟨hα, hne⟩
        rw [hemp] at hmem; exact Finset.notMem_empty α hmem
      subst hα0; simp
    omega
  let d_max : ℕ := S_nc.sup fun α => (Pmin.coeff α).natDegree
  obtain ⟨α₀, hα₀_mem, hα₀_eq⟩ := Finset.exists_mem_eq_sup S_nc hS_nc (fun α => (Pmin.coeff α).natDegree)
  have hα₀_supp : α₀ ∈ Pmin.support := (Finset.mem_filter.mp hα₀_mem).1
  have hα₀_ne : α₀ ≠ 0 := (Finset.mem_filter.mp hα₀_mem).2
  have hα₀_top : (coeffUJ d_max Pmin).coeff α₀ ≠ 0 := by
    rw [coeffUJ_coeff]
    dsimp only [d_max]
    rw [hα₀_eq]
    exact Polynomial.leadingCoeff_ne_zero.mpr (MvPolynomial.mem_support_iff.mp hα₀_supp)
  let P_top : MvPolynomial (Fin K × Fin (r + 1)) ℂ := coeffUJ d_max Pmin
  have hP_top_pderiv : ∀ ij : Fin K × Fin (r + 1), MvPolynomial.pderiv ij P_top = 0 := by
    rintro ⟨i, j⟩
    let v : Fin (r + 1) → ℂ := fun m => -(ω i m.val : ℂ)
    let V : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.vandermonde v
    have hdet : V.det ≠ 0 := by
      rw [Matrix.det_vandermonde]
      refine Finset.prod_ne_zero_iff.mpr fun a _ => Finset.prod_ne_zero_iff.mpr fun b hb => ?_
      have hab : a < b := Finset.mem_Ioi.mp hb
      have hlt : ω i a.val < ω i b.val := hmono i hab
      intro h0
      have heq : (ω i a.val : ℂ) = (ω i b.val : ℂ) := by
        dsimp only [v] at h0; linear_combination h0
      have hreal : ω i a.val = ω i b.val := Complex.ofReal_injective heq
      linarith
    have hmul_zero : ∀ α : Fin K × Fin (r + 1) →₀ ℕ,
        V.mulVec (fun k : Fin (r + 1) => (MvPolynomial.pderiv (i, k) P_top).coeff α) = 0 := by
      intro α
      ext m
      simp only [Matrix.mulVec, dotProduct, V, Matrix.vandermonde_apply, Pi.zero_apply]
      have hDm := hD i m.val m.isLt
      have hc := congrArg (fun Q => (coeffUJ d_max Q).coeff α) hDm
      change (coeffUJ d_max (D_joint K r i (ω i m.val : ℂ) Pmin)).coeff α =
        (coeffUJ d_max 0).coeff α at hc
      have hc0 : (coeffUJ d_max (0 : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))).coeff α = 0 := by
        simp [coeffUJ_coeff]
      rw [hc0] at hc
      unfold D_joint at hc
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at hc
      rw [coeffUJ_sum, MvPolynomial.coeff_sum] at hc
      rw [← hc]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeffUJ_C_smul, coeffUJ_pderiv, MvPolynomial.coeff_smul, smul_eq_mul]
    ext α
    have hvec : (fun k : Fin (r + 1) => (MvPolynomial.pderiv (i, k) P_top).coeff α) = 0 := by
      have h1 := congrArg (V⁻¹.mulVec) (hmul_zero α)
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
        Matrix.one_mulVec, Matrix.mulVec_zero] at h1
      exact h1
    simpa using congrFun hvec j
  have hconst := all_partials_zero P_top hP_top_pderiv
  have hzero : P_top.coeff α₀ = 0 := by
    rw [hconst, MvPolynomial.coeff_C, ite_eq_right_iff.mpr (fun h => absurd h hα₀_ne.symm)]
  exact hα₀_top hzero

/-! #### 1D. Joint Borellized Expressions (`JointBorelExpr`) and Lateral Transfer -/

private def aPhiJ (φ : ℂ → ℂ) : Minor := ⟨0, φ⟩

private lemma aPhiJ_toSeries (φ : ℂ → ℂ) : (aPhiJ φ).toSeries = formalSeries φ := by
  ext n; cases n <;> simp [aPhiJ, Minor.toSeries, formalSeries]

private def polyMinorJ (q : Polynomial ℂ) : Minor :=
  ⟨q.coeff 0, fun z : ℂ =>
    ∑ m ∈ Finset.range q.natDegree, (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m⟩

private lemma polyMinorJ_toSeries (q : Polynomial ℂ) :
    (polyMinorJ q).toSeries = (q : PowerSeries ℂ) := by
  ext n
  cases n with
  | zero => simp [polyMinorJ, Minor.toSeries]
  | succ k =>
    simp only [polyMinorJ, Minor.toSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe]
    have hcd : ∀ m ∈ Finset.range q.natDegree,
        ContDiffAt ℂ k (fun z : ℂ => (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m) 0 :=
      fun _ _ => (analyticAt_const.mul (analyticAt_id.pow _)).contDiffAt
    rw [iteratedDeriv_fun_sum hcd]
    have hterm : ∀ m ∈ Finset.range q.natDegree,
        iteratedDeriv k (fun z : ℂ => (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m) 0 =
          if m = k then q.coeff (k + 1) else 0 := by
      intro m _
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_pow_zero]
      by_cases hkm : m = k
      · subst hkm; simp only [↓reduceIte]
        have hfac : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        field_simp [hfac]
      · simp [hkm, Ne.symm hkm]
    rw [Finset.sum_congr rfl hterm]
    by_cases hk : k < q.natDegree
    · rw [Finset.sum_ite_eq']; simp [Finset.mem_range.mpr hk]
    · have hnot : k ∉ Finset.range q.natDegree := by simpa [Finset.mem_range] using hk
      rw [Finset.sum_ite_eq', ite_eq_right_iff.mpr fun hmem => absurd hmem hnot]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

private lemma polyMinorJ_good (q : Polynomial ℂ) (U : Set ℂ) (d : ℂ) :
    (polyMinorJ q).Good U d := by
  refine ⟨?_, ?_⟩
  · intro z _; dsimp only [polyMinorJ]
    exact Finset.analyticAt_fun_sum _ fun m _ => by fun_prop
  · refine ⟨∑ m ∈ Finset.range q.natDegree, ‖d‖ ^ (m + 1) * ‖q.coeff (m + 1)‖, 1,
      Finset.sum_nonneg (fun _ _ => by positivity), zero_le_one, fun v hv => ?_⟩
    rw [Minor.pull]; dsimp only [polyMinorJ]
    rw [Finset.mul_sum, one_mul, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [mul_pow, norm_mul, norm_mul, norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_natCast,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv]
    have hpow : v ^ m / (m.factorial : ℝ) ≤ Real.exp v := Real.pow_div_factorial_le_exp v hv m
    calc ‖d‖ * (‖q.coeff (m + 1)‖ / (m.factorial : ℝ) * (‖d‖ ^ m * v ^ m))
        = (‖d‖ ^ (m + 1) * ‖q.coeff (m + 1)‖) * (v ^ m / (m.factorial : ℝ)) := by
          rw [pow_succ']; ring
      _ ≤ (‖d‖ ^ (m + 1) * ‖q.coeff (m + 1)‖) * Real.exp v :=
          mul_le_mul_of_nonneg_left hpow (by positivity)

private lemma polyMinorJ_value (q : Polynomial ℂ) {d p : ℂ} (hp : 0 < (p * d).re) :
    (polyMinorJ q).value d p = q.eval p⁻¹ := by
  have hpd0 : p * d ≠ 0 := fun h0 => by simp [h0] at hp
  have hp0 : p ≠ 0 := left_ne_zero_of_mul hpd0
  have hd0 : d ≠ 0 := right_ne_zero_of_mul hpd0
  unfold Minor.value polyMinorJ complexLaplace; dsimp only
  have heq : (fun v : ℝ => damped (p * d)
      (Minor.pull d fun z => ∑ m ∈ Finset.range q.natDegree,
        (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m) v) =
      fun v : ℝ => ∑ m ∈ Finset.range q.natDegree,
        (d ^ (m + 1) * (q.coeff (m + 1) / (m.factorial : ℂ))) *
          (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m) := by
    funext v; simp only [damped, Minor.pull, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => by rw [mul_pow, pow_succ']; ring
  rw [heq]
  have hi_term : ∀ m ∈ Finset.range q.natDegree,
      IntegrableOn (fun v : ℝ => (d ^ (m + 1) * (q.coeff (m + 1) / (m.factorial : ℂ))) *
        (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m)) (Ioi 0) := by
    intro m _
    refine Integrable.const_mul ?_ _
    refine ((integrableOn_exp_mul_Ioi (show -((p * d).re / 2) < 0 by linarith) 0).const_mul
      ((m.factorial : ℝ) / ((p * d).re / 2) ^ m)).mono'
      ((by fun_prop : Continuous (fun v : ℝ =>
        Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m)).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    change 0 < v at hv
    rw [norm_mul, Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.le]
    have hre2 : (-(p * d) * (v : ℂ)).re = -(p * d).re * v := by simp [Complex.mul_re]; ring
    rw [hre2]
    have hpow := Real.pow_div_factorial_le_exp ((p * d).re / 2 * v) (by positivity) m
    have h1 : 0 < ((p * d).re / 2) ^ m := pow_pos (by positivity) m
    have h2 : 0 < (m.factorial : ℝ) := by positivity
    rw [mul_pow, div_le_iff₀ h2] at hpow
    have hvm : v ^ m ≤ ((m.factorial : ℝ) / ((p * d).re / 2) ^ m) * Real.exp ((p * d).re / 2 * v) := by
      calc v ^ m ≤ (Real.exp ((p * d).re / 2 * v) * m.factorial) / ((p * d).re / 2) ^ m :=
            (le_div_iff₀ h1).mpr (by linarith)
        _ = _ := by ring
    calc Real.exp (-(p * d).re * v) * v ^ m
        ≤ Real.exp (-(p * d).re * v) *
            (((m.factorial : ℝ) / ((p * d).re / 2) ^ m) * Real.exp ((p * d).re / 2 * v)) :=
          mul_le_mul_of_nonneg_left hvm (Real.exp_pos _).le
      _ = ((m.factorial : ℝ) / ((p * d).re / 2) ^ m) * Real.exp (-((p * d).re / 2) * v) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  rw [MeasureTheory.integral_finsetSum _ hi_term]
  have hsum_eq : ∑ m ∈ Finset.range q.natDegree,
      ∫ v in Ioi (0 : ℝ), (d ^ (m + 1) * (q.coeff (m + 1) / (m.factorial : ℂ))) *
        (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m) =
      ∑ m ∈ Finset.range q.natDegree, q.coeff (m + 1) * p⁻¹ ^ (m + 1) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [integral_const_mul, Minor.complexLaplace_monomial m hp, mul_pow, inv_pow]
    have hm_ne : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    field_simp [hm_ne, hd0, hp0]
  rw [hsum_eq, Polynomial.eval_eq_sum_range, Finset.sum_range_succ']
  simp only [pow_zero, mul_one]; ring

private inductive JointBorelExpr (K : ℕ) where
  | poly (q : Polynomial ℂ)
  | leaf (i : Fin K)
  | add (e f : JointBorelExpr K)
  | mul (e f : JointBorelExpr K)
  | jet (e : JointBorelExpr K)

namespace JointBorelExpr

private def residual {K : ℕ} (a : Fin K → Minor) : JointBorelExpr K → Minor
  | poly q => polyMinorJ q
  | leaf i => a i
  | add e f => (e.residual a).plus (f.residual a)
  | mul e f => (e.residual a).times (f.residual a)
  | jet e => (e.residual a).jet

private def eval {K : ℕ} (a : Fin K → Minor) (d : ℂ) : JointBorelExpr K → ℂ → ℂ
  | poly q => fun p => q.eval p⁻¹
  | leaf i => (a i).value d
  | add e f => fun p => e.eval a d p + f.eval a d p
  | mul e f => fun p => e.eval a d p * f.eval a d p
  | jet e => fun p => deriv (e.eval a d) p

private lemma represents {K : ℕ} (e : JointBorelExpr K) {U : Set ℂ} {d : ℂ} (hU : Domain U)
    (ray : ContainsRay U d) {a : Fin K → Minor} (ha : ∀ i, (a i).Good U d) :
    (e.residual a).Good U d ∧ e.eval a d =ᶠ[BorelStokesVandermonde.far d] (e.residual a).value d := by
  induction e with
  | poly q =>
    refine ⟨polyMinorJ_good q U d, ?_⟩
    filter_upwards [eventually_bound_far d 0] with p hp
    exact (polyMinorJ_value q hp).symm
  | leaf i => exact ⟨ha i, .rfl⟩
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

private lemma jetIter_eval_eq {K : ℕ} (a : Fin K → Minor) (d : ℂ) (i : Fin K) (j : ℕ) :
    (Nat.iterate jet j (leaf i)).eval a d =
      (Nat.iterate BorelExpr.jet j BorelExpr.leaf).eval (a i) d := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change (fun p => deriv ((Nat.iterate jet j (leaf i)).eval a d) p) =
      (fun p => deriv ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).eval (a i) d) p)
    rw [ih]

private lemma exists_of_mvPolynomial {K r : ℕ}
    (Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) :
    ∃ e : JointBorelExpr K,
      (∀ (U : Set ℂ) (d : ℂ) (a : Fin K → Minor), Domain U → ContainsRay U d →
        (∀ i, (a i).Good U d) →
        (e.residual a).toSeries = jointFormalEvalW (fun i => (a i).toSeries) Q) ∧
      (∀ (U : Set ℂ) (d : ℂ) (a : Fin K → Minor) (_hU : Domain U) (_ray : ContainsRay U d)
        (_ha : ∀ i, (a i).Good U d) (_hd : 0 < d.re),
        ∀ᶠ u : ℝ in atTop,
          e.eval a d (u : ℂ) =
            MvPolynomial.eval
              (fun ij : Fin K × Fin (r + 1) =>
                iteratedDeriv ij.2.val (fun t : ℝ => (a ij.1).value d (t : ℂ)) u)
              (jointEvalU Q (u : ℂ)⁻¹)) := by
  induction Q using MvPolynomial.induction_on with
  | C q =>
    refine ⟨poly q, ?_, ?_⟩
    · intro U d a _ _ _
      simp [residual, polyMinorJ_toSeries, jointFormalEvalW]
    · intro U d a _ _ _ _
      exact .of_forall fun u => by simp [eval, jointEvalU]
  | add Q₁ Q₂ h₁ h₂ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    obtain ⟨e₂, hs₂, he₂⟩ := h₂
    refine ⟨add e₁ e₂, ?_, ?_⟩
    · intro U d a hU ray ha
      have hg₁ := (e₁.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      have hg₂ := (e₂.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      rw [residual, Minor.toSeries_plus hg₁ hg₂, hs₁ U d a hU ray ha, hs₂ U d a hU ray ha]
      simp [jointFormalEvalW]
    · intro U d a hU ray ha hd
      filter_upwards [he₁ U d a hU ray ha hd, he₂ U d a hU ray ha hd] with u hu₁ hu₂
      simp [eval, jointEvalU, hu₁, hu₂]
  | mul_X Q₁ ij h₁ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    let ej : JointBorelExpr K := Nat.iterate jet ij.2.val (leaf ij.1)
    refine ⟨mul e₁ ej, ?_, ?_⟩
    · intro U d a hU ray ha
      have h0 : (0 : ℂ) ∈ U := by simpa using ray 0 le_rfl
      have hg₁ := (e₁.represents hU ray ha).1.1 0 h0
      have hgj := (ej.represents hU ray ha).1.1 0 h0
      rw [residual, Minor.toSeries_times hg₁ hgj, hs₁ U d a hU ray ha]
      have hj_series : ∀ k : ℕ, ((Nat.iterate jet k (leaf ij.1)).residual a).toSeries =
          d_u^[k] (a ij.1).toSeries := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          have hgk := ((Nat.iterate jet k (leaf ij.1)).represents hU ray ha).1.1 0 h0
          rw [Function.iterate_succ_apply' jet k (leaf ij.1),
            Function.iterate_succ_apply' d_u k (a ij.1).toSeries]
          exact (Minor.toSeries_jet hgk).trans (congrArg d_u ih)
      rw [hj_series ij.2.val]
      simp [jointFormalEvalW]
    · intro U d a hU ray ha hd
      have hjet_eq := (BorelExpr.jetIter_eval_eq_iteratedDeriv (a ij.1) hU ray (ha ij.1) hd ij.2.val).1
      filter_upwards [he₁ U d a hU ray ha hd, hjet_eq] with u hu₁ huj
      have heval_eq : ej.eval a d (u : ℂ) =
          (Nat.iterate BorelExpr.jet ij.2.val BorelExpr.leaf).eval (a ij.1) d (u : ℂ) :=
        congrFun (jetIter_eval_eq a d ij.1 ij.2.val) (u : ℂ)
      simp only [eval, jointEvalU, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X] at hu₁ ⊢
      rw [heval_eq, hu₁, huj]

end JointBorelExpr

/-! #### 1E. Wedge Geometry, Single-Component Simple-Pole Stokes Jump at Arbitrary Cut `R`, & Joint Descent -/

private def dPlusJ (θ : ℝ) : ℂ := Complex.exp (I * (θ : ℂ))
private def dMinusJ (θ : ℝ) : ℂ := Complex.exp (-I * (θ : ℂ))

private lemma dPlusJ_eq (θ : ℝ) : dPlusJ θ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
  unfold dPlusJ; rw [mul_comm I, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma dMinusJ_eq (θ : ℝ) : dMinusJ θ = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
  unfold dMinusJ
  rw [show -I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast; ring

private lemma norm_dPlusJ (θ : ℝ) : ‖dPlusJ θ‖ = 1 := by
  unfold dPlusJ; rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ

private lemma norm_dMinusJ (θ : ℝ) : ‖dMinusJ θ‖ = 1 := by
  unfold dMinusJ; rw [show -I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (-θ)

private lemma dPlusJ_re (θ : ℝ) : (dPlusJ θ).re = Real.cos θ := by
  unfold dPlusJ; rw [mul_comm]; exact Complex.exp_ofReal_mul_I_re θ

private lemma dPlusJ_im (θ : ℝ) : (dPlusJ θ).im = Real.sin θ := by
  unfold dPlusJ; rw [mul_comm]; exact Complex.exp_ofReal_mul_I_im θ

private lemma dMinusJ_re (θ : ℝ) : (dMinusJ θ).re = Real.cos θ := by
  unfold dMinusJ
  rw [show -I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

private lemma dMinusJ_im (θ : ℝ) : (dMinusJ θ).im = -Real.sin θ := by
  unfold dMinusJ
  rw [show -I * (θ : ℂ) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

private def wedgePlusJ (α₀ ε : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ < ε ∨ (0 < z.im ∧ z.im < Real.tan α₀ * z.re)}

private def wedgeMinusJ (α₀ ε : ℝ) : Set ℂ :=
  {z : ℂ | ‖z‖ < ε ∨ (z.im < 0 ∧ -z.im < Real.tan α₀ * z.re)}

private lemma wedgePlusJ_domain {α₀ ε : ℝ} (hε : 0 < ε) : Domain (wedgePlusJ α₀ ε) := by
  refine ⟨?_, ?_⟩
  · exact (isOpen_lt continuous_norm continuous_const).union
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im (continuous_const.mul Complex.continuous_re)))
  · intro z hz t ht
    rcases hz with hball | ⟨him, htan⟩
    · left
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hball
    · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
      · left; simpa using hε
      · right
        have hre_eq : ((t : ℂ) * z).re = t * z.re := by simp [Complex.mul_re]
        have him_eq : ((t : ℂ) * z).im = t * z.im := by simp [Complex.mul_im]
        rw [hre_eq, him_eq]
        refine ⟨mul_pos ht_pos him, ?_⟩
        calc t * z.im < t * (Real.tan α₀ * z.re) := mul_lt_mul_of_pos_left htan ht_pos
          _ = Real.tan α₀ * (t * z.re) := by ring

private lemma wedgeMinusJ_domain {α₀ ε : ℝ} (hε : 0 < ε) : Domain (wedgeMinusJ α₀ ε) := by
  refine ⟨?_, ?_⟩
  · exact (isOpen_lt continuous_norm continuous_const).union
      ((isOpen_lt Complex.continuous_im continuous_const).inter
        (isOpen_lt (continuous_neg.comp Complex.continuous_im) (continuous_const.mul Complex.continuous_re)))
  · intro z hz t ht
    rcases hz with hball | ⟨him, htan⟩
    · left
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hball
    · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
      · left; simpa using hε
      · right
        have hre_eq : ((t : ℂ) * z).re = t * z.re := by simp [Complex.mul_re]
        have him_eq : ((t : ℂ) * z).im = t * z.im := by simp [Complex.mul_im]
        rw [hre_eq, him_eq]
        refine ⟨mul_neg_of_pos_of_neg ht_pos him, ?_⟩
        have h1 : -(t * z.im) = t * (-z.im) := by ring
        rw [h1]
        calc t * (-z.im) < t * (Real.tan α₀ * z.re) := mul_lt_mul_of_pos_left htan ht_pos
          _ = Real.tan α₀ * (t * z.re) := by ring

private lemma isPreconnected_of_starJ {U : Set ℂ} (h0 : (0 : ℂ) ∈ U)
    (hstar : ∀ z ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ U) : IsPreconnected U := by
  refine isPreconnected_iff_subset_of_disjoint_closed.mpr fun s t hs ht hsub hdisj => ?_
  have h0_mem : (0 : ℂ) ∈ s ∪ t := hsub h0
  rcases h0_mem with h0s | h0t
  · left
    intro z hz
    let γ : ℝ → ℂ := fun τ => (τ : ℂ) * z
    have hγ_cont : Continuous γ := Complex.continuous_ofReal.mul continuous_const
    have hconn : IsPreconnected (Icc (0 : ℝ) 1) := isPreconnected_Icc
    have hsub' : Icc (0 : ℝ) 1 ⊆ γ ⁻¹' s ∪ γ ⁻¹' t := fun τ hτ => hsub (hstar z hz τ hτ)
    have hdisj' : Icc (0 : ℝ) 1 ∩ (γ ⁻¹' s ∩ γ ⁻¹' t) = ∅ := by
      ext τ; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hτ, hτs, hτt⟩
      have hmem : γ τ ∈ U ∩ (s ∩ t) := ⟨hstar z hz τ hτ, hτs, hτt⟩
      rw [hdisj] at hmem; exact hmem
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn (γ ⁻¹' s) (γ ⁻¹' t)
        (hs.preimage hγ_cont) (ht.preimage hγ_cont) hsub' hdisj' with hL | hR
    · have := hL ⟨zero_le_one, le_rfl⟩; simpa [γ] using this
    · have h0t' : (0 : ℂ) ∈ t := by simpa [γ] using hR ⟨le_rfl, zero_le_one⟩
      have hmem : (0 : ℂ) ∈ U ∩ (s ∩ t) := ⟨h0, h0s, h0t'⟩
      rw [hdisj] at hmem; exact hmem.elim
  · right
    intro z hz
    let γ : ℝ → ℂ := fun τ => (τ : ℂ) * z
    have hγ_cont : Continuous γ := Complex.continuous_ofReal.mul continuous_const
    have hconn : IsPreconnected (Icc (0 : ℝ) 1) := isPreconnected_Icc
    have hsub' : Icc (0 : ℝ) 1 ⊆ γ ⁻¹' s ∪ γ ⁻¹' t := fun τ hτ => hsub (hstar z hz τ hτ)
    have hdisj' : Icc (0 : ℝ) 1 ∩ (γ ⁻¹' s ∩ γ ⁻¹' t) = ∅ := by
      ext τ; simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hτ, hτs, hτt⟩
      have hmem : γ τ ∈ U ∩ (s ∩ t) := ⟨hstar z hz τ hτ, hτs, hτt⟩
      rw [hdisj] at hmem; exact hmem
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn (γ ⁻¹' s) (γ ⁻¹' t)
        (hs.preimage hγ_cont) (ht.preimage hγ_cont) hsub' hdisj' with hL | hR
    · have h0s' : (0 : ℂ) ∈ s := by simpa [γ] using hL ⟨le_rfl, zero_le_one⟩
      have hmem : (0 : ℂ) ∈ U ∩ (s ∩ t) := ⟨h0, h0s', h0t⟩
      rw [hdisj] at hmem; exact hmem.elim
    · have := hR ⟨zero_le_one, le_rfl⟩; simpa [γ] using this

private lemma analyticAt_eqOn_zero_of_iteratedDeriv_zeroJ {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsPreconnected U) (h0 : (0 : ℂ) ∈ U) (hf : AnalyticOnNhd ℂ f U)
    (hderiv : ∀ k : ℕ, iteratedDeriv k f 0 = 0) : EqOn f 0 U := by
  refine hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h0 ?_
  by_contra hne
  obtain ⟨n, g, hg, hg0, hfac⟩ := (hf 0 h0).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hne
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * g z := by
    filter_upwards [hfac] with z hz; simpa [smul_eq_mul] using hz
  have hdn : iteratedDeriv n f 0 = (n.factorial : ℂ) * g 0 := by
    rw [hloc.iteratedDeriv_eq n]
    rw [iteratedDeriv_fun_mul (n := n) (x := (0 : ℂ))
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z ^ n) 0).contDiffAt hg.contDiffAt]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i (fun z : ℂ => z ^ n) (0 : ℂ) * iteratedDeriv (n - i) g 0 =
          if i = n then (n.factorial : ℂ) * g 0 else 0 := by
      intro i _; rw [iteratedDeriv_fun_pow_zero]
      split_ifs with hin
      · subst hin; simp [Nat.choose_self]
      · simp
    rw [Finset.sum_congr rfl hterm]; simp
  exact (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hg0) (hdn ▸ hderiv n)

private lemma tan_lt_tanJ {θ α₀ : ℝ} (hθ : 0 < θ) (hθα : θ < α₀) (hα : α₀ < Real.pi / 2) :
    Real.tan θ < Real.tan α₀ :=
  Real.strictMonoOn_tan ⟨by linarith, by linarith⟩ ⟨by linarith, hα⟩ hθα

private lemma cos_pos_J {θ α₀ : ℝ} (hθ : 0 < θ) (hθα : θ < α₀) (hα : α₀ < Real.pi / 2) :
    0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩

private lemma sin_pos_J {θ α₀ : ℝ} (hθ : 0 < θ) (hθα : θ < α₀) (hα : α₀ < Real.pi / 2) :
    0 < Real.sin θ :=
  Real.sin_pos_of_pos_of_lt_pi hθ (by linarith)

private lemma tan_pos_J {θ α₀ : ℝ} (hθ : 0 < θ) (hθα : θ < α₀) (hα : α₀ < Real.pi / 2) :
    0 < Real.tan θ := by
  rw [Real.tan_eq_sin_div_cos]
  exact div_pos (sin_pos_J hθ hθα hα) (cos_pos_J hθ hθα hα)

private lemma wedgePlusJ_containsRay {θ α₀ ε : ℝ} (hθ : 0 < θ) (hθα : θ < α₀)
    (hα : α₀ < Real.pi / 2) (hε : 0 < ε) :
    ContainsRay (wedgePlusJ α₀ ε) (dPlusJ θ) := by
  intro v hv
  rcases eq_or_lt_of_le hv with rfl | hv_pos
  · left; simpa using hε
  · right
    have hre : (dPlusJ θ * (v : ℂ)).re = Real.cos θ * v := by
      simp [Complex.mul_re, dPlusJ_re]
    have him : (dPlusJ θ * (v : ℂ)).im = Real.sin θ * v := by
      simp [Complex.mul_im, dPlusJ_im]
    rw [hre, him]
    have hcos := cos_pos_J hθ hθα hα
    have hsin := sin_pos_J hθ hθα hα
    refine ⟨mul_pos hsin hv_pos, ?_⟩
    have htan := tan_lt_tanJ hθ hθα hα
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos] at htan
    nlinarith

private lemma wedgeMinusJ_containsRay {θ α₀ ε : ℝ} (hθ : 0 < θ) (hθα : θ < α₀)
    (hα : α₀ < Real.pi / 2) (hε : 0 < ε) :
    ContainsRay (wedgeMinusJ α₀ ε) (dMinusJ θ) := by
  intro v hv
  rcases eq_or_lt_of_le hv with rfl | hv_pos
  · left; simpa using hε
  · right
    have hre : (dMinusJ θ * (v : ℂ)).re = Real.cos θ * v := by
      simp [Complex.mul_re, dMinusJ_re]
    have him : (dMinusJ θ * (v : ℂ)).im = -(Real.sin θ * v) := by
      simp [Complex.mul_im, dMinusJ_im]
    rw [hre, him]
    have hcos := cos_pos_J hθ hθα hα
    have hsin := sin_pos_J hθ hθα hα
    refine ⟨by nlinarith, ?_⟩
    have htan := tan_lt_tanJ hθ hθα hα
    rw [Real.tan_eq_sin_div_cos, div_lt_iff₀ hcos] at htan
    nlinarith

private lemma rotatedPuncturedWedge_zero_eqJ (α₀ ε : ℝ) (ω : ℕ → ℝ) :
    rotatedPuncturedWedge 0 α₀ ε ω = puncturedWedge α₀ ε ω := by
  ext z; simp [rotatedPuncturedWedge]

private lemma wedgePlusJ_subset_punctured {α₀ ε ε₀ : ℝ} {ω : ℕ → ℝ}
    (hα : 0 < α₀) (hα2 : α₀ < Real.pi / 2) (hε₀_le : ε₀ ≤ ε) (hε₀_lt : ε₀ ≤ ω 0 / 2)
    (hω_pos : 0 < ω 0) (hω_mono : StrictMono ω) :
    wedgePlusJ α₀ ε₀ ⊆ rotatedPuncturedWedge 0 α₀ ε ω := by
  rw [rotatedPuncturedWedge_zero_eqJ]
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hball | ⟨him, htan⟩
    · left; simpa [Metric.mem_ball, dist_zero_right] using hball.trans_le hε₀_le
    · right
      have htan_pos : 0 < Real.tan α₀ := by
        rw [Real.tan_eq_sin_div_cos]
        exact div_pos (Real.sin_pos_of_pos_of_lt_pi hα (by linarith))
          (Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩)
      have hre_pos : 0 < z.re := by nlinarith
      refine ⟨hre_pos, ?_⟩
      rwa [abs_of_pos him]
  · rintro ⟨m, rfl⟩
    rcases hz with hball | ⟨him, _⟩
    · rw [Complex.norm_real, Real.norm_of_nonneg (lt_of_lt_of_le hω_pos (hω_mono.monotone (Nat.zero_le m))).le] at hball
      have hle : ω 0 ≤ ω m := hω_mono.monotone (Nat.zero_le m)
      linarith
    · simp at him

private lemma wedgeMinusJ_subset_punctured {α₀ ε ε₀ : ℝ} {ω : ℕ → ℝ}
    (hα : 0 < α₀) (hα2 : α₀ < Real.pi / 2) (hε₀_le : ε₀ ≤ ε) (hε₀_lt : ε₀ ≤ ω 0 / 2)
    (hω_pos : 0 < ω 0) (hω_mono : StrictMono ω) :
    wedgeMinusJ α₀ ε₀ ⊆ rotatedPuncturedWedge 0 α₀ ε ω := by
  rw [rotatedPuncturedWedge_zero_eqJ]
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hball | ⟨him, htan⟩
    · left; simpa [Metric.mem_ball, dist_zero_right] using hball.trans_le hε₀_le
    · right
      have htan_pos : 0 < Real.tan α₀ := by
        rw [Real.tan_eq_sin_div_cos]
        exact div_pos (Real.sin_pos_of_pos_of_lt_pi hα (by linarith))
          (Real.cos_pos_of_mem_Ioo ⟨by linarith, hα2⟩)
      have hre_pos : 0 < z.re := by nlinarith
      refine ⟨hre_pos, ?_⟩
      rwa [abs_of_neg him]
  · rintro ⟨m, rfl⟩
    rcases hz with hball | ⟨him, _⟩
    · rw [Complex.norm_real, Real.norm_of_nonneg (lt_of_lt_of_le hω_pos (hω_mono.monotone (Nat.zero_le m))).le] at hball
      have hle : ω 0 ≤ ω m := hω_mono.monotone (Nat.zero_le m)
      linarith
    · simp at him

private lemma tendsto_coe_farJ {d : ℂ} (hd : 0 < d.re) :
    Tendsto (fun u : ℝ => (u : ℂ)) atTop (BorelStokesVandermonde.far d) := by
  rw [BorelStokesVandermonde.far, Filter.tendsto_comap_iff]
  have hfun : (fun u : ℝ => ((u : ℂ) * d).re) = fun u : ℝ => d.re * u := by
    funext u; simp [Complex.mul_re]; ring
  rw [show (fun x : ℂ => (x * d).re) ∘ (fun u : ℝ => (u : ℂ)) = fun u : ℝ => d.re * u from hfun]
  exact Filter.Tendsto.const_mul_atTop hd tendsto_id

private lemma jet_residual_densityJ (φ : ℂ → ℂ) (j : ℕ) :
    ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhiJ φ)).density =
      fun z : ℂ => (-z) ^ j * φ z := by
  induction j with
  | zero => funext z; simp [aPhiJ, BorelExpr.residual]
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change (fun z : ℂ => -z * ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhiJ φ)).density z) = _
    rw [ih]; funext z; rw [pow_succ']; ring

private lemma jet_residual_atomJ (φ : ℂ → ℂ) (j : ℕ) :
    ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhiJ φ)).atom = 0 := by
  cases j with
  | zero => rfl
  | succ j =>
    rw [Function.iterate_succ_apply']
    rfl

private lemma iteratedDeriv_lateral_eq_laplaceJ {φ : ℂ → ℂ} {U : Set ℂ} {d : ℂ}
    (hU : Domain U) (hray : ContainsRay U d) (hgood : (aPhiJ φ).Good U d) (hd : 0 < d.re) (j : ℕ) :
    ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value d (t : ℂ)) u =
        ∫ v in Ioi (0 : ℝ), d * ((-(d * (v : ℂ))) ^ j * Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) *
          φ (d * (v : ℂ))) := by
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have hrep := (tendsto_coe_farJ hd).eventually (ej.represents hU hray hgood).2
  have hjet := (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ φ) hU hray hgood hd j).1
  filter_upwards [hrep, hjet] with u hurep hujet
  rw [← hujet, hurep, Minor.value, jet_residual_atomJ φ j, zero_add, complexLaplace]
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [damped, Minor.pull, jet_residual_densityJ φ j]
  have hexp : -((u : ℂ) * d) * (v : ℂ) = -(d * (v : ℂ)) * (u : ℂ) := by ring
  rw [hexp]; ring

/-- Tail bound along a flanking ray `d` (`‖d‖ = 1`, `d.re = cos θ > 0`) for any cut `R > 0`. -/
private lemma exp_tail_boundJ {φ : ℂ → ℂ} {U : Set ℂ} {d : ℂ} {θ R : ℝ}
    (hR : 0 < R) (hcos : 0 < Real.cos θ)
    (hd_norm : ‖d‖ = 1) (hd_re : d.re = Real.cos θ)
    (hexp : ExpType (Minor.pull d φ))
    (hgood : (aPhiJ φ).Good U d) (hray : ContainsRay U d) (hU : Domain U) (j : ℕ) :
    ∃ K : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖∫ v in Ioi (R / Real.cos θ),
        d * ((-(d * (v : ℂ))) ^ j * Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ)))‖ ≤
        K * Real.exp (-R * u) := by
  obtain ⟨Cexp, Dexp, hCexp, _, hexp_bd⟩ := hexp
  let v₀ : ℝ := R / Real.cos θ
  have hv₀_pos : 0 < v₀ := div_pos hR hcos
  have h_base_int : IntegrableOn (fun v : ℝ => v ^ j * Real.exp (-(1 / 2 : ℝ) * v)) (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (show -(1 / 4 : ℝ) < 0 by norm_num) 0).const_mul
      ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j)).mono'
      ((by fun_prop : Continuous fun v : ℝ => v ^ j * Real.exp (-(1 / 2 : ℝ) * v)).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    change 0 < v at hv
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le)]
    have hpow := Real.pow_div_factorial_le_exp ((1 / 4 : ℝ) * v) (by positivity) j
    have h1 : 0 < (1 / 4 : ℝ) ^ j := by positivity
    have h2 : 0 < (j.factorial : ℝ) := by positivity
    rw [mul_pow, div_le_iff₀ h2] at hpow
    have hvj : v ^ j ≤ ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp ((1 / 4 : ℝ) * v) := by
      calc v ^ j ≤ (Real.exp ((1 / 4 : ℝ) * v) * j.factorial) / (1 / 4 : ℝ) ^ j :=
            (le_div_iff₀ h1).mpr (by linarith)
        _ = _ := by ring
    calc v ^ j * Real.exp (-(1 / 2 : ℝ) * v)
        ≤ (((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp ((1 / 4 : ℝ) * v)) *
            Real.exp (-(1 / 2 : ℝ) * v) := mul_le_mul_of_nonneg_right hvj (Real.exp_pos _).le
      _ = ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp (-(1 / 4 : ℝ) * v) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  let Ij : ℝ := ∫ v in Ioi (0 : ℝ), v ^ j * Real.exp (-(1 / 2 : ℝ) * v)
  let K : ℝ := Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Ij
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have hej_good : (ej.residual (aPhiJ φ)).Good U d := (ej.represents hU hray hgood).1
  have hej_int := (tendsto_coe_farJ (by rw [hd_re]; exact hcos)).eventually (hej_good.integrable hray)
  refine ⟨K, ?_⟩
  filter_upwards [hej_int, eventually_ge_atTop ((Dexp + 1) / Real.cos θ)] with u hu_int hu_ge
  have hu_re : Dexp + 1 ≤ u * Real.cos θ := (div_le_iff₀ hcos).mp hu_ge
  let Ftail (v : ℝ) : ℂ := d * ((-(d * (v : ℂ))) ^ j *
    Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ)))
  have hF_int_Ioi0 : IntegrableOn Ftail (Ioi 0) :=
    hu_int.congr_fun (fun v _ => by
      rw [damped, Minor.pull, jet_residual_densityJ φ j]
      have hexp' : -((u : ℂ) * d) * (v : ℂ) = -(d * (v : ℂ)) * (u : ℂ) := by ring
      rw [hexp']; dsimp only [Ftail]; ring) measurableSet_Ioi
  have hF_int_tail : IntegrableOn Ftail (Ioi v₀) :=
    hF_int_Ioi0.mono_set (Ioi_subset_Ioi hv₀_pos.le)
  let bnd (v : ℝ) : ℝ :=
    (Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u)) *
      (v ^ j * Real.exp (-(1 / 2 : ℝ) * v))
  have hbnd_int : IntegrableOn bnd (Ioi 0) :=
    h_base_int.const_mul (Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u))
  have h_pt_le : ∀ v ∈ Ioi v₀, ‖Ftail v‖ ≤ bnd v := by
    intro v hv; change v₀ < v at hv
    have hv0 : 0 ≤ v := le_trans hv₀_pos.le hv.le
    have hF_rew : Ftail v = (-(d * (v : ℂ))) ^ j * Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) *
        Minor.pull d φ v := by dsimp only [Ftail, Minor.pull]; ring
    rw [hF_rew, norm_mul, norm_mul, norm_pow, norm_neg, norm_mul, hd_norm, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
    have hexp_re : (-(d * (v : ℂ)) * (u : ℂ)).re = -(u * Real.cos θ) * v := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, hd_re]; ring
    rw [Complex.norm_exp, hexp_re]
    have hpull := hexp_bd v hv0
    have h_exp_split : Real.exp (-(u * Real.cos θ) * v) * (Cexp * Real.exp (Dexp * v)) =
        Cexp * Real.exp (-(u * Real.cos θ - Dexp) * v) := by
      rw [mul_left_comm _ Cexp, ← Real.exp_add]; congr 2; ring
    have h_exp_le : Real.exp (-(u * Real.cos θ - Dexp) * v) ≤
        Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u) * Real.exp (-(1 / 2 : ℝ) * v) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have h_rem_pos : 0 ≤ u * Real.cos θ - Dexp - 1 / 2 := by linarith
      have h_v0_mul : (u * Real.cos θ - Dexp - 1 / 2) * v₀ ≤
          (u * Real.cos θ - Dexp - 1 / 2) * v :=
        mul_le_mul_of_nonneg_left hv.le h_rem_pos
      have hv₀_eq : Real.cos θ * v₀ = R := by dsimp only [v₀]; field_simp [hcos.ne']
      nlinarith [hv₀_eq]
    calc v ^ j * Real.exp (-(u * Real.cos θ) * v) * ‖Minor.pull d φ v‖
        ≤ v ^ j * Real.exp (-(u * Real.cos θ) * v) * (Cexp * Real.exp (Dexp * v)) :=
          mul_le_mul_of_nonneg_left hpull (by positivity)
      _ = Cexp * (v ^ j * Real.exp (-(u * Real.cos θ - Dexp) * v)) := by
          rw [mul_assoc, h_exp_split]; ring
      _ ≤ Cexp * (v ^ j * (Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-R * u) *
            Real.exp (-(1 / 2 : ℝ) * v))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_exp_le (pow_nonneg hv0 _)) hCexp
      _ = bnd v := by dsimp only [bnd]; ring
  calc ‖∫ v in Ioi v₀, Ftail v‖
      ≤ ∫ v in Ioi v₀, ‖Ftail v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioi v₀, bnd v :=
        setIntegral_mono_on hF_int_tail.norm (hbnd_int.mono_set (Ioi_subset_Ioi hv₀_pos.le))
          measurableSet_Ioi h_pt_le
    _ ≤ ∫ v in Ioi 0, bnd v :=
        setIntegral_mono_set hbnd_int
          ((ae_restrict_mem measurableSet_Ioi).mono fun v (hv : 0 < v) => by
            dsimp only [bnd]
            exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le))
          (Eventually.of_forall fun _ hx => Ioi_subset_Ioi hv₀_pos.le hx)
    _ = K * Real.exp (-R * u) := by
        dsimp only [bnd, K, Ij]; rw [integral_const_mul]; ring

private def TriBdIntJ (F : ℂ → ℂ) (R m : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) volume 0 R ∧
  IntervalIntegrable (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) volume (-m * R) (m * R) ∧
  IntervalIntegrable (fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) volume 0 R

private lemma triIntegral_addJ {F G : ℂ → ℂ} {R m : ℝ}
    (hF : TriBdIntJ F R m) (hG : TriBdIntJ G R m) :
    triIntegral (fun z => F z + G z) R m = triIntegral F R m + triIntegral G R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (F ((x : ℂ) * (1 - I * (m : ℂ))) +
      G ((x : ℂ) * (1 - I * (m : ℂ))))) = fun x : ℝ =>
      (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ))) +
      (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))) := by funext x; ring
  have h2 : (fun x : ℝ => (1 + I * (m : ℂ)) * (F ((x : ℂ) * (1 + I * (m : ℂ))) +
      G ((x : ℂ) * (1 + I * (m : ℂ))))) = fun x : ℝ =>
      (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ))) +
      (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))) := by funext x; ring
  rw [h1, h2, intervalIntegral.integral_add hF.1 hG.1,
    intervalIntegral.integral_add hF.2.1 hG.2.1,
    intervalIntegral.integral_add hF.2.2 hG.2.2]; ring

private lemma triIntegral_const_mulJ (c : ℂ) (F : ℂ → ℂ) (R m : ℝ) :
    triIntegral (fun z => c * F z) R m = c * triIntegral F R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (c * F ((x : ℂ) * (1 - I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) := by funext x; ring
  have h2 : (fun x : ℝ => (1 + I * (m : ℂ)) * (c * F ((x : ℂ) * (1 + I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) := by funext x; ring
  rw [h1, h2, intervalIntegral.integral_const_mul c, intervalIntegral.integral_const_mul c,
    intervalIntegral.integral_const_mul c]; ring

private lemma triIntegral_sumJ {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (R m : ℝ)
    (hF : ∀ i ∈ s, TriBdIntJ (F i) R m) :
    triIntegral (fun z => ∑ i ∈ s, F i z) R m = ∑ i ∈ s, triIntegral (F i) R m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [triIntegral]
  | @insert i s hi ih =>
    have hFi := hF i (Finset.mem_insert_self i s)
    have hFs : ∀ j ∈ s, TriBdIntJ (F j) R m := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hsum_int : TriBdIntJ (fun z => ∑ j ∈ s, F j z) R m := by
      refine ⟨?_, ?_, ?_⟩
      · have heq : (fun x : ℝ => (1 - I * (m : ℂ)) * ∑ j ∈ s, F j ((x : ℂ) * (1 - I * (m : ℂ)))) =
            ∑ j ∈ s, fun x : ℝ => (1 - I * (m : ℂ)) * F j ((x : ℂ) * (1 - I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).1
      · have heq : (fun y : ℝ => ∑ j ∈ s, F j ((R : ℂ) + (y : ℂ) * I)) =
            ∑ j ∈ s, fun y : ℝ => F j ((R : ℂ) + (y : ℂ) * I) := by
          funext y; rw [Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).2.1
      · have heq : (fun x : ℝ => (1 + I * (m : ℂ)) * ∑ j ∈ s, F j ((x : ℂ) * (1 + I * (m : ℂ)))) =
            ∑ j ∈ s, fun x : ℝ => (1 + I * (m : ℂ)) * F j ((x : ℂ) * (1 + I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).2.2
    have hfn : (fun z => ∑ j ∈ insert i s, F j z) = fun z => F i z + ∑ j ∈ s, F j z := by
      funext z; rw [Finset.sum_insert hi]
    rw [hfn, triIntegral_addJ hFi hsum_int, ih hFs, Finset.sum_insert hi]

private lemma triIntegral_congrJ {F G : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 - I * (m : ℂ))) = G ((x : ℂ) * (1 - I * (m : ℂ))))
    (h2 : ∀ y ∈ Icc (-m * R) (m * R), F ((R : ℂ) + (y : ℂ) * I) = G ((R : ℂ) + (y : ℂ) * I))
    (h3 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 + I * (m : ℂ))) = G ((x : ℂ) * (1 + I * (m : ℂ)))) :
    triIntegral F R m = triIntegral G R m := by
  unfold triIntegral
  have hmR : -m * R ≤ m * R := by nlinarith
  have i1 : (∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))) :=
    intervalIntegral.integral_congr fun x hx => by rw [uIcc_of_le hR] at hx; rw [h1 x hx]
  have i2 : (∫ y : ℝ in (-m * R)..(m * R), F ((R : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in (-m * R)..(m * R), G ((R : ℂ) + (y : ℂ) * I) :=
    intervalIntegral.integral_congr fun y hy => by rw [uIcc_of_le hmR] at hy; rw [h2 y hy]
  have i3 : (∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))) :=
    intervalIntegral.integral_congr fun x hx => by rw [uIcc_of_le hR] at hx; rw [h3 x hx]
  rw [i1, i2, i3]

private lemma triBdIntJ_of_cont {F : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 - I * (m : ℂ)))) (Icc 0 R))
    (h2 : ContinuousOn (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) (Icc (-m * R) (m * R)))
    (h3 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 + I * (m : ℂ)))) (Icc 0 R)) :
    TriBdIntJ F R m :=
  ⟨(continuousOn_const.mul h1).intervalIntegrable_of_Icc hR,
   h2.intervalIntegrable_of_Icc (by nlinarith),
   (continuousOn_const.mul h3).intervalIntegrable_of_Icc hR⟩

private lemma triIntegral_mul_inv_sub_simple {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ)
    {c R m : ℝ} (hc : 0 < c) (hR : c < R) (hm : 0 < m) :
    triIntegral (fun z : ℂ => F z / (z - (c : ℂ))) R m =
      2 * (Real.pi : ℂ) * I * F (c : ℂ) := by
  have hR_pos : 0 < R := lt_trans hc hR
  have hav : (∀ x : ℝ, (x : ℂ) * (1 - I * (m : ℂ)) ≠ (c : ℂ)) ∧
      (∀ x : ℝ, (x : ℂ) * (1 + I * (m : ℂ)) ≠ (c : ℂ)) ∧
      (∀ y : ℝ, (R : ℂ) + (y : ℂ) * I ≠ (c : ℂ)) := by
    refine ⟨fun x h0 => ?_, fun x h0 => ?_, fun y h0 => ?_⟩
    · have him := congrArg Complex.im h0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
        Complex.one_im, Complex.I_im, mul_zero, zero_mul, zero_sub, add_zero] at him
      have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * (-m) = 0)).resolve_right (neg_ne_zero.mpr hm.ne')
      subst hx0; have hre := congrArg Complex.re h0; simp at hre; linarith
    · have him := congrArg Complex.im h0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add] at him
      have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * m = 0)).resolve_right hm.ne'
      subst hx0; have hre := congrArg Complex.re h0; simp at hre; linarith
    · have hre := congrArg Complex.re h0; simp [Complex.mul_re] at hre; linarith
  let G : ℂ → ℂ := dslope F (c : ℂ)
  have hG_an : AnalyticOnNhd ℂ G univ :=
    ((Complex.differentiableOn_dslope (Filter.univ_mem : univ ∈ 𝓝 (c : ℂ))).mpr
      hF.differentiableOn).analyticOnNhd isOpen_univ
  have htri_G : triIntegral G R m = 0 :=
    triIntegral_eq_zero_of_analyticOn hR_pos.le hm.le isOpen_univ (subset_univ _) hG_an
  have hG_int : TriBdIntJ G R m :=
    triBdIntJ_of_cont hR_pos.le hm.le
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
  have hP_int : TriBdIntJ (fun z => F (c : ℂ) * (z - (c : ℂ))⁻¹) R m :=
    triBdIntJ_of_cont hR_pos.le hm.le
      (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun x h0 =>
        hav.1 x (sub_eq_zero.mp h0))))
      (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun y h0 =>
        hav.2.2 y (sub_eq_zero.mp h0))))
      (Continuous.continuousOn (continuous_const.mul (Continuous.inv₀ (by fun_prop) fun x h0 =>
        hav.2.1 x (sub_eq_zero.mp h0))))
  have hsplit : ∀ z : ℂ, z ≠ (c : ℂ) → F z / (z - (c : ℂ)) = G z + F (c : ℂ) * (z - (c : ℂ))⁻¹ := by
    intro z hzc
    have hsub : z - (c : ℂ) ≠ 0 := sub_ne_zero.mpr hzc
    have hsl := sub_smul_dslope F (c : ℂ) z
    rw [smul_eq_mul] at hsl
    dsimp only [G]
    rw [← sub_add_cancel (F z) (F (c : ℂ)), ← hsl, add_div, mul_div_cancel_left₀ _ hsub, div_eq_mul_inv]
  have hcongr := triIntegral_congrJ
    (F := fun z : ℂ => F z / (z - (c : ℂ)))
    (G := fun z : ℂ => G z + F (c : ℂ) * (z - (c : ℂ))⁻¹)
    hR_pos.le hm.le
    (fun x _ => hsplit _ (hav.1 x)) (fun y _ => hsplit _ (hav.2.2 y)) (fun x _ => hsplit _ (hav.2.1 x))
  rw [hcongr, triIntegral_addJ hG_int hP_int, htri_G, zero_add, triIntegral_const_mulJ,
    triIntegral_inv_sub hc hR hm]
  ring

/-- **Single-Component Simple-Pole Stokes Jump at Any Pole-Avoiding Cut `R > 0`**:
For a simple-pole kernel `φ` along `θ₀ = 0` with poles `ω m`, if `M : ℕ` satisfies
`∀ m < M, ω m < R` and `R < ω M` (hence `R` avoids every pole `ω m`), then for every `j`,
`iteratedDeriv j (g_neg - g_pos) u - ∑_{m < M} (2π i res m (-ω m)^j) e^{-ω m u} = O(e^{-R u})`. -/
private lemma simplePole_stokes_jump_at_cut
    {φ : ℂ → ℂ} {ω : ℕ → ℝ} {res : ℕ → ℂ} {α₀ θ ε ε₀ R : ℝ} {M : ℕ}
    (hθ_pos : 0 < θ) (hθ_lt : θ < α₀) (hα₀_lt : α₀ < Real.pi / 2)
    (hε₀_pos : 0 < ε₀) (hε₀_le : ε₀ ≤ ε) (hε₀_lt : ε₀ ≤ ω 0 / 2)
    (hω_pos : 0 < ω 0) (hω_mono : StrictMono ω)
    (hana : AnalyticOnNhd ℂ φ (rotatedPuncturedWedge 0 α₀ ε ω))
    (hpole : ∀ m, ∃ L : ℂ, Tendsto (fun z => φ z - res m / (z - (ω m : ℂ))) (𝓝[≠] (ω m : ℂ)) (𝓝 L))
    (hexpP : ExpType (Minor.pull (dPlusJ θ) φ))
    (hexpM : ExpType (Minor.pull (dMinusJ θ) φ))
    (hR_pos : 0 < R) (hM_below : ∀ m < M, ω m < R) (hM_above : R < ω M) (j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dMinusJ θ) (t : ℂ) -
          (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u -
        ∑ m ∈ Finset.range M,
          (2 * (Real.pi : ℂ) * I * res m * (-(ω m : ℂ)) ^ j) *
            Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
        C * Real.exp (-R * u) := by
  classical
  let mθ : ℝ := Real.tan θ
  let v₀ : ℝ := R / Real.cos θ
  have hα_pos : 0 < α₀ := hθ_pos.trans hθ_lt
  have hcos : 0 < Real.cos θ := cos_pos_J hθ_pos hθ_lt hα₀_lt
  have hm_pos : 0 < mθ := tan_pos_J hθ_pos hθ_lt hα₀_lt
  have hv₀_pos : 0 < v₀ := div_pos hR_pos hcos
  have hreP : 0 < (dPlusJ θ).re := by rw [dPlusJ_re]; exact hcos
  have hreM : 0 < (dMinusJ θ).re := by rw [dMinusJ_re]; exact hcos
  let Up := wedgePlusJ α₀ ε₀
  let Um := wedgeMinusJ α₀ ε₀
  have hUp_dom : Domain Up := wedgePlusJ_domain hε₀_pos
  have hUm_dom : Domain Um := wedgeMinusJ_domain hε₀_pos
  have hrayP : ContainsRay Up (dPlusJ θ) := wedgePlusJ_containsRay hθ_pos hθ_lt hα₀_lt hε₀_pos
  have hrayM : ContainsRay Um (dMinusJ θ) := wedgeMinusJ_containsRay hθ_pos hθ_lt hα₀_lt hε₀_pos
  have hgoodP : (aPhiJ φ).Good Up (dPlusJ θ) :=
    ⟨hana.mono (wedgePlusJ_subset_punctured hα_pos hα₀_lt hε₀_le hε₀_lt hω_pos hω_mono), hexpP⟩
  have hgoodM : (aPhiJ φ).Good Um (dMinusJ θ) :=
    ⟨hana.mono (wedgeMinusJ_subset_punctured hα_pos hα₀_lt hε₀_le hε₀_lt hω_pos hω_mono), hexpM⟩
  have h_sub_deriv : ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dMinusJ θ) (t : ℂ) -
          (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u =
        iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dMinusJ θ) (t : ℂ)) u -
          iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u :=
    eventually_iteratedDeriv_sub
      (fun i _ => (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ φ) hUm_dom hrayM hgoodM hreM i).2)
      (fun i _ => (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ φ) hUp_dom hrayP hgoodP hreP i).2)
  have h_lapP := iteratedDeriv_lateral_eq_laplaceJ hUp_dom hrayP hgoodP hreP j
  have h_lapM := iteratedDeriv_lateral_eq_laplaceJ hUm_dom hrayM hgoodM hreM j
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have h_intP := (tendsto_coe_farJ hreP).eventually ((ej.represents hUp_dom hrayP hgoodP).1.integrable hrayP)
  have h_intM := (tendsto_coe_farJ hreM).eventually ((ej.represents hUm_dom hrayM hgoodM).1.integrable hrayM)
  obtain ⟨Km, hKm⟩ := exp_tail_boundJ hR_pos hcos (norm_dMinusJ θ) (dMinusJ_re θ) hexpM hgoodM hrayM hUm_dom j
  obtain ⟨Kp, hKp⟩ := exp_tail_boundJ hR_pos hcos (norm_dPlusJ θ) (dPlusJ_re θ) hexpP hgoodP hrayP hUp_dom j
  -- Avoidance of poles on triangle boundary
  have h_avoid : (∀ x : ℝ, ∀ m : ℕ, (x : ℂ) * (1 - I * (mθ : ℂ)) ≠ (ω m : ℂ)) ∧
      (∀ x : ℝ, ∀ m : ℕ, (x : ℂ) * (1 + I * (mθ : ℂ)) ≠ (ω m : ℂ)) ∧
      (∀ y : ℝ, ∀ m : ℕ, (R : ℂ) + (y : ℂ) * I ≠ (ω m : ℂ)) := by
    refine ⟨fun x m h0 => ?_, fun x m h0 => ?_, fun y m h0 => ?_⟩
    · have him := congrArg Complex.im h0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
        Complex.one_im, Complex.I_im, mul_zero, zero_mul, zero_sub, add_zero] at him
      have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * (-mθ) = 0)).resolve_right (neg_ne_zero.mpr hm_pos.ne')
      subst hx0; have hre := congrArg Complex.re h0; simp at hre
      have hωm : 0 < ω m := lt_of_lt_of_le hω_pos (hω_mono.monotone (Nat.zero_le m))
      linarith
    · have him := congrArg Complex.im h0
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add] at him
      have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * mθ = 0)).resolve_right hm_pos.ne'
      subst hx0; have hre := congrArg Complex.re h0; simp at hre
      have hωm : 0 < ω m := lt_of_lt_of_le hω_pos (hω_mono.monotone (Nat.zero_le m))
      linarith
    · have hre := congrArg Complex.re h0; simp [Complex.mul_re] at hre
      rcases lt_or_ge m M with hm | hm
      · exact (hM_below m hm).ne hre.symm
      · exact (lt_of_lt_of_le hM_above (hω_mono.monotone hm)).ne hre
  -- Triangle residue formula for Fkern(z) = (-z)^j e^{-z u} φ(z)
  have htri_eq : ∀ u : ℝ,
      triIntegral (fun z => (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z) R mθ =
        ∑ m ∈ Finset.range M,
          (2 * (Real.pi : ℂ) * I * res m * (-(ω m : ℂ)) ^ j) *
            Complex.exp (-(ω m : ℂ) * (u : ℂ)) := by
    intro u
    let Un : Set ℂ := borelWedge α₀ ε₀ ∩ {z : ℂ | z.re < ω M}
    have hUn_open : IsOpen Un :=
      (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im)
          (continuous_const.mul Complex.continuous_re)))).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have htri_sub : closedTri R mθ ⊆ Un := by
      intro z hz
      refine ⟨?_, lt_of_le_of_lt hz.2.1 hM_above⟩
      rcases eq_or_lt_of_le hz.1 with hz0 | hzpos
      · left
        have him0 : z.im = 0 := abs_nonpos_iff.mp (by simpa [← hz0] using hz.2.2)
        have hz_eq : z = 0 := Complex.ext hz0.symm him0
        simpa [hz_eq, Metric.mem_ball, dist_zero_right] using hε₀_pos
      · right
        exact ⟨hzpos, lt_of_le_of_lt hz.2.2 (mul_lt_mul_of_pos_right (tan_lt_tanJ hθ_pos hθ_lt hα₀_lt) hzpos)⟩
    let Sn (z : ℂ) : ℂ := ∑ m ∈ Finset.range M, res m / (z - (ω m : ℂ))
    let Pset : Set ℂ := (fun m : ℕ => (ω m : ℂ)) '' (Finset.range M : Set ℕ)
    let ψn (z : ℂ) : ℂ :=
      if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => φ w - Sn w) else φ z - Sn z
    have hP_fin : Pset.Finite := (Finset.finite_toSet (Finset.range M)).image _
    have hP_closed : IsClosed Pset := hP_fin.isClosed
    have hUn_sub : Un \ Pset ⊆ rotatedPuncturedWedge 0 α₀ ε ω := by
      rw [rotatedPuncturedWedge_zero_eqJ]
      intro w ⟨hwU, hwP⟩
      refine ⟨?_, ?_⟩
      · rcases hwU.1 with hw_ball | hw_sec
        · left; exact Metric.ball_subset_ball hε₀_le hw_ball
        · right; exact hw_sec
      · rintro ⟨m, rfl⟩
        have hm_lt : ω m < ω M := by simpa using hwU.2
        have hm_idx : m < M := hω_mono.lt_iff_lt.mp hm_lt
        exact hwP ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr hm_idx), rfl⟩
    have hSn_an : ∀ z ∈ Un \ Pset, AnalyticAt ℂ Sn z := by
      intro z hz
      refine Finset.analyticAt_fun_sum _ fun m hm => analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
      intro h0; exact hz.2 ⟨m, Finset.mem_coe.mpr hm, (sub_eq_zero.mp h0).symm⟩
    have hψ_an : AnalyticOnNhd ℂ ψn Un := by
      intro z hzU
      by_cases hzP : z ∈ Pset
      · obtain ⟨k, hk_mem, rfl⟩ := hzP
        let Qk : Set ℂ := Pset \ {(ω k : ℂ)}
        have hQk_closed : IsClosed Qk := (hP_fin.subset Set.sdiff_subset).isClosed
        let Vk : Set ℂ := Un \ Qk
        have hVk_open : IsOpen Vk := hUn_open.sdiff hQk_closed
        have hwk_Vk : (ω k : ℂ) ∈ Vk := ⟨hzU, fun hmem => hmem.2 rfl⟩
        have hmem_punc : Vk \ {(ω k : ℂ)} ∈ 𝓝[≠] (ω k : ℂ) := by
          rw [Set.sdiff_eq, inter_comm]; exact inter_mem_nhdsWithin _ (hVk_open.mem_nhds hwk_Vk)
        have hsub_open : Vk \ {(ω k : ℂ)} ⊆ Un \ Pset := fun ζ hζ =>
          ⟨hζ.1.1, fun hP => hζ.2 (by by_contra hne; exact hζ.1.2 ⟨hP, hne⟩)⟩
        have hψ_diff_punc : ∀ᶠ w in 𝓝[≠] (ω k : ℂ), DifferentiableAt ℂ ψn w := by
          filter_upwards [hmem_punc] with w hw
          have hdiff := ((hana w (hUn_sub (hsub_open hw))).sub (hSn_an w (hsub_open hw))).differentiableAt
          refine hdiff.congr_of_eventuallyEq ?_
          filter_upwards [(hUn_open.sdiff hP_closed).mem_nhds (hsub_open hw)] with ζ hζ
          exact ite_eq_right_iff.mpr fun hmem => absurd hmem hζ.2
        let Sn_rest (w : ℂ) : ℂ := ∑ m ∈ (Finset.range M).erase k, res m / (w - (ω m : ℂ))
        have hSn_split : ∀ w : ℂ, φ w - Sn w = (φ w - res k / (w - (ω k : ℂ))) - Sn_rest w := by
          intro w; dsimp only [Sn, Sn_rest]
          rw [← Finset.add_sum_erase (Finset.range M) (fun m => res m / (w - (ω m : ℂ))) hk_mem]; ring
        have hrest_an : AnalyticAt ℂ Sn_rest (ω k : ℂ) := by
          refine Finset.analyticAt_fun_sum _ fun m hm => analyticAt_const.div (analyticAt_id.sub analyticAt_const) ?_
          intro h0; exact hω_mono.injective.ne (Finset.mem_erase.mp hm).1.symm
            (by exact_mod_cast sub_eq_zero.mp h0)
        obtain ⟨L, hL⟩ := hpole k
        have h_tend : Tendsto (fun w => φ w - Sn w) (𝓝[≠] (ω k : ℂ)) (𝓝 (L - Sn_rest (ω k : ℂ))) := by
          simp_rw [hSn_split]; exact hL.sub hrest_an.continuousAt.continuousWithinAt.tendsto
        have hψ_tend : Tendsto ψn (𝓝[≠] (ω k : ℂ)) (𝓝 (L - Sn_rest (ω k : ℂ))) := by
          refine h_tend.congr' ?_
          filter_upwards [hmem_punc] with w hw
          exact (ite_eq_right_iff.mpr fun hmem => absurd hmem (hsub_open hw).2).symm
        have hψ_at : ψn (ω k : ℂ) = L - Sn_rest (ω k : ℂ) := by
          have hmemP : (ω k : ℂ) ∈ Pset := ⟨k, Finset.mem_coe.mpr hk_mem, rfl⟩
          dsimp only [ψn]; rw [ite_eq_left_iff.mpr fun hnot => absurd hmemP hnot, h_tend.limUnder_eq]
        exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hψ_diff_punc
          (continuousAt_iff_punctured_nhds.mpr (by simpa [hψ_at] using hψ_tend))
      · have hdiff := (hana z (hUn_sub ⟨hzU, hzP⟩)).sub (hSn_an z ⟨hzU, hzP⟩)
        refine hdiff.congr ?_
        filter_upwards [(hUn_open.sdiff hP_closed).mem_nhds ⟨hzU, hzP⟩] with w hw
        exact (ite_eq_right_iff.mpr fun hmem => absurd hmem hw.2).symm
    let Fψ (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * ψn z
    have hFψ_an : AnalyticOnNhd ℂ Fψ Un :=
      ((analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)).mul hψ_an
    have htri_ψ : triIntegral Fψ R mθ = 0 :=
      triIntegral_eq_zero_of_analyticOn hR_pos.le hm_pos.le hUn_open htri_sub hFψ_an
    let termM (m : ℕ) (z : ℂ) : ℂ :=
      (-z) ^ j * Complex.exp (-z * (u : ℂ)) * (res m / (z - (ω m : ℂ)))
    have htermM_int : ∀ m ∈ Finset.range M, TriBdIntJ (termM m) R mθ := by
      intro m _
      refine triBdIntJ_of_cont hR_pos.le hm_pos.le
        ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
          (continuous_const.div (by fun_prop) fun x h0 => h_avoid.1 x m (sub_eq_zero.mp h0))))
        ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
          (continuous_const.div (by fun_prop) fun y h0 => h_avoid.2.2 y m (sub_eq_zero.mp h0))))
        ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
          (continuous_const.div (by fun_prop) fun x h0 => h_avoid.2.1 x m (sub_eq_zero.mp h0))))
    have hFψ_int : TriBdIntJ Fψ R mθ := by
      refine triBdIntJ_of_cont hR_pos.le hm_pos.le
        (hFψ_an.continuousOn.comp (by fun_prop) fun x hx => htri_sub ?_)
        (hFψ_an.continuousOn.comp (by fun_prop) fun y hy => htri_sub ?_)
        (hFψ_an.continuousOn.comp (by fun_prop) fun x hx => htri_sub ?_)
      · refine ⟨by simp [Complex.mul_re]; exact hx.1, by simp [Complex.mul_re]; exact hx.2, ?_⟩
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, sub_zero, add_zero, zero_sub, zero_add, neg_zero, mul_one, mul_neg, one_mul]
        rw [abs_neg, abs_mul, abs_of_nonneg hx.1, abs_of_pos hm_pos, mul_comm]
      · refine ⟨by simp [Complex.mul_re]; exact hR_pos.le, by simp [Complex.mul_re], ?_⟩
        simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
          add_zero, zero_add]
        have hy' : y ∈ Icc (-(mθ * R)) (mθ * R) := by simpa [neg_mul] using hy
        exact abs_le.mpr hy'
      · refine ⟨by simp [Complex.mul_re]; exact hx.1, by simp [Complex.mul_re]; exact hx.2, ?_⟩
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
          mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one, one_mul]
        rw [abs_mul, abs_of_nonneg hx.1, abs_of_pos hm_pos, mul_comm]
    have hsum_int : TriBdIntJ (fun z => ∑ m ∈ Finset.range M, termM m z) R mθ := by
      refine ⟨?_, ?_, ?_⟩
      · have heq : (fun x : ℝ => (1 - I * (mθ : ℂ)) *
            ∑ m ∈ Finset.range M, termM m ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
            ∑ m ∈ Finset.range M, fun x : ℝ => (1 - I * (mθ : ℂ)) * termM m ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).1
      · have heq : (fun y : ℝ => ∑ m ∈ Finset.range M, termM m ((R : ℂ) + (y : ℂ) * I)) =
            ∑ m ∈ Finset.range M, fun y : ℝ => termM m ((R : ℂ) + (y : ℂ) * I) := by
          funext y; rw [Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).2.1
      · have heq : (fun x : ℝ => (1 + I * (mθ : ℂ)) *
            ∑ m ∈ Finset.range M, termM m ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
            ∑ m ∈ Finset.range M, fun x : ℝ => (1 + I * (mθ : ℂ)) * termM m ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).2.2
    have hpt_eq : ∀ z : ℂ, z ∉ Pset →
        (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z = Fψ z + ∑ m ∈ Finset.range M, termM m z := by
      intro z hz
      dsimp only [Fψ, ψn, termM, Sn]
      rw [ite_eq_right_iff.mpr (fun h => absurd h hz), mul_sub, Finset.mul_sum]; ring
    have hcongr := triIntegral_congrJ
      (F := fun z : ℂ => (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z)
      (G := fun z : ℂ => Fψ z + ∑ m ∈ Finset.range M, termM m z)
      hR_pos.le hm_pos.le
      (fun x _ => hpt_eq _ fun ⟨m, _, hm⟩ => h_avoid.1 x m hm.symm)
      (fun y _ => hpt_eq _ fun ⟨m, _, hm⟩ => h_avoid.2.2 y m hm.symm)
      (fun x _ => hpt_eq _ fun ⟨m, _, hm⟩ => h_avoid.2.1 x m hm.symm)
    rw [hcongr, triIntegral_addJ hFψ_int hsum_int, htri_ψ, zero_add,
      triIntegral_sumJ _ _ R mθ htermM_int]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hterm_rew : termM m = fun z => res m * (((-z) ^ j * Complex.exp (-z * (u : ℂ))) / (z - (ω m : ℂ))) := by
      funext z; dsimp only [termM]; ring
    rw [hterm_rew, triIntegral_const_mulJ]
    have hFn : AnalyticOnNhd ℂ (fun z : ℂ => (-z) ^ j * Complex.exp (-z * (u : ℂ))) univ :=
      (analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)
    rw [triIntegral_mul_inv_sub_simple hFn
      (lt_of_lt_of_le hω_pos (hω_mono.monotone (Nat.zero_le m)))
      (hM_below m (Finset.mem_range.mp hm)) hm_pos]
    ring
  -- Vertical edge bound on x = R
  have h_vert_sub : ∀ y ∈ Icc (-mθ * R) (mθ * R),
      (R : ℂ) + (y : ℂ) * I ∈ rotatedPuncturedWedge 0 α₀ ε ω := by
    rw [rotatedPuncturedWedge_zero_eqJ]
    intro y hy
    refine ⟨Or.inr ?_, fun ⟨m, hm⟩ => h_avoid.2.2 y m hm.symm⟩
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add]
    rw [show -mθ * R = -(mθ * R) by ring] at hy
    exact ⟨hR_pos, lt_of_le_of_lt (abs_le.mpr hy)
      (mul_lt_mul_of_pos_right (tan_lt_tanJ hθ_pos hθ_lt hα₀_lt) hR_pos)⟩
  have hφ_vert_cont : ContinuousOn (fun y : ℝ => φ ((R : ℂ) + (y : ℂ) * I)) (Icc (-mθ * R) (mθ * R)) :=
    hana.continuousOn.comp (by fun_prop) h_vert_sub
  obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ_vert_cont
  let Kv : ℝ := (2 * mθ * R) * ((R / Real.cos θ) ^ j * max Mφ 0)
  have h_vert_bd : ∀ u : ℝ,
      ‖I * (∫ y : ℝ in (-mθ * R)..(mθ * R),
        (-((R : ℂ) + (y : ℂ) * I)) ^ j * Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ)) *
          φ ((R : ℂ) + (y : ℂ) * I))‖ ≤ Kv * Real.exp (-R * u) := by
    intro u
    rw [norm_mul, Complex.norm_I, one_mul]
    have hpt : ∀ y ∈ uIoc (-mθ * R) (mθ * R),
        ‖(-((R : ℂ) + (y : ℂ) * I)) ^ j * Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ)) *
          φ ((R : ℂ) + (y : ℂ) * I)‖ ≤
          ((R / Real.cos θ) ^ j * max Mφ 0) * Real.exp (-R * u) := by
      intro y hy
      rw [uIoc_of_le (by nlinarith : -mθ * R ≤ mθ * R)] at hy
      have hy_cc : y ∈ Icc (-mθ * R) (mθ * R) := ⟨hy.1.le, hy.2⟩
      have hnorm_z : ‖-((R : ℂ) + (y : ℂ) * I)‖ ≤ R / Real.cos θ := by
        rw [norm_neg, Complex.norm_def]
        have hy_sq : y ^ 2 ≤ mθ ^ 2 * R ^ 2 := by
          have : |y| ≤ mθ * R := abs_le.mpr (by simpa [neg_mul] using hy_cc)
          rw [← sq_abs y]
          calc |y| ^ 2 ≤ (mθ * R) ^ 2 := sq_le_sq' (by linarith [abs_nonneg y]) this
            _ = mθ ^ 2 * R ^ 2 := by ring
        have hnsq : Complex.normSq ((R : ℂ) + (y : ℂ) * I) ≤ (R / Real.cos θ) ^ 2 := by
          rw [Complex.normSq_apply]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
            mul_one, zero_add]
          have hsec : 1 + mθ ^ 2 = (Real.cos θ) ^ (-2 : ℤ) := by
            dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, _root_.zpow_neg, zpow_two]
            have hc := hcos.ne'; have hid := Real.sin_sq_add_cos_sq θ
            field_simp [hc]; linarith
          calc R * R + y * y = R ^ 2 + y ^ 2 := by ring
            _ ≤ R ^ 2 + mθ ^ 2 * R ^ 2 := by linarith
            _ = R ^ 2 * (1 + mθ ^ 2) := by ring
            _ = R ^ 2 * (Real.cos θ) ^ (-2 : ℤ) := by rw [hsec]
            _ = (R / Real.cos θ) ^ 2 := by rw [_root_.zpow_neg, zpow_two, div_pow]; ring
        exact Real.sqrt_le_iff.mpr ⟨div_nonneg hR_pos.le hcos.le, hnsq⟩
      have hexp_norm : ‖Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ))‖ = Real.exp (-R * u) := by
        rw [Complex.norm_exp]; simp [Complex.mul_re]
      have hφ_le : ‖φ ((R : ℂ) + (y : ℂ) * I)‖ ≤ max Mφ 0 := (hMφ y hy_cc).trans (le_max_left _ _)
      rw [norm_mul, norm_mul, norm_pow, hexp_norm]
      calc ‖-((R : ℂ) + (y : ℂ) * I)‖ ^ j * Real.exp (-R * u) * ‖φ ((R : ℂ) + (y : ℂ) * I)‖
          ≤ (R / Real.cos θ) ^ j * Real.exp (-R * u) * max Mφ 0 := by gcongr
        _ = ((R / Real.cos θ) ^ j * max Mφ 0) * Real.exp (-R * u) := by ring
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    calc ‖∫ y : ℝ in (-mθ * R)..(mθ * R), _‖
        ≤ ((R / Real.cos θ) ^ j * max Mφ 0) * Real.exp (-R * u) * |mθ * R - -mθ * R| := hle
      _ = Kv * Real.exp (-R * u) := by
          rw [show mθ * R - -mθ * R = 2 * mθ * R by ring, abs_of_pos (by positivity)]
          dsimp only [Kv]; ring
  refine ⟨Kv + Km + Kp, ?_⟩
  filter_upwards [h_sub_deriv, h_lapP, h_lapM, h_intP, h_intM, hKp, hKm] with
    u hsub hlp hlm hip him hkp_bd hkm_bd
  let Fkern (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z
  have hintP_Ioi : IntegrableOn (fun v : ℝ => dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))) (Ioi 0) :=
    hip.congr_fun (fun v _ => by
      rw [damped, Minor.pull, jet_residual_densityJ φ j]
      have hexp : -((u : ℂ) * dPlusJ θ) * (v : ℂ) = -(dPlusJ θ * (v : ℂ)) * (u : ℂ) := by ring
      rw [hexp]; dsimp only [Fkern]; ring) measurableSet_Ioi
  have hintM_Ioi : IntegrableOn (fun v : ℝ => dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))) (Ioi 0) :=
    him.congr_fun (fun v _ => by
      rw [damped, Minor.pull, jet_residual_densityJ φ j]
      have hexp : -((u : ℂ) * dMinusJ θ) * (v : ℂ) = -(dMinusJ θ * (v : ℂ)) * (u : ℂ) := by ring
      rw [hexp]; dsimp only [Fkern]; ring) measurableSet_Ioi
  have hsplitP := intervalIntegral.integral_interval_add_Ioi hintP_Ioi
    (hintP_Ioi.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hsplitM := intervalIntegral.integral_interval_add_Ioi hintM_Ioi
    (hintM_Ioi.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hcovP : ∫ v in (0 : ℝ)..v₀, dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 + I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun v : ℝ => dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))) hcos.ne' (a := 0) (b := R)
    have hmul_eq : (1 + I * (mθ : ℂ)) = ((Real.cos θ)⁻¹ : ℂ) * dPlusJ θ := by
      rw [dPlusJ_eq]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
      have hc : (Real.cos θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
      field_simp [hc]
    have heq_int : (fun x : ℝ => (1 + I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos θ)⁻¹ • (dPlusJ θ * Fkern (dPlusJ θ * ((x / Real.cos θ : ℝ) : ℂ))) := by
      funext x
      have harg : (x : ℂ) * (1 + I * (mθ : ℂ)) = dPlusJ θ * ((x / Real.cos θ : ℝ) : ℂ) := by
        rw [hmul_eq]; push_cast; ring
      rw [harg, Complex.real_smul, hmul_eq]; push_cast; ring
    rw [heq_int, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne',
      one_smul, zero_div]
  have hcovM : ∫ v in (0 : ℝ)..v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 - I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun v : ℝ => dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))) hcos.ne' (a := 0) (b := R)
    have hmul_eq : (1 - I * (mθ : ℂ)) = ((Real.cos θ)⁻¹ : ℂ) * dMinusJ θ := by
      rw [dMinusJ_eq]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
      have hc : (Real.cos θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
      field_simp [hc]
    have heq_int : (fun x : ℝ => (1 - I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos θ)⁻¹ • (dMinusJ θ * Fkern (dMinusJ θ * ((x / Real.cos θ : ℝ) : ℂ))) := by
      funext x
      have harg : (x : ℂ) * (1 - I * (mθ : ℂ)) = dMinusJ θ * ((x / Real.cos θ : ℝ) : ℂ) := by
        rw [hmul_eq]; push_cast; ring
      rw [harg, Complex.real_smul, hmul_eq]; push_cast; ring
    rw [heq_int, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne',
      one_smul, zero_div]
  have h_id : iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dMinusJ θ) (t : ℂ) -
        (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u -
      ∑ m ∈ Finset.range M,
        (2 * (Real.pi : ℂ) * I * res m * (-(ω m : ℂ)) ^ j) *
          Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
      -(I * (∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I))) +
        (∫ v in Ioi v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))) -
        (∫ v in Ioi v₀, dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))) := by
    rw [hsub, hlm, hlp, ← htri_eq u]
    change (∫ v in Ioi (0 : ℝ), dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))) -
        (∫ v in Ioi (0 : ℝ), dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))) -
        triIntegral Fkern R mθ = _
    rw [← hsplitM, ← hsplitP, hcovM, hcovP]; unfold triIntegral; ring
  rw [h_id]
  calc ‖-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I)) +
          (∫ v in Ioi v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))) -
          (∫ v in Ioi v₀, dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ)))‖
      ≤ ‖-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I))‖ +
          ‖∫ v in Ioi v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))‖ +
          ‖∫ v in Ioi v₀, dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))‖ := by
        linarith [norm_sub_le (-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I)) +
            (∫ v in Ioi v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ))))
            (∫ v in Ioi v₀, dPlusJ θ * Fkern (dPlusJ θ * (v : ℂ))),
          norm_add_le (-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I)))
            (∫ v in Ioi v₀, dMinusJ θ * Fkern (dMinusJ θ * (v : ℂ)))]
    _ ≤ Kv * Real.exp (-R * u) + Km * Real.exp (-R * u) + Kp * Real.exp (-R * u) := by
        rw [norm_neg]; exact add_le_add (add_le_add (h_vert_bd u) hkm_bd) hkp_bd
    _ = (Kv + Km + Kp) * Real.exp (-R * u) := by ring

private lemma pow_mul_exp_neg_le_oneJ (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, u ^ K * Real.exp (-δ * u) ≤ 1 := by
  let U₀ : ℝ := max 1 (((K + 1).factorial : ℝ) / δ ^ (K + 1))
  filter_upwards [eventually_ge_atTop U₀] with u hu
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hU_ge : ((K + 1).factorial : ℝ) / δ ^ (K + 1) ≤ u := le_trans (le_max_right _ _) hu
  have harg := Real.pow_div_factorial_le_exp (δ * u) (by positivity) (K + 1)
  have hfac : 0 < ((K + 1).factorial : ℝ) := by positivity
  have hpow : 0 < (δ * u) ^ (K + 1) := pow_pos (by positivity) (K + 1)
  have hexp : Real.exp (-δ * u) ≤ ((K + 1).factorial : ℝ) / (δ ^ (K + 1) * u ^ (K + 1)) := by
    calc Real.exp (-δ * u) = (Real.exp (δ * u))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
      _ ≤ ((δ * u) ^ (K + 1) / ((K + 1).factorial : ℝ))⁻¹ := inv_anti₀ (div_pos hpow hfac) harg
      _ = ((K + 1).factorial : ℝ) / (δ ^ (K + 1) * u ^ (K + 1)) := by rw [inv_div, mul_pow]
  have hδ_pos : 0 < δ ^ (K + 1) := pow_pos hδ (K + 1)
  calc u ^ K * Real.exp (-δ * u)
      ≤ u ^ K * (((K + 1).factorial : ℝ) / (δ ^ (K + 1) * u ^ (K + 1))) :=
        mul_le_mul_of_nonneg_left hexp (pow_nonneg hu_pos.le K)
    _ = (((K + 1).factorial : ℝ) / δ ^ (K + 1)) / u := by
        rw [pow_succ u K]; field_simp [hu_pos.ne', hδ_pos.ne']
    _ ≤ u / u := div_le_div_of_nonneg_right hU_ge hu_pos.le
    _ = 1 := div_self hu_pos.ne'

private lemma const_mul_exp_neg_le_oneJ {δ C : ℝ} (hδ : 0 < δ) (_hC : 0 ≤ C) :
    ∀ᶠ u : ℝ in atTop, C * Real.exp (-δ * u) ≤ 1 := by
  filter_upwards [eventually_ge_atTop (max 1 (C / δ))] with u hu
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) hu)
  have hpow1 := Real.pow_div_factorial_le_exp (δ * u) (by positivity) 1
  rw [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hpow1
  have hexp : Real.exp (-δ * u) = (Real.exp (δ * u))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  have hge : C ≤ δ * u := by
    have : C / δ ≤ u := le_trans (le_max_right _ _) hu
    calc C = δ * (C / δ) := by field_simp [hδ.ne']
      _ ≤ δ * u := mul_le_mul_of_nonneg_left this hδ.le
  calc C * Real.exp (-δ * u)
      ≤ (δ * u) * (δ * u)⁻¹ := by
        rw [hexp]; exact mul_le_mul hge (inv_anti₀ (by positivity) hpow1)
          (inv_nonneg.mpr (Real.exp_pos _).le) (by positivity)
    _ = 1 := mul_inv_cancel₀ (by positivity)

private lemma joint_formal_to_lateral_zero {K r : ℕ}
    {φ : Fin K → ℂ → ℂ} {Up Um : Set ℂ} {θ : ℝ}
    (hUp_dom : Domain Up) (hUm_dom : Domain Um)
    (hrayP : ContainsRay Up (dPlusJ θ)) (hrayM : ContainsRay Um (dMinusJ θ))
    (hgoodP : ∀ i : Fin K, (aPhiJ (φ i)).Good Up (dPlusJ θ))
    (hgoodM : ∀ i : Fin K, (aPhiJ (φ i)).Good Um (dMinusJ θ))
    (hreP : 0 < (dPlusJ θ).re) (hreM : 0 < (dMinusJ θ).re)
    (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hP : jointFormalEvalPoly (fun i => formalSeries (φ i)) P = 0) :
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fun t : ℝ => (aPhiJ (φ ij.1)).value (dPlusJ θ) (t : ℂ)) u)
        (jointEvalU P (u : ℂ)) = 0) ∧
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fun t : ℝ => (aPhiJ (φ ij.1)).value (dMinusJ θ) (t : ℂ)) u)
        (jointEvalU P (u : ℂ)) = 0) := by
  let N := maxUDegJ P
  let Q := revMvPolyJ N P
  have hNP : ∀ α, (P.coeff α).natDegree ≤ N := natDegree_le_maxUDegJ P
  have hQ0 : jointFormalEvalW (fun i => formalSeries (φ i)) Q = 0 :=
    (jointFormalEvalW_eq_zero_iff_poly _ _ hNP).mpr hP
  obtain ⟨e, hs, he⟩ := JointBorelExpr.exists_of_mvPolynomial Q
  have hres_series : (e.residual (fun i => aPhiJ (φ i))).toSeries = 0 := by
    rw [hs Up (dPlusJ θ) (fun i => aPhiJ (φ i)) hUp_dom hrayP hgoodP]
    simpa only [aPhiJ_toSeries] using hQ0
  have hatom : (e.residual (fun i => aPhiJ (φ i))).atom = 0 := by
    have := congrArg (PowerSeries.coeff 0) hres_series
    simpa [Minor.toSeries] using this
  have hderiv_zero : ∀ k : ℕ, iteratedDeriv k (e.residual (fun i => aPhiJ (φ i))).density 0 = 0 := by
    intro k
    have := congrArg (PowerSeries.coeff (k + 1)) hres_series
    simpa [Minor.toSeries] using this
  have h0Up : (0 : ℂ) ∈ Up := by simpa using hrayP 0 le_rfl
  have h0Um : (0 : ℂ) ∈ Um := by simpa using hrayM 0 le_rfl
  have hplus_dens : EqOn (e.residual (fun i => aPhiJ (φ i))).density 0 Up :=
    analyticAt_eqOn_zero_of_iteratedDeriv_zeroJ
      (isPreconnected_of_starJ h0Up hUp_dom.star) h0Up
      (e.represents hUp_dom hrayP hgoodP).1.1 hderiv_zero
  have hminus_dens : EqOn (e.residual (fun i => aPhiJ (φ i))).density 0 Um :=
    analyticAt_eqOn_zero_of_iteratedDeriv_zeroJ
      (isPreconnected_of_starJ h0Um hUm_dom.star) h0Um
      (e.represents hUm_dom hrayM hgoodM).1.1 hderiv_zero
  constructor
  · have hrep := (tendsto_coe_farJ hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
    filter_upwards [hrep, he Up (dPlusJ θ) (fun i => aPhiJ (φ i)) hUp_dom hrayP hgoodP hreP,
      eventually_gt_atTop (0 : ℝ)] with u hu_rep hu_ev hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hevalQ : MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fun t : ℝ => (aPhiJ (φ ij.1)).value (dPlusJ θ) (t : ℂ)) u)
        (jointEvalU Q (u : ℂ)⁻¹) = 0 := by
      rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      have hd0 : (e.residual (fun i => aPhiJ (φ i))).density (dPlusJ θ * (v : ℂ)) = 0 :=
        hplus_dens (hrayP v hv.le)
      rw [damped, Minor.pull, hd0, mul_zero, mul_zero]
    rw [show Q = revMvPolyJ N P from rfl, jointEvalU_revMvPolyJ P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C] at hevalQ
    exact (mul_eq_zero.mp hevalQ).resolve_left (pow_ne_zero N (inv_ne_zero hu_ne))
  · have hrep := (tendsto_coe_farJ hreM).eventually (e.represents hUm_dom hrayM hgoodM).2
    filter_upwards [hrep, he Um (dMinusJ θ) (fun i => aPhiJ (φ i)) hUm_dom hrayM hgoodM hreM,
      eventually_gt_atTop (0 : ℝ)] with u hu_rep hu_ev hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hevalQ : MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fun t : ℝ => (aPhiJ (φ ij.1)).value (dMinusJ θ) (t : ℂ)) u)
        (jointEvalU Q (u : ℂ)⁻¹) = 0 := by
      rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      have hd0 : (e.residual (fun i => aPhiJ (φ i))).density (dMinusJ θ * (v : ℂ)) = 0 :=
        hminus_dens (hrayM v hv.le)
      rw [damped, Minor.pull, hd0, mul_zero, mul_zero]
    rw [show Q = revMvPolyJ N P from rfl, jointEvalU_revMvPolyJ P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C] at hevalQ
    exact (mul_eq_zero.mp hevalQ).resolve_left (pow_ne_zero N (inv_ne_zero hu_ne))

private lemma joint_flat_to_formal_zero {K r : ℕ}
    {φ : Fin K → ℂ → ℂ} {Up : Set ℂ} {θ δ : ℝ}
    (hUp_dom : Domain Up) (hrayP : ContainsRay Up (dPlusJ θ))
    (hgoodP : ∀ i : Fin K, (aPhiJ (φ i)).Good Up (dPlusJ θ))
    (hreP : 0 < (dPlusJ θ).re) (hδ : 0 < δ)
    (Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hQ : ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fun t : ℝ => (aPhiJ (φ ij.1)).value (dPlusJ θ) (t : ℂ)) u)
        (jointEvalU Q (u : ℂ))‖ ≤ C * Real.exp (-δ * u)) :
    jointFormalEvalPoly (fun i => formalSeries (φ i)) Q = 0 := by
  obtain ⟨C, hC⟩ := hQ
  let N := maxUDegJ Q
  let Qrev := revMvPolyJ N Q
  have hNQ : ∀ α, (Q.coeff α).natDegree ≤ N := natDegree_le_maxUDegJ Q
  obtain ⟨e, hs, he⟩ := JointBorelExpr.exists_of_mvPolynomial Qrev
  have hrep := (tendsto_coe_farJ hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
  have hflat : ∀ M : ℕ, ∃ C_M : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖(e.residual (fun i => aPhiJ (φ i))).value (dPlusJ θ) (u : ℂ)‖ ≤ C_M / u ^ (M + 1) := by
    intro M
    refine ⟨max C 0 * (((M + 1).factorial : ℝ) / δ ^ (M + 1)), ?_⟩
    filter_upwards [hC, hrep, he Up (dPlusJ θ) (fun i => aPhiJ (φ i)) hUp_dom hrayP hgoodP hreP,
      eventually_ge_atTop (1 : ℝ)] with u huC hurep huev hu1
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hinv_le1 : ‖(u : ℂ)⁻¹ ^ N‖ ≤ 1 := by
      rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu1)
    rw [← hurep, huev, show Qrev = revMvPolyJ N Q from rfl, jointEvalU_revMvPolyJ Q hNQ hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, norm_mul]
    have hexp : Real.exp (-δ * u) ≤ ((M + 1).factorial : ℝ) / (δ ^ (M + 1) * u ^ (M + 1)) := by
      have harg := Real.pow_div_factorial_le_exp (δ * u) (by positivity) (M + 1)
      have hfac : 0 < ((M + 1).factorial : ℝ) := by positivity
      have hpow : 0 < (δ * u) ^ (M + 1) := pow_pos (by positivity) (M + 1)
      calc Real.exp (-δ * u) = (Real.exp (δ * u))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
        _ ≤ ((δ * u) ^ (M + 1) / ((M + 1).factorial : ℝ))⁻¹ := inv_anti₀ (div_pos hpow hfac) harg
        _ = ((M + 1).factorial : ℝ) / (δ ^ (M + 1) * u ^ (M + 1)) := by rw [inv_div, mul_pow]
    calc ‖(u : ℂ)⁻¹ ^ N‖ * ‖MvPolynomial.eval _ (jointEvalU Q (u : ℂ))‖
        ≤ 1 * (C * Real.exp (-δ * u)) := mul_le_mul hinv_le1 huC (norm_nonneg _) zero_le_one
      _ ≤ max C 0 * Real.exp (-δ * u) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
      _ ≤ max C 0 * (((M + 1).factorial : ℝ) / (δ ^ (M + 1) * u ^ (M + 1))) :=
          mul_le_mul_of_nonneg_left hexp (le_max_right C 0)
      _ = (max C 0 * (((M + 1).factorial : ℝ) / δ ^ (M + 1))) / u ^ (M + 1) := by ring
  have hzero := Minor.toSeries_eq_zero_of_flat (e.residual (fun i => aPhiJ (φ i))) hUp_dom hrayP
    (e.represents hUp_dom hrayP hgoodP).1 hreP hflat
  rw [hs Up (dPlusJ θ) (fun i => aPhiJ (φ i)) hUp_dom hrayP hgoodP] at hzero
  have hzero' : jointFormalEvalW (fun i => formalSeries (φ i)) Qrev = 0 := by
    simpa only [aPhiJ_toSeries] using hzero
  exact (jointFormalEvalW_eq_zero_iff_poly _ _ hNQ).mp hzero'

private lemma joint_lateral_bounded_deriv {φ : ℂ → ℂ} {Up : Set ℂ} {θ : ℝ}
    (hUp_dom : Domain Up) (hrayP : ContainsRay Up (dPlusJ θ))
    (hgoodP : (aPhiJ φ).Good Up (dPlusJ θ)) (hreP : 0 < (dPlusJ θ).re) (j : ℕ) :
    ∃ B : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u‖ ≤ B := by
  let e := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have ha := (e.represents hUp_dom hrayP hgoodP).1
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := Minor.value_asymptotic (e.residual (aPhiJ φ)) hUp_dom hrayP ha hreP 0
  have hrep := (tendsto_coe_farJ hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
  have heq := (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ φ) hUp_dom hrayP hgoodP hreP j).1
  refine ⟨‖(e.residual (aPhiJ φ)).atom‖ + C₀, ?_⟩
  filter_upwards [hC₀, hrep, heq, eventually_ge_atTop (1 : ℝ)] with u hu0 hurep hueq hu1
  have heq' : iteratedDeriv j (fun t : ℝ => (aPhiJ φ).value (dPlusJ θ) (t : ℂ)) u =
      (e.residual (aPhiJ φ)).value (dPlusJ θ) (u : ℂ) := hueq.symm.trans hurep
  rw [heq']
  have hu0' : ‖(e.residual (aPhiJ φ)).value (dPlusJ θ) (u : ℂ) -
      (e.residual (aPhiJ φ)).atom‖ ≤ C₀ := by
    simpa using hu0.trans (div_le_self hC₀_nn (one_le_pow₀ hu1))
  calc ‖(e.residual (aPhiJ φ)).value (dPlusJ θ) (u : ℂ)‖
      = ‖((e.residual (aPhiJ φ)).value (dPlusJ θ) (u : ℂ) -
          (e.residual (aPhiJ φ)).atom) + (e.residual (aPhiJ φ)).atom‖ := by congr 1; ring
    _ ≤ ‖(e.residual (aPhiJ φ)).value (dPlusJ θ) (u : ℂ) -
          (e.residual (aPhiJ φ)).atom‖ + ‖(e.residual (aPhiJ φ)).atom‖ := norm_add_le _ _
    _ ≤ ‖(e.residual (aPhiJ φ)).atom‖ + C₀ := by linarith

private lemma exp_comb_rhs_le {CL Cr CT A u R lam δ : ℝ} {Du : ℕ}
    (hCL : 0 ≤ CL) (hCr : 0 ≤ Cr) (hCT : 0 ≤ CT) (hA : 0 < A)
    (h1 : u ^ Du * Real.exp (-R * u) ≤ Real.exp (-lam * u) * Real.exp (-(δ / 2) * u))
    (h2 : u ^ Du * Real.exp (-lam * u) ^ 2 ≤ Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) :
    (CL * Cr) * u ^ Du * Real.exp (-R * u) + CT * u ^ Du * (A ^ 2 * Real.exp (-lam * u) ^ 2) ≤
      (A * Real.exp (-lam * u)) * (((CL * Cr + CT * A ^ 2) / A) * Real.exp (-(δ / 2) * u)) := by
  have hcomb : (CL * Cr) * (u ^ Du * Real.exp (-R * u)) +
        (CT * A ^ 2) * (u ^ Du * Real.exp (-lam * u) ^ 2) ≤
      (CL * Cr + CT * A ^ 2) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) := by
    calc (CL * Cr) * (u ^ Du * Real.exp (-R * u)) +
          (CT * A ^ 2) * (u ^ Du * Real.exp (-lam * u) ^ 2)
        ≤ (CL * Cr) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) +
            (CT * A ^ 2) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (mul_nonneg hCL hCr))
            (mul_le_mul_of_nonneg_left h2 (mul_nonneg hCT (sq_nonneg A)))
      _ = (CL * Cr + CT * A ^ 2) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) := by ring
  have hL : (CL * Cr) * u ^ Du * Real.exp (-R * u) + CT * u ^ Du * (A ^ 2 * Real.exp (-lam * u) ^ 2) =
      (CL * Cr) * (u ^ Du * Real.exp (-R * u)) + (CT * A ^ 2) * (u ^ Du * Real.exp (-lam * u) ^ 2) := by ring
  have hR : (A * Real.exp (-lam * u)) * (((CL * Cr + CT * A ^ 2) / A) * Real.exp (-(δ / 2) * u)) =
      (CL * Cr + CT * A ^ 2) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) := by
    calc (A * Real.exp (-lam * u)) * (((CL * Cr + CT * A ^ 2) / A) * Real.exp (-(δ / 2) * u))
        = (A * ((CL * Cr + CT * A ^ 2) / A)) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) := by ring
      _ = (CL * Cr + CT * A ^ 2) * (Real.exp (-lam * u) * Real.exp (-(δ / 2) * u)) := by
            rw [mul_div_cancel₀ _ hA.ne']
  rw [hL, hR]; exact hcomb

set_option maxHeartbeats 3200000 in
/-- **Unrotated Multi-Function Simple-Pole Joint Differential Independence (`θ₀ = 0`, `ℂ[u]`)**:
Given `JointSimplePoleFamily K φ 0 ω res`, any joint polynomial ODE `P ∈ ℂ[u][Y_{i, j}]`
annihilating `(formalSeries (φ 0), ..., formalSeries (φ (K-1)))` must vanish identically. -/
theorem joint_stokes_vandermonde_no_ade_zero {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {ω : Fin K → ℕ → ℝ} {res : Fin K → ℕ → ℂ}
    (h : JointSimplePoleFamily K φ 0 ω res)
    {r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hP : jointFormalEvalPoly (fun i => formalSeries (φ i)) P = 0) : P = 0 := by
  classical
  cases K with
  | zero =>
    have h0 : P.totalDegree = 0 := by
      rw [MvPolynomial.totalDegree_eq]
      refine Nat.eq_zero_of_le_zero (Finset.sup_le fun α _ => ?_)
      have hα : α = 0 := Finsupp.ext fun ij => Fin.elim0 ij.1
      subst hα; simp
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    have hev0 : jointFormalEvalPoly (fun i => formalSeries (φ i))
        (MvPolynomial.C (P.coeff 0) : MvPolynomial (Fin 0 × Fin (r + 1)) (Polynomial ℂ)) = 0 := by
      rw [← hC]; exact hP
    have hp0 : polyToLaurent (P.coeff 0) = 0 := by simpa [jointFormalEvalPoly] using hev0
    have hc0 : P.coeff 0 = 0 := polyToLaurent_injectiveJ (hp0.trans (map_zero _).symm)
    exact hC.trans (by rw [hc0, map_zero])
  | succ K' =>
    let K := K' + 1
    by_contra hP_ne
    have hex : ∃ d : ℕ, ∃ Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ),
        Q.totalDegree = d ∧ Q ≠ 0 ∧ jointFormalEvalPoly (fun i => formalSeries (φ i)) Q = 0 :=
      ⟨P.totalDegree, P, rfl, hP_ne, hP⟩
    let Pmin := Classical.choose (Nat.find_spec hex)
    have hPmin_spec := Classical.choose_spec (Nat.find_spec hex)
    have hPmin_deg : Pmin.totalDegree = Nat.find hex := hPmin_spec.1
    have hPmin_ne : Pmin ≠ 0 := hPmin_spec.2.1
    have hPmin_zero : jointFormalEvalPoly (fun i => formalSeries (φ i)) Pmin = 0 := hPmin_spec.2.2
    have hPmin_min : ∀ Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ),
        Q ≠ 0 → Q.totalDegree < Pmin.totalDegree →
          ¬ jointFormalEvalPoly (fun i => formalSeries (φ i)) Q = 0 := by
      intro Q hQ_ne hQ_deg hQ_zero
      rw [hPmin_deg] at hQ_deg
      exact Nat.find_min hex hQ_deg ⟨Q, rfl, hQ_ne, hQ_zero⟩
    have hPmin_pos_deg : 0 < Pmin.totalDegree := by
      by_contra! hle
      have h0 : Pmin.totalDegree = 0 := Nat.eq_zero_of_le_zero hle
      have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
      have hev0 : jointFormalEvalPoly (fun i => formalSeries (φ i))
          (MvPolynomial.C (Pmin.coeff 0) : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) = 0 := by
        rw [← hC]; exact hPmin_zero
      have hp0 : polyToLaurent (Pmin.coeff 0) = 0 := by simpa [jointFormalEvalPoly] using hev0
      have hc0 : Pmin.coeff 0 = 0 := polyToLaurent_injectiveJ (hp0.trans (map_zero _).symm)
      exact hPmin_ne (hC.trans (by rw [hc0, map_zero]))
    -- Shared wedge setup
    have hα_pos : 0 < h.α₀ := h.hθ_pos.trans h.hθ_lt
    let ω0_min : ℝ := (Finset.univ : Finset (Fin K)).inf' Finset.univ_nonempty (fun i => ω i 0)
    have hω0_pos : 0 < ω0_min := (Finset.lt_inf'_iff _).mpr fun i _ => h.ω_pos i
    let ε₀ : ℝ := min h.ε (ω0_min / 2)
    have hε₀_pos : 0 < ε₀ := lt_min h.hε_pos (half_pos hω0_pos)
    have hε₀_le : ε₀ ≤ h.ε := min_le_left _ _
    have hε₀_lt : ∀ i : Fin K, ε₀ ≤ ω i 0 / 2 := fun i =>
      (min_le_right _ _).trans (div_le_div_of_nonneg_right
        (Finset.inf'_le (fun k => ω k 0) (Finset.mem_univ i)) (by norm_num))
    let Up := wedgePlusJ h.α₀ ε₀
    let Um := wedgeMinusJ h.α₀ ε₀
    have hUp_dom : Domain Up := wedgePlusJ_domain hε₀_pos
    have hUm_dom : Domain Um := wedgeMinusJ_domain hε₀_pos
    have hrayP : ContainsRay Up (dPlusJ h.θ) := wedgePlusJ_containsRay h.hθ_pos h.hθ_lt h.hα₀_lt hε₀_pos
    have hrayM : ContainsRay Um (dMinusJ h.θ) := wedgeMinusJ_containsRay h.hθ_pos h.hθ_lt h.hα₀_lt hε₀_pos
    have hcos : 0 < Real.cos h.θ := cos_pos_J h.hθ_pos h.hθ_lt h.hα₀_lt
    have hreP : 0 < (dPlusJ h.θ).re := by rw [dPlusJ_re]; exact hcos
    have hreM : 0 < (dMinusJ h.θ).re := by rw [dMinusJ_re]; exact hcos
    have hexpP : ∀ i : Fin K, ExpType (Minor.pull (dPlusJ h.θ) (φ i)) := fun i => by
      simpa [dPlusJ] using h.expType_plus i
    have hexpM : ∀ i : Fin K, ExpType (Minor.pull (dMinusJ h.θ) (φ i)) := fun i => by
      simpa [dMinusJ, neg_mul] using h.expType_minus i
    have hgoodP : ∀ i : Fin K, (aPhiJ (φ i)).Good Up (dPlusJ h.θ) := fun i =>
      ⟨(h.analyticOn i).mono (wedgePlusJ_subset_punctured hα_pos h.hα₀_lt hε₀_le (hε₀_lt i) (h.ω_pos i) (h.ω_mono i)),
       hexpP i⟩
    have hgoodM : ∀ i : Fin K, (aPhiJ (φ i)).Good Um (dMinusJ h.θ) := fun i =>
      ⟨(h.analyticOn i).mono (wedgeMinusJ_subset_punctured hα_pos h.hα₀_lt hε₀_le (hε₀_lt i) (h.ω_pos i) (h.ω_mono i)),
       hexpM i⟩
    let g_pos (i : Fin K) (t : ℝ) : ℂ := (aPhiJ (φ i)).value (dPlusJ h.θ) (t : ℂ)
    let g_neg (i : Fin K) (t : ℝ) : ℂ := (aPhiJ (φ i)).value (dMinusJ h.θ) (t : ℂ)
    have hPmin_lateral :=
      joint_formal_to_lateral_zero hUp_dom hUm_dom hrayP hrayM hgoodP hgoodM hreP hreM Pmin hPmin_zero
    have hflat_to_formal : ∀ {δ : ℝ}, 0 < δ →
        ∀ Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ),
        (∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
          ‖MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
            iteratedDeriv ij.2.val (g_pos ij.1) u) (jointEvalU Q (u : ℂ))‖ ≤ C * Real.exp (-δ * u)) →
        jointFormalEvalPoly (fun i => formalSeries (φ i)) Q = 0 :=
      fun hδ Q hQ => joint_flat_to_formal_zero hUp_dom hrayP hgoodP hreP hδ Q hQ
    have h_bg_each : ∀ ij : Fin K × Fin (r + 1), ∃ B : ℝ, ∀ᶠ u : ℝ in atTop,
        ‖iteratedDeriv ij.2.val (g_pos ij.1) u‖ ≤ B :=
      fun ij => joint_lateral_bounded_deriv hUp_dom hrayP (hgoodP ij.1) hreP ij.2.val
    -- Collect and sort all poles in the union up to B_top = max_i ω i r
    let B_top : ℝ := (Finset.univ : Finset (Fin K)).sup' Finset.univ_nonempty (fun i => ω i r)
    choose M_hi hM_hi using fun i : Fin K => h.ω_unbounded i B_top
    let poleSet : Finset (Fin K × ℕ) :=
      ((Finset.univ : Finset (Fin K)).biUnion fun i =>
        (Finset.range (M_hi i)).image fun m => (i, m)).filter (fun im => ω im.1 im.2 ≤ B_top)
    have hpoleSet_inj : Set.InjOn (fun im : Fin K × ℕ => ω im.1 im.2) (poleSet : Set (Fin K × ℕ)) := by
      intro a _ b _ hab
      by_cases hi : a.1 = b.1
      · have hm : a.2 = b.2 := (h.ω_mono a.1).injective (by simpa [hi] using hab)
        exact Prod.ext hi hm
      · exact absurd hab (h.ω_disjoint a.1 b.1 hi a.2 b.2)
    have hmem_poleSet : ∀ (i : Fin K) (m : ℕ), ω i m ≤ B_top → (i, m) ∈ poleSet := by
      intro i m hm
      refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i,
        Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr ?_, rfl⟩⟩, hm⟩
      exact (h.ω_mono i).lt_iff_lt.mp (lt_of_le_of_lt hm (hM_hi i))
    let valSet : Finset ℝ := poleSet.image (fun im => ω im.1 im.2)
    let N_poles : ℕ := valSet.card
    let lamEmb : Fin N_poles ↪o ℝ := valSet.orderEmbOfFin rfl
    have hlam_mem : ∀ n : Fin N_poles, lamEmb n ∈ valSet := fun n =>
      Finset.orderEmbOfFin_mem valSet rfl n
    -- For each n : Fin N_poles, pick its unique owner (i_n, m_n) ∈ poleSet
    choose owner howner_mem howner_eq using fun n : Fin N_poles =>
      Finset.mem_image.mp (hlam_mem n)
    -- Strong induction peeling off every pole in lamEmb 0 < lamEmb 1 < ... < lamEmb (N_poles - 1)
    have hD_peel : ∀ n : ℕ, (hn : n < N_poles) →
        D_joint K r (owner ⟨n, hn⟩).1 (ω (owner ⟨n, hn⟩).1 (owner ⟨n, hn⟩).2 : ℂ) Pmin = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | ind n ih =>
        intro hn
        let nFin : Fin N_poles := ⟨n, hn⟩
        let i₀ : Fin K := (owner nFin).1
        let m₀ : ℕ := (owner nFin).2
        let lam₀ : ℝ := lamEmb nFin
        have hlam₀_eq : ω i₀ m₀ = lam₀ := howner_eq nFin
        have hlam₀_pos : 0 < lam₀ := by
          rw [← hlam₀_eq]
          exact lt_of_lt_of_le (h.ω_pos i₀) ((h.ω_mono i₀).monotone (Nat.zero_le m₀))
        -- For every component i, find the first index M_cut i with lam₀ < ω i (M_cut i)
        let M_cut (i : Fin K) : ℕ := Nat.find (h.ω_unbounded i lam₀)
        have hM_above : ∀ i : Fin K, lam₀ < ω i (M_cut i) := fun i =>
          Nat.find_spec (h.ω_unbounded i lam₀)
        have hM_below : ∀ (i : Fin K) (m : ℕ), m < M_cut i → ω i m ≤ lam₀ := fun i m hm =>
          not_lt.mp (Nat.find_min (h.ω_unbounded i lam₀) hm)
        let nextMin : ℝ := (Finset.univ : Finset (Fin K)).inf' Finset.univ_nonempty
          (fun i => ω i (M_cut i))
        have hlam₀_lt_next : lam₀ < nextMin := (Finset.lt_inf'_iff _).mpr fun i _ => hM_above i
        let R_cut : ℝ := (lam₀ + nextMin) / 2
        have hlam₀_lt_R : lam₀ < R_cut := by dsimp only [R_cut]; linarith
        have hR_lt_next : ∀ i : Fin K, R_cut < ω i (M_cut i) := fun i => by
          have h1 : nextMin ≤ ω i (M_cut i) :=
            Finset.inf'_le (fun k => ω k (M_cut k)) (Finset.mem_univ i)
          dsimp only [R_cut]; linarith
        have hR_pos : 0 < R_cut := lt_trans hlam₀_pos hlam₀_lt_R
        have hM_lt_R : ∀ (i : Fin K) (m : ℕ), m < M_cut i → ω i m < R_cut := fun i m hm =>
          lt_of_le_of_lt (hM_below i m hm) hlam₀_lt_R
        -- Characterize every pole (i, m) with m < M_cut i: either (i, m) = (i₀, m₀) or ω i m < lam₀ (already peeled!)
        have h_strict_lt_peeled : ∀ (i : Fin K) (m : ℕ), ω i m < lam₀ →
            D_joint K r i (ω i m : ℂ) Pmin = 0 := by
          intro i m hlt
          have hle_top : ω i m ≤ B_top :=
            le_trans hlt.le ((Finset.mem_filter.mp (howner_mem nFin)).2 |> fun hle => hlam₀_eq ▸ hle)
          have hmem_val : ω i m ∈ valSet :=
            Finset.mem_image.mpr ⟨(i, m), hmem_poleSet i m hle_top, rfl⟩
          have hrange : Set.range lamEmb = (valSet : Set ℝ) := Finset.range_orderEmbOfFin valSet rfl
          obtain ⟨kFin, hk_eq⟩ : ∃ k : Fin N_poles, lamEmb k = ω i m := by
            have : ω i m ∈ Set.range lamEmb := hrange.symm ▸ Finset.mem_coe.mpr hmem_val
            exact this
          have hk_lt : kFin.val < n := by
            have hlt' : lamEmb kFin < lamEmb nFin := by rw [hk_eq]; exact hlt
            exact lamEmb.lt_iff_lt.mp hlt'
          have hown_eq : owner kFin = (i, m) :=
            hpoleSet_inj (howner_mem kFin) (hmem_poleSet i m hle_top) ((howner_eq kFin).trans hk_eq)
          have hpeel := ih kFin.val hk_lt kFin.isLt
          have hfin_eq : (⟨kFin.val, kFin.isLt⟩ : Fin N_poles) = kFin := Fin.eta kFin kFin.isLt
          rw [hfin_eq, hown_eq] at hpeel
          exact hpeel
        -- Note m₀ < M_cut i₀ and for i ≠ i₀ every m < M_cut i has ω i m < lam₀
        have hm₀_lt : m₀ < M_cut i₀ := by
          have : ω i₀ m₀ < ω i₀ (M_cut i₀) := by rw [hlam₀_eq]; exact hM_above i₀
          exact (h.ω_mono i₀).lt_iff_lt.mp this
        have h_other_lt : ∀ (i : Fin K) (m : ℕ), m < M_cut i → (i, m) ≠ (i₀, m₀) → ω i m < lam₀ := by
          intro i m hm hne
          refine lt_of_le_of_ne (hM_below i m hm) ?_
          intro heq
          apply hne
          by_cases hi : i = i₀
          · subst hi
            exact Prod.ext rfl ((h.ω_mono i₀).injective (heq.trans hlam₀_eq.symm))
          · exact absurd (heq.trans hlam₀_eq.symm) (h.ω_disjoint i i₀ hi m m₀)
        -- Shift invariance of jointEvalU Pmin u along any earlier pole (i, m) with ω i m < lam₀
        have h_shift_one : ∀ (u : ℝ) (i : Fin K) (m : ℕ), ω i m < lam₀ →
            ∀ (x : Fin K × Fin (r + 1) → ℂ) (a : ℂ),
            MvPolynomial.eval
              (fun ij => x ij + if ij.1 = i then a * (-(ω i m : ℂ)) ^ ij.2.val else 0)
              (jointEvalU Pmin (u : ℂ)) =
            MvPolynomial.eval x (jointEvalU Pmin (u : ℂ)) := by
          intro u i m hlt x a
          let v : Fin K × Fin (r + 1) → ℂ := fun ij =>
            if ij.1 = i then (-(ω i m : ℂ)) ^ ij.2.val else 0
          have hv_zero : ∑ ij : Fin K × Fin (r + 1),
              v ij • MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ)) = 0 := by
            rw [Fintype.sum_prod_type]
            have hinner : ∀ i' : Fin K,
                (∑ j : Fin (r + 1), v (i', j) • MvPolynomial.pderiv (i', j) (jointEvalU Pmin (u : ℂ))) =
                  if i' = i then jointEvalU (D_joint K r i (ω i m : ℂ) Pmin) (u : ℂ) else 0 := by
              intro i'
              by_cases h' : i' = i
              · subst h'
                rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), jointEvalU_D_joint]
                refine Finset.sum_congr rfl fun j _ => by simp [v]
              · rw [ite_eq_right_iff.mpr (fun h => absurd h h')]
                exact Finset.sum_eq_zero fun j _ => by simp [v, h']
            simp_rw [hinner]
            simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
              h_strict_lt_peeled i m hlt, jointEvalU, map_zero]
          have hsh := shift_invariant_any v (jointEvalU Pmin (u : ℂ)) hv_zero x a
          simpa only [v, mul_ite, mul_zero] using hsh
        -- Shift invariance for ANY finite set of earlier poles (i, m)
        let earlierPoles : Finset (Fin K × ℕ) :=
          ((Finset.univ : Finset (Fin K)).biUnion fun i =>
            (Finset.range (M_cut i)).image fun m => (i, m)).filter (fun im => im ≠ (i₀, m₀))
        have h_shift_finset : ∀ (s : Finset (Fin K × ℕ)), s ⊆ earlierPoles →
            ∀ (u : ℝ) (x : Fin K × Fin (r + 1) → ℂ) (c : Fin K × ℕ → ℂ),
            MvPolynomial.eval
              (fun ij => x ij + ∑ p ∈ s, if ij.1 = p.1 then c p * (-(ω p.1 p.2 : ℂ)) ^ ij.2.val else 0)
              (jointEvalU Pmin (u : ℂ)) =
            MvPolynomial.eval x (jointEvalU Pmin (u : ℂ)) := by
          intro s hs u x c
          induction s using Finset.induction_on generalizing x with
          | empty => simp
          | @insert p s hp ih =>
            have hp_mem : p ∈ earlierPoles := hs (Finset.mem_insert_self p s)
            have hs_sub : s ⊆ earlierPoles := fun q hq => hs (Finset.mem_insert_of_mem hq)
            have hp_ne : p ≠ (i₀, m₀) := (Finset.mem_filter.mp hp_mem).2
            obtain ⟨i, _, hm_img⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hp_mem).1
            obtain ⟨m, hm_rng, hpm⟩ := Finset.mem_image.mp hm_img
            have hp_lt : ω p.1 p.2 < lam₀ := by
              rw [← hpm]; exact h_other_lt i m (Finset.mem_range.mp hm_rng) (hpm ▸ hp_ne)
            have hrew : (fun ij : Fin K × Fin (r + 1) =>
                x ij + ∑ q ∈ insert p s, if ij.1 = q.1 then c q * (-(ω q.1 q.2 : ℂ)) ^ ij.2.val else 0) =
                fun ij => (x ij + ∑ q ∈ s, if ij.1 = q.1 then c q * (-(ω q.1 q.2 : ℂ)) ^ ij.2.val else 0) +
                  if ij.1 = p.1 then c p * (-(ω p.1 p.2 : ℂ)) ^ ij.2.val else 0 := by
              funext ij; rw [Finset.sum_insert hp]; ring
            rw [hrew, h_shift_one u p.1 p.2 hp_lt _ (c p), ih hs_sub]
        -- Assemble Stokes jump expansions at cut R_cut for every (i, j)
        choose Cexp h_exp_ev using fun ij : Fin K × Fin (r + 1) =>
          simplePole_stokes_jump_at_cut (φ := φ ij.1) (ω := ω ij.1) (res := res ij.1)
            (α₀ := h.α₀) (θ := h.θ) (ε := h.ε) (ε₀ := ε₀) (R := R_cut) (M := M_cut ij.1)
            h.hθ_pos h.hθ_lt h.hα₀_lt hε₀_pos hε₀_le (hε₀_lt ij.1) (h.ω_pos ij.1) (h.ω_mono ij.1)
            (h.analyticOn ij.1) (fun m => by simpa using h.pole_res ij.1 m) (hexpP ij.1) (hexpM ij.1)
            hR_pos (hM_lt_R ij.1) (hR_lt_next ij.1) ij.2.val
        have h_all_exp : ∀ᶠ u : ℝ in atTop, ∀ ij : Fin K × Fin (r + 1),
            ‖iteratedDeriv ij.2.val (fun t : ℝ => g_neg ij.1 t - g_pos ij.1 t) u -
              ∑ m ∈ Finset.range (M_cut ij.1),
                (2 * (Real.pi : ℂ) * I * res ij.1 m * (-(ω ij.1 m : ℂ)) ^ ij.2.val) *
                  Complex.exp (-(ω ij.1 m : ℂ) * (u : ℂ))‖ ≤
              Cexp ij * Real.exp (-R_cut * u) :=
          Filter.eventually_all.mpr h_exp_ev
        have h_all_sub : ∀ᶠ u : ℝ in atTop, ∀ ij : Fin K × Fin (r + 1),
            iteratedDeriv ij.2.val (fun t : ℝ => g_neg ij.1 t - g_pos ij.1 t) u =
              iteratedDeriv ij.2.val (g_neg ij.1) u - iteratedDeriv ij.2.val (g_pos ij.1) u :=
          Filter.eventually_all.mpr fun ij =>
            eventually_iteratedDeriv_sub
              (fun k _ => (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ (φ ij.1)) hUm_dom hrayM (hgoodM ij.1) hreM k).2)
              (fun k _ => (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiJ (φ ij.1)) hUp_dom hrayP (hgoodP ij.1) hreP k).2)
        choose Bg hBg using h_bg_each
        have h_all_bg : ∀ᶠ u : ℝ in atTop, ∀ ij : Fin K × Fin (r + 1),
            ‖iteratedDeriv ij.2.val (g_pos ij.1) u‖ ≤ Bg ij :=
          Filter.eventually_all.mpr hBg
        -- Bounds for Taylor & Lipschitz estimates
        let amp₀ : ℂ := 2 * (Real.pi : ℂ) * I * res i₀ m₀
        have hamp₀_ne : amp₀ ≠ 0 := by
          have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
          exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero) (h.res_ne_zero i₀ m₀)
        let v_dir : Fin K × Fin (r + 1) → ℂ := fun ij =>
          if ij.1 = i₀ then (-(ω i₀ m₀ : ℂ)) ^ ij.2.val else 0
        let M_v : ℝ := ∑ ij : Fin K × Fin (r + 1), ‖v_dir ij‖
        let M_box : ℝ := 2 + (∑ ij : Fin K × Fin (r + 1), |Bg ij|) + M_v
        have hM_nn : 0 ≤ M_box := by
          have h1 : 0 ≤ ∑ ij : Fin K × Fin (r + 1), |Bg ij| := Finset.sum_nonneg fun _ _ => abs_nonneg _
          have h2 : 0 ≤ M_v := Finset.sum_nonneg fun _ _ => norm_nonneg _
          dsimp only [M_box]; linarith
        have hBg_le : ∀ ij, |Bg ij| + 2 ≤ M_box := fun ij => by
          have h1 : |Bg ij| ≤ ∑ p : Fin K × Fin (r + 1), |Bg p| :=
            Finset.single_le_sum (f := fun p => |Bg p|) (fun _ _ => abs_nonneg _) (Finset.mem_univ ij)
          have h2 : 0 ≤ M_v := Finset.sum_nonneg fun _ _ => norm_nonneg _
          dsimp only [M_box]; linarith
        have hv_le : ∀ ij, ‖v_dir ij‖ ≤ M_box := fun ij => by
          have h1 : 0 ≤ ∑ p : Fin K × Fin (r + 1), |Bg p| := Finset.sum_nonneg fun _ _ => abs_nonneg _
          have h2 : ‖v_dir ij‖ ≤ M_v :=
            Finset.single_le_sum (f := fun p => ‖v_dir p‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ ij)
          dsimp only [M_box]; linarith
        let C_rem : ℝ := ∑ ij : Fin K × Fin (r + 1), max (Cexp ij) 0
        have hC_rem_nn : 0 ≤ C_rem := Finset.sum_nonneg fun _ _ => le_max_right _ _
        let Du : ℕ := maxUDegJ Pmin
        choose C_lip_k hC_lip_k h_lip_k using fun k : ℕ => eval_lipschitz_of_bounded (coeffUJ k Pmin) hM_nn
        choose C_tay_k hC_tay_k h_tay_k using fun k : ℕ => eval_shift_taylor_bound_any (coeffUJ k Pmin) hM_nn
        let C_L : ℝ := ∑ k ∈ Finset.range (Du + 1), C_lip_k k
        let C_T : ℝ := ∑ k ∈ Finset.range (Du + 1), C_tay_k k
        have hC_L_nn : 0 ≤ C_L := Finset.sum_nonneg fun k _ => hC_lip_k k
        have hC_T_nn : 0 ≤ C_T := Finset.sum_nonneg fun k _ => hC_tay_k k
        let δ_gap : ℝ := min lam₀ (R_cut - lam₀)
        have hδ_pos : 0 < δ_gap := lt_min hlam₀_pos (by linarith)
        -- Eventual smallness of Stokes sums, remainder, and a = amp₀ * e^{-lam₀ u}
        have hS_small : ∀ᶠ u : ℝ in atTop, ∀ ij : Fin K × Fin (r + 1),
            ‖∑ m ∈ Finset.range (M_cut ij.1),
              (2 * (Real.pi : ℂ) * I * res ij.1 m * (-(ω ij.1 m : ℂ)) ^ ij.2.val) *
                Complex.exp (-(ω ij.1 m : ℂ) * (u : ℂ))‖ ≤ 1 := by
          refine Filter.eventually_all.mpr fun ij => ?_
          by_cases hM0 : M_cut ij.1 = 0
          · exact Filter.Eventually.of_forall fun _ => by simp [hM0]
          · have hM_pos : (0 : ℝ) < (M_cut ij.1 : ℝ) := by positivity
            have hterm : ∀ m ∈ Finset.range (M_cut ij.1), ∀ᶠ u : ℝ in atTop,
                ‖(2 * (Real.pi : ℂ) * I * res ij.1 m * (-(ω ij.1 m : ℂ)) ^ ij.2.val) *
                  Complex.exp (-(ω ij.1 m : ℂ) * (u : ℂ))‖ ≤ 1 / (M_cut ij.1 : ℝ) := by
              intro m _
              have hωm : 0 < ω ij.1 m := lt_of_lt_of_le (h.ω_pos ij.1) ((h.ω_mono ij.1).monotone (Nat.zero_le m))
              let C_m : ℝ := (M_cut ij.1 : ℝ) * ‖2 * (Real.pi : ℂ) * I * res ij.1 m * (-(ω ij.1 m : ℂ)) ^ ij.2.val‖
              filter_upwards [const_mul_exp_neg_le_oneJ hωm (by positivity : 0 ≤ C_m)] with u hu
              rw [norm_mul, Complex.norm_exp,
                show (-(ω ij.1 m : ℂ) * (u : ℂ)).re = -ω ij.1 m * u from by simp [Complex.mul_re] ]
              rw [le_div_iff₀' hM_pos]
              dsimp only [C_m] at hu; linarith
            filter_upwards [(Filter.eventually_all_finset (Finset.range (M_cut ij.1))).mpr hterm] with u hu
            calc ‖∑ m ∈ Finset.range (M_cut ij.1), _‖
                ≤ ∑ m ∈ Finset.range (M_cut ij.1), ‖_‖ := norm_sum_le _ _
              _ ≤ ∑ _m ∈ Finset.range (M_cut ij.1), (1 / (M_cut ij.1 : ℝ)) := Finset.sum_le_sum hu
              _ = 1 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div, mul_inv_cancel₀ hM_pos.ne']
        have ha_small : ∀ᶠ u : ℝ in atTop, ‖amp₀‖ * Real.exp (-lam₀ * u) ≤ 1 :=
          const_mul_exp_neg_le_oneJ hlam₀_pos (norm_nonneg amp₀)
        have hrem_small : ∀ᶠ u : ℝ in atTop, C_rem * Real.exp (-R_cut * u) ≤ 1 :=
          const_mul_exp_neg_le_oneJ hR_pos hC_rem_nn
        have hu_poly_exp : ∀ᶠ u : ℝ in atTop, u ^ Du * Real.exp (-(δ_gap / 2) * u) ≤ 1 :=
          pow_mul_exp_neg_le_oneJ Du (half_pos hδ_pos)
        -- Main bridge bound isolating D_joint K r i₀ lam₀ Pmin
        have h_bridge : ∀ᶠ u : ℝ in atTop,
            ‖MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (g_pos ij.1) u)
              (jointEvalU (D_joint K r i₀ (ω i₀ m₀ : ℂ) Pmin) (u : ℂ))‖ ≤
              ((C_L * C_rem + C_T * ‖amp₀‖ ^ 2) / ‖amp₀‖) * Real.exp (-(δ_gap / 2) * u) := by
          filter_upwards [h_all_bg, h_all_exp, h_all_sub, hPmin_lateral.1, hPmin_lateral.2,
            hS_small, ha_small, hrem_small, hu_poly_exp, eventually_ge_atTop (1 : ℝ)] with
            u hbg hexp hsub hpos hneg hS1 ha1 hrem1 hpoly_u hu1
          have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
          let x : Fin K × Fin (r + 1) → ℂ := fun ij => iteratedDeriv ij.2.val (g_pos ij.1) u
          let S : Fin K × Fin (r + 1) → ℂ := fun ij =>
            ∑ m ∈ Finset.range (M_cut ij.1),
              (2 * (Real.pi : ℂ) * I * res ij.1 m * (-(ω ij.1 m : ℂ)) ^ ij.2.val) *
                Complex.exp (-(ω ij.1 m : ℂ) * (u : ℂ))
          let y : Fin K × Fin (r + 1) → ℂ := fun ij => x ij + S ij
          let z : Fin K × Fin (r + 1) → ℂ := fun ij => iteratedDeriv ij.2.val (g_neg ij.1) u
          let a : ℂ := amp₀ * Complex.exp (-(lam₀ : ℂ) * (u : ℂ))
          have ha_norm : ‖a‖ = ‖amp₀‖ * Real.exp (-lam₀ * u) := by
            simp only [a, norm_mul, Complex.norm_exp,
              show (-(lam₀ : ℂ) * (u : ℂ)).re = -lam₀ * u from by simp [Complex.mul_re] ]
          have ha_le1 : ‖a‖ ≤ 1 := ha_norm ▸ ha1
          have hx_le : ∀ ij, ‖x ij‖ ≤ M_box := fun ij =>
            (hbg ij).trans ((le_abs_self _).trans (by linarith [hBg_le ij]))
          have hy_le : ∀ ij, ‖y ij‖ ≤ M_box := fun ij =>
            (norm_add_le _ _).trans ((add_le_add ((hbg ij).trans (le_abs_self _)) (hS1 ij)).trans (by linarith [hBg_le ij]))
          have hzy_le : ∀ ij, ‖z ij - y ij‖ ≤ C_rem * Real.exp (-R_cut * u) := fun ij => by
            have hsub_eq : z ij - y ij = iteratedDeriv ij.2.val (fun t => g_neg ij.1 t - g_pos ij.1 t) u - S ij := by
              rw [hsub ij]; simp only [y, x, z]; ring
            rw [hsub_eq]
            refine (hexp ij).trans ?_
            exact mul_le_mul_of_nonneg_right ((le_max_left _ _).trans
              (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ ij))) (Real.exp_pos _).le
          have hz_le : ∀ ij, ‖z ij‖ ≤ M_box := fun ij => by
            rw [show z ij = y ij + (z ij - y ij) by ring]
            exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans
              (add_le_add ((hbg ij).trans (le_abs_self _)) (hS1 ij))) ((hzy_le ij).trans hrem1)).trans
              (by linarith [hBg_le ij]))
          have hu_pow_le : ∀ k ∈ Finset.range (Du + 1), ‖(u : ℂ) ^ k‖ ≤ u ^ Du := fun k hk => by
            rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
            exact pow_le_pow_right₀ hu1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
          -- Split y = (x + a * v_dir) + (earlier poles sum), then apply h_shift_finset!
          have hy_eq : MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) =
              MvPolynomial.eval (fun ij => x ij + a * v_dir ij) (jointEvalU Pmin (u : ℂ)) := by
            let c_pole : Fin K × ℕ → ℂ := fun p =>
              2 * (Real.pi : ℂ) * I * res p.1 p.2 * Complex.exp (-(ω p.1 p.2 : ℂ) * (u : ℂ))
            have hy_split : y = fun ij => (x ij + a * v_dir ij) +
                ∑ p ∈ earlierPoles, if ij.1 = p.1 then c_pole p * (-(ω p.1 p.2 : ℂ)) ^ ij.2.val else 0 := by
              funext ij
              dsimp only [y, S, v_dir, a, amp₀, c_pole]
              have hsum_er : ∑ p ∈ earlierPoles,
                    (if ij.1 = p.1 then (2 * (Real.pi : ℂ) * I * res p.1 p.2 *
                      Complex.exp (-(ω p.1 p.2 : ℂ) * (u : ℂ))) * (-(ω p.1 p.2 : ℂ)) ^ ij.2.val else 0) =
                  ∑ m ∈ (Finset.range (M_cut ij.1)).filter (fun m => (ij.1, m) ≠ (i₀, m₀)),
                    (2 * (Real.pi : ℂ) * I * res ij.1 m * (-(ω ij.1 m : ℂ)) ^ ij.2.val) *
                      Complex.exp (-(ω ij.1 m : ℂ) * (u : ℂ)) := by
                rw [← Finset.sum_filter]
                refine Finset.sum_bij (fun p _ => p.2) ?_ ?_ ?_ ?_
                · intro p hp
                  have hp1 := Finset.mem_filter.mp hp
                  have hp2 := Finset.mem_filter.mp hp1.1
                  obtain ⟨i', _, hm_img⟩ := Finset.mem_biUnion.mp hp2.1
                  obtain ⟨m', hm_rng, hpm⟩ := Finset.mem_image.mp hm_img
                  have hi_eq : ij.1 = p.1 := hp1.2
                  rw [Finset.mem_filter, Finset.mem_range]
                  refine ⟨?_, ?_⟩
                  · rw [hi_eq, ← hpm]; exact Finset.mem_range.mp hm_rng
                  · rw [hi_eq]; exact hp2.2
                · intro p₁ hp₁ p₂ hp₂ h2
                  have h1 : p₁.1 = p₂.1 := ((Finset.mem_filter.mp hp₁).2).symm.trans (Finset.mem_filter.mp hp₂).2
                  exact Prod.ext h1 h2
                · intro m hm
                  have hm' := Finset.mem_filter.mp hm
                  refine ⟨(ij.1, m), ?_, rfl⟩
                  rw [Finset.mem_filter]
                  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨ij.1, Finset.mem_univ _,
                    Finset.mem_image.mpr ⟨m, hm'.1, rfl⟩⟩, hm'.2⟩, rfl⟩
                · intro p hp
                  have hi_eq : ij.1 = p.1 := (Finset.mem_filter.mp hp).2
                  rw [← hi_eq]; ring
              rw [hsum_er]
              by_cases hij : ij.1 = i₀
              · rw [hij, ite_eq_left_iff.mpr (fun h => absurd rfl h)]
                have hfilt : (Finset.range (M_cut i₀)).filter (fun m => (i₀, m) ≠ (i₀, m₀)) =
                    (Finset.range (M_cut i₀)).erase m₀ := by
                  ext m; simp [Finset.mem_erase, and_comm]
                rw [hfilt, ← hlam₀_eq]
                have hadd := Finset.add_sum_erase (Finset.range (M_cut i₀))
                  (fun m => (2 * (Real.pi : ℂ) * I * res i₀ m * (-(ω i₀ m : ℂ)) ^ ij.2.val) *
                    Complex.exp (-(ω i₀ m : ℂ) * (u : ℂ))) (Finset.mem_range.mpr hm₀_lt)
                rw [← hadd]; ring
              · rw [ite_eq_right_iff.mpr (fun h => absurd h hij), mul_zero, add_zero]
                have hfilt : (Finset.range (M_cut ij.1)).filter (fun m => (ij.1, m) ≠ (i₀, m₀)) =
                    Finset.range (M_cut ij.1) := by
                  ext m; simp [hij]
                rw [hfilt]
            rw [hy_split]
            exact h_shift_finset earlierPoles Subset.rfl u (fun ij => x ij + a * v_dir ij) c_pole
          have h_lip_y : ‖MvPolynomial.eval y (jointEvalU Pmin (u : ℂ))‖ ≤
              (C_L * C_rem) * u ^ Du * Real.exp (-R_cut * u) := by
            have hyz : MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) =
                ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                  (MvPolynomial.eval y (coeffUJ k Pmin) - MvPolynomial.eval z (coeffUJ k Pmin)) := by
              rw [← sub_zero (MvPolynomial.eval y (jointEvalU Pmin (u : ℂ))), ← hneg]
              dsimp only [Du]
              simp only [jointEvalU_eq_sum_coeffUJ Pmin (u : ℂ), map_sum, MvPolynomial.smul_eq_C_mul,
                map_mul, MvPolynomial.eval_C, ← Finset.sum_sub_distrib, ← mul_sub]
              rfl
            rw [hyz]
            calc ‖∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k * _‖
                ≤ ∑ k ∈ Finset.range (Du + 1), ‖(u : ℂ) ^ k * _‖ := norm_sum_le _ _
              _ ≤ ∑ k ∈ Finset.range (Du + 1), u ^ Du * (C_lip_k k * (C_rem * Real.exp (-R_cut * u))) := by
                  refine Finset.sum_le_sum fun k hk => ?_
                  rw [norm_mul]
                  have hlk := h_lip_k k z y (C_rem * Real.exp (-R_cut * u))
                    (mul_nonneg hC_rem_nn (Real.exp_pos _).le) hz_le hy_le hzy_le
                  rw [norm_sub_rev] at hlk
                  exact mul_le_mul (hu_pow_le k hk) hlk (norm_nonneg _) (pow_nonneg hu_pos.le Du)
              _ = (C_L * C_rem) * u ^ Du * Real.exp (-R_cut * u) := by
                  dsimp only [C_L]; rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
          have h_tay_y :
              ‖MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) -
                  a * ∑ ij : Fin K × Fin (r + 1),
                    MvPolynomial.eval x (MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ))) * v_dir ij‖ ≤
                C_T * u ^ Du * ‖a‖ ^ 2 := by
            have hsum_id : MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) -
                  a * ∑ ij : Fin K × Fin (r + 1),
                    MvPolynomial.eval x (MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ))) * v_dir ij =
                ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                  (MvPolynomial.eval (fun ij => x ij + a * v_dir ij) (coeffUJ k Pmin) -
                    MvPolynomial.eval x (coeffUJ k Pmin) -
                    a * ∑ ij : Fin K × Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv ij (coeffUJ k Pmin)) * v_dir ij) := by
              rw [hy_eq, ← sub_zero (MvPolynomial.eval (fun ij => x ij + a * v_dir ij) (jointEvalU Pmin (u : ℂ))), ← hpos]
              have hpd_u : ∑ ij : Fin K × Fin (r + 1),
                    MvPolynomial.eval x (MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ))) * v_dir ij =
                  ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                    ∑ ij : Fin K × Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv ij (coeffUJ k Pmin)) * v_dir ij := by
                have hexp_ij : ∀ ij : Fin K × Fin (r + 1),
                    MvPolynomial.eval x (MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ))) * v_dir ij =
                      ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                        (MvPolynomial.eval x (MvPolynomial.pderiv ij (coeffUJ k Pmin)) * v_dir ij) := by
                  intro ij
                  rw [jointEvalU_eq_sum_coeffUJ Pmin (u : ℂ), map_sum, map_sum, Finset.sum_mul]
                  refine Finset.sum_congr rfl fun k _ => by
                    rw [(MvPolynomial.pderiv ij).map_smul_of_tower, MvPolynomial.smul_eq_C_mul,
                      map_mul, MvPolynomial.eval_C, mul_assoc]
                simp_rw [hexp_ij]; rw [Finset.sum_comm]
                exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
              rw [hpd_u, Finset.mul_sum]
              dsimp only [Du]
              simp only [jointEvalU_eq_sum_coeffUJ Pmin (u : ℂ), map_sum, MvPolynomial.smul_eq_C_mul,
                map_mul, MvPolynomial.eval_C, ← Finset.sum_sub_distrib]
              exact Finset.sum_congr rfl fun k _ => by ring
            rw [hsum_id]
            calc ‖∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k * _‖
                ≤ ∑ k ∈ Finset.range (Du + 1), ‖(u : ℂ) ^ k * _‖ := norm_sum_le _ _
              _ ≤ ∑ k ∈ Finset.range (Du + 1), u ^ Du * (C_tay_k k * ‖a‖ ^ 2) := by
                  refine Finset.sum_le_sum fun k hk => ?_
                  rw [norm_mul]
                  exact mul_le_mul (hu_pow_le k hk) (h_tay_k k x v_dir a hx_le hv_le ha_le1)
                    (norm_nonneg _) (pow_nonneg hu_pos.le Du)
              _ = C_T * u ^ Du * ‖a‖ ^ 2 := by dsimp only [C_T]; rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
          have hD_rew : ∑ ij : Fin K × Fin (r + 1),
                MvPolynomial.eval x (MvPolynomial.pderiv ij (jointEvalU Pmin (u : ℂ))) * v_dir ij =
              MvPolynomial.eval x (jointEvalU (D_joint K r i₀ (ω i₀ m₀ : ℂ) Pmin) (u : ℂ)) := by
            rw [Fintype.sum_prod_type, jointEvalU_D_joint, map_sum]
            have hinner : ∀ i' : Fin K,
                (∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv (i', j) (jointEvalU Pmin (u : ℂ))) * v_dir (i', j)) =
                  if i' = i₀ then ∑ j : Fin (r + 1),
                    MvPolynomial.eval x (((-(ω i₀ m₀ : ℂ)) ^ j.val) • MvPolynomial.pderiv (i₀, j) (jointEvalU Pmin (u : ℂ)))
                  else 0 := by
              intro i'
              by_cases h' : i' = i₀
              · subst h'
                rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
                refine Finset.sum_congr rfl fun j _ => ?_
                dsimp only [v_dir]
                rw [ite_eq_left_iff.mpr (fun h => absurd rfl h), MvPolynomial.smul_eq_C_mul,
                  map_mul, MvPolynomial.eval_C, mul_comm]
              · rw [ite_eq_right_iff.mpr (fun h => absurd h h')]
                refine Finset.sum_eq_zero fun j _ => ?_
                dsimp only [v_dir]
                rw [ite_eq_right_iff.mpr (fun h => absurd h h'), mul_zero]
            simp_rw [hinner]
            simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
          rw [hD_rew] at h_tay_y
          have h_main : ‖a‖ * ‖MvPolynomial.eval x (jointEvalU (D_joint K r i₀ (ω i₀ m₀ : ℂ) Pmin) (u : ℂ))‖ ≤
              (C_L * C_rem) * u ^ Du * Real.exp (-R_cut * u) + C_T * u ^ Du * ‖a‖ ^ 2 := by
            have htri := norm_sub_le (MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)))
              (MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) -
                a * MvPolynomial.eval x (jointEvalU (D_joint K r i₀ (ω i₀ m₀ : ℂ) Pmin) (u : ℂ)))
            have hsimp : MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) -
                (MvPolynomial.eval y (jointEvalU Pmin (u : ℂ)) -
                  a * MvPolynomial.eval x (jointEvalU (D_joint K r i₀ (ω i₀ m₀ : ℂ) Pmin) (u : ℂ))) =
                a * MvPolynomial.eval x (jointEvalU (D_joint K r i₀ (ω i₀ m₀ : ℂ) Pmin) (u : ℂ)) := by ring
            rw [hsimp, norm_mul] at htri
            exact htri.trans (add_le_add h_lip_y h_tay_y)
          have h1_bd : u ^ Du * Real.exp (-R_cut * u) ≤ Real.exp (-lam₀ * u) * Real.exp (-(δ_gap / 2) * u) := by
            have hle : lam₀ + δ_gap ≤ R_cut := by have := min_le_right lam₀ (R_cut - lam₀); linarith
            have hexp_cut : Real.exp (-R_cut * u) ≤ Real.exp (-(lam₀ + δ_gap) * u) :=
              Real.exp_le_exp.mpr (by nlinarith [hu_pos.le])
            have hexp_eq : Real.exp (-(lam₀ + δ_gap) * u) =
                Real.exp (-lam₀ * u) * (Real.exp (-(δ_gap / 2) * u) * Real.exp (-(δ_gap / 2) * u)) := by
              rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
            calc u ^ Du * Real.exp (-R_cut * u)
                ≤ u ^ Du * Real.exp (-(lam₀ + δ_gap) * u) := mul_le_mul_of_nonneg_left hexp_cut (pow_nonneg hu_pos.le _)
              _ = Real.exp (-lam₀ * u) * ((u ^ Du * Real.exp (-(δ_gap / 2) * u)) * Real.exp (-(δ_gap / 2) * u)) := by
                  rw [hexp_eq]; ring
              _ ≤ Real.exp (-lam₀ * u) * (1 * Real.exp (-(δ_gap / 2) * u)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le) (Real.exp_pos _).le
              _ = Real.exp (-lam₀ * u) * Real.exp (-(δ_gap / 2) * u) := by rw [one_mul]
          have h2_bd : u ^ Du * Real.exp (-lam₀ * u) ^ 2 ≤ Real.exp (-lam₀ * u) * Real.exp (-(δ_gap / 2) * u) := by
            have hle : δ_gap ≤ lam₀ := min_le_left _ _
            have hexp_om : Real.exp (-lam₀ * u) ≤ Real.exp (-δ_gap * u) :=
              Real.exp_le_exp.mpr (by nlinarith [hu_pos.le])
            have hexp_eq : Real.exp (-δ_gap * u) =
                Real.exp (-(δ_gap / 2) * u) * Real.exp (-(δ_gap / 2) * u) := by
              rw [← Real.exp_add]; congr 1; ring
            calc u ^ Du * Real.exp (-lam₀ * u) ^ 2
                = Real.exp (-lam₀ * u) * (u ^ Du * Real.exp (-lam₀ * u)) := by ring
              _ ≤ Real.exp (-lam₀ * u) * (u ^ Du * Real.exp (-δ_gap * u)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_om (pow_nonneg hu_pos.le _)) (Real.exp_pos _).le
              _ = Real.exp (-lam₀ * u) * ((u ^ Du * Real.exp (-(δ_gap / 2) * u)) * Real.exp (-(δ_gap / 2) * u)) := by
                  rw [hexp_eq]; ring
              _ ≤ Real.exp (-lam₀ * u) * (1 * Real.exp (-(δ_gap / 2) * u)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le) (Real.exp_pos _).le
              _ = Real.exp (-lam₀ * u) * Real.exp (-(δ_gap / 2) * u) := by rw [one_mul]
          rw [ha_norm, mul_pow] at h_main
          have hamp_pos : 0 < ‖amp₀‖ := norm_pos_iff.mpr hamp₀_ne
          have h_rhs := exp_comb_rhs_le hC_L_nn hC_rem_nn hC_T_nn hamp_pos h1_bd h2_bd
          exact le_of_mul_le_mul_left (h_main.trans h_rhs) (mul_pos hamp_pos (Real.exp_pos _))
        have h_iso := hflat_to_formal (half_pos hδ_pos)
          (D_joint K r i₀ (ω i₀ m₀ : ℂ) Pmin) ⟨(C_L * C_rem + C_T * ‖amp₀‖ ^ 2) / ‖amp₀‖, h_bridge⟩
        by_contra h_ne
        exact hPmin_min _ h_ne (degree_D_joint_lt i₀ _ Pmin hPmin_pos_deg) h_iso
    -- Every component i and every m < r + 1 lies in valSet, so D_joint K r i (ω i m) Pmin = 0!
    have hD_all : ∀ (i : Fin K) (m : ℕ), m < r + 1 → D_joint K r i (ω i m : ℂ) Pmin = 0 := by
      intro i m hm
      have hle_top : ω i m ≤ B_top :=
        le_trans ((h.ω_mono i).monotone (Nat.lt_succ_iff.mp hm))
          (Finset.le_sup' (fun k => ω k r) (Finset.mem_univ i))
      have hmem_val : ω i m ∈ valSet :=
        Finset.mem_image.mpr ⟨(i, m), hmem_poleSet i m hle_top, rfl⟩
      have hrange : Set.range lamEmb = (valSet : Set ℝ) := Finset.range_orderEmbOfFin valSet rfl
      obtain ⟨kFin, hk_eq⟩ : ∃ k : Fin N_poles, lamEmb k = ω i m := by
        have : ω i m ∈ Set.range lamEmb := hrange.symm ▸ Finset.mem_coe.mpr hmem_val
        exact this
      have hown_eq : owner kFin = (i, m) :=
        hpoleSet_inj (howner_mem kFin) (hmem_poleSet i m hle_top) ((howner_eq kFin).trans hk_eq)
      have hpeel := hD_peel kFin.val kFin.isLt
      have hfin_eq : (⟨kFin.val, kFin.isLt⟩ : Fin N_poles) = kFin := Fin.eta kFin kFin.isLt
      rw [hfin_eq, hown_eq] at hpeel
      exact hpeel
    exact joint_vandermonde_contradiction Pmin hPmin_pos_deg ω h.ω_mono hD_all

/-! #### 1F. Arbitrary Ray `θ₀`, Rational Coefficients `ℂ(u)`, & Analytic Laplace / Mordell Transfer -/

private def JointSimplePoleFamily.rotateToZero {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {θ₀ : ℝ} {ω : Fin K → ℕ → ℝ} {res : Fin K → ℕ → ℂ}
    (h : JointSimplePoleFamily K φ θ₀ ω res) :
    JointSimplePoleFamily K (fun i z => φ i (Complex.exp (I * (θ₀ : ℂ)) * z)) 0 ω
      (fun i m => Complex.exp (-I * (θ₀ : ℂ)) * res i m) where
  α₀ := h.α₀
  θ := h.θ
  ε := h.ε
  hθ_pos := h.hθ_pos
  hθ_lt := h.hθ_lt
  hα₀_lt := h.hα₀_lt
  hε_pos := h.hε_pos
  ω_pos := h.ω_pos
  ω_mono := h.ω_mono
  ω_unbounded := h.ω_unbounded
  ω_disjoint := h.ω_disjoint
  res_ne_zero := fun i m => mul_ne_zero (Complex.exp_ne_zero _) (h.res_ne_zero i m)
  analyticOn := fun i z hz => by
    have hmem : Complex.exp (I * (θ₀ : ℂ)) * z ∈ rotatedPuncturedWedge θ₀ h.α₀ h.ε (ω i) := by
      simp only [rotatedPuncturedWedge, Set.mem_ofPred_eq] at hz ⊢
      have hcancel : Complex.exp (-I * (θ₀ : ℂ)) * (Complex.exp (I * (θ₀ : ℂ)) * z) = z := by
        rw [← mul_assoc, ← Complex.exp_add, show -I * (θ₀ : ℂ) + I * (θ₀ : ℂ) = 0 by ring,
          Complex.exp_zero, one_mul]
      rw [hcancel]
      simpa [rotatedPuncturedWedge] using hz
    exact AnalyticAt.comp (f := fun w : ℂ => Complex.exp (I * (θ₀ : ℂ)) * w) (g := φ i)
      (h.analyticOn i _ hmem) (analyticAt_const.mul analyticAt_id)
  pole_res := fun i m => by
    obtain ⟨L, hL⟩ := h.pole_res i m
    refine ⟨L, ?_⟩
    let μ : ℂ := Complex.exp (I * (θ₀ : ℂ))
    have hμ_ne : μ ≠ 0 := Complex.exp_ne_zero _
    have hμ_inv : Complex.exp (-I * (θ₀ : ℂ)) = μ⁻¹ := by
      rw [← Complex.exp_neg]; congr 1; ring
    have hmap : Tendsto (fun z : ℂ => μ * z) (𝓝[≠] ((ω i m : ℝ) : ℂ)) (𝓝[≠] (μ * (ω i m : ℂ))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact ((continuous_const.mul continuous_id).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        intro heq; exact hz (mul_left_cancel₀ hμ_ne heq)
    have hcomp := hL.comp hmap
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hsub : z - (ω i m : ℂ) ≠ 0 := sub_ne_zero.mpr hz
    dsimp only [Function.comp_apply, μ]
    rw [hμ_inv]
    have hdiv : res i m / (μ * z - μ * (ω i m : ℂ)) = (μ⁻¹ * res i m) / (z - (ω i m : ℂ)) := by
      rw [← mul_sub]; field_simp [hμ_ne, hsub]
    rw [hdiv]
  expType_plus := fun i => by
    obtain ⟨C, B, hC, hB, hbd⟩ := h.expType_plus i
    refine ⟨C, B, hC, hB, fun v hv => ?_⟩
    have hnorm : ‖Complex.exp (I * (θ₀ : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I θ₀
    have hexp : Complex.exp (I * (θ₀ : ℂ)) * (Complex.exp (I * ((0 + h.θ : ℝ) : ℂ)) * (v : ℂ)) =
        Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ)) * (v : ℂ) := by
      rw [← mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
    have hpull : ‖Minor.pull (Complex.exp (I * ((0 + h.θ : ℝ) : ℂ)))
        (fun z => φ i (Complex.exp (I * (θ₀ : ℂ)) * z)) v‖ =
        ‖Minor.pull (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ))) (φ i) v‖ := by
      simp only [Minor.pull, hexp, norm_mul]
      rw [show ‖Complex.exp (I * ((0 + h.θ : ℝ) : ℂ))‖ = 1 by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _,
          show ‖Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ))‖ = 1 by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _]
    rw [hpull]; exact hbd v hv
  expType_minus := fun i => by
    obtain ⟨C, B, hC, hB, hbd⟩ := h.expType_minus i
    refine ⟨C, B, hC, hB, fun v hv => ?_⟩
    have hexp : Complex.exp (I * (θ₀ : ℂ)) * (Complex.exp (I * ((0 - h.θ : ℝ) : ℂ)) * (v : ℂ)) =
        Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ)) * (v : ℂ) := by
      rw [← mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring
    have hpull : ‖Minor.pull (Complex.exp (I * ((0 - h.θ : ℝ) : ℂ)))
        (fun z => φ i (Complex.exp (I * (θ₀ : ℂ)) * z)) v‖ =
        ‖Minor.pull (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ))) (φ i) v‖ := by
      simp only [Minor.pull, hexp, norm_mul]
      rw [show ‖Complex.exp (I * ((0 - h.θ : ℝ) : ℂ))‖ = 1 by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _,
          show ‖Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ))‖ = 1 by rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _]
    rw [hpull]; exact hbd v hv

/-- **General Rotated Multi-Function Simple-Pole Joint Differential Independence (`ℂ[u]`)**. -/
theorem joint_stokes_vandermonde_no_ade {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {θ₀ : ℝ} {ω : Fin K → ℕ → ℝ} {res : Fin K → ℕ → ℂ}
    (h : JointSimplePoleFamily K φ θ₀ ω res)
    {r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hP : jointFormalEvalPoly (fun i => formalSeries (φ i)) P = 0) : P = 0 := by
  let μ : ℂ := Complex.exp (I * (θ₀ : ℂ))
  have hμ_ne : μ ≠ 0 := Complex.exp_ne_zero _
  have hφ0 : ∀ i : Fin K, AnalyticAt ℂ (φ i) 0 := fun i => by
    refine h.analyticOn i 0 ?_
    simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, mul_zero, Set.mem_sdiff]
    refine ⟨Or.inl (by simpa [Metric.mem_ball] using h.hε_pos), ?_⟩
    rintro ⟨m, hm⟩
    have hωm : 0 < ω i m := lt_of_lt_of_le (h.ω_pos i) ((h.ω_mono i).monotone (Nat.zero_le m))
    have h0 : ω i m = 0 := Complex.ofReal_eq_zero.mp hm
    linarith
  have hrot_zero := jointFormalEvalPoly_rot_eq_zero hφ0 hμ_ne P hP
  have hrot_eq0 := joint_stokes_vandermonde_no_ade_zero h.rotateToZero (jointRotPoly K r μ P) hrot_zero
  exact (jointRotPoly_eq_zero_iff hμ_ne P).mp hrot_eq0

private def clearDenomPolyJ {ι : Type*} (P : MvPolynomial ι (RatFunc ℂ)) : Polynomial ℂ :=
  ∏ α ∈ P.support, (P.coeff α).denom

private lemma clearDenomPolyJ_ne_zero {ι : Type*} (P : MvPolynomial ι (RatFunc ℂ)) :
    clearDenomPolyJ P ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => RatFunc.denom_ne_zero _

private def clearDenomMvPolyJ {ι : Type*} [DecidableEq ι] (P : MvPolynomial ι (RatFunc ℂ)) :
    MvPolynomial ι (Polynomial ℂ) :=
  ∑ α ∈ P.support,
    MvPolynomial.monomial α ((P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom)

private lemma clearDenomMvPolyJ_coeff {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial ι (RatFunc ℂ)) (α : ι →₀ ℕ) :
    (clearDenomMvPolyJ P).coeff α =
      (P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom := by
  unfold clearDenomMvPolyJ
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, RatFunc.num_zero, zero_mul, Finset.sum_eq_zero]
    intro β hβ
    have hne : β ≠ α := fun h => hα (h ▸ hβ)
    simp [hne]

private lemma clearDenomMvPolyJ_eq_zero_iff {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial ι (RatFunc ℂ)) :
    clearDenomMvPolyJ P = 0 ↔ P = 0 := by
  constructor
  · intro h0
    ext α
    have hα : (clearDenomMvPolyJ P).coeff α = 0 := by rw [h0]; simp
    rw [clearDenomMvPolyJ_coeff] at hα
    have hprod_ne : ∏ β ∈ P.support.erase α, (P.coeff β).denom ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun _ _ => RatFunc.denom_ne_zero _
    have hnum0 : (P.coeff α).num = 0 := (mul_eq_zero.mp hα).resolve_right hprod_ne
    have hdiv := RatFunc.num_div_denom (P.coeff α)
    rw [hnum0, map_zero, zero_div] at hdiv
    simpa using hdiv.symm
  · rintro rfl
    ext α; simp [clearDenomMvPolyJ_coeff]

private lemma poly_eval_eventually_ne_zeroJ {q : Polynomial ℂ} (hq : q ≠ 0) :
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

private lemma jointEvalU_clearDenomMvPolyJ {K r : ℕ}
    (P : MvPolynomial (Fin K × Fin (r + 1)) (RatFunc ℂ)) {u : ℂ}
    (hu : ∀ β ∈ P.support, (P.coeff β).denom.eval u ≠ 0) :
    jointEvalU (clearDenomMvPolyJ P) u = (clearDenomPolyJ P).eval u • jointEvalRatU P u := by
  classical
  ext α
  rw [jointEvalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, clearDenomMvPolyJ_coeff,
    MvPolynomial.coeff_smul, smul_eq_mul, jointEvalRatU, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp only [↓reduceIte, ratEval, clearDenomPolyJ, Polynomial.eval_prod]
      rw [← Finset.mul_prod_erase P.support (fun β => (P.coeff β).denom.eval u) hα,
        Polynomial.eval_mul, Polynomial.eval_prod]
      field_simp [hu α hα]
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
    rw [hP0, RatFunc.num_zero, zero_mul, Polynomial.eval_zero, Finset.sum_eq_zero]
    · simp
    · intro β hβ
      rw [ite_eq_right_iff]; intro hβα; subst hβα; exact absurd hβ hα

/-- **General Rotated Multi-Function Simple-Pole Joint Differential Independence (`ℂ(u)`)**. -/
theorem joint_stokes_vandermonde_no_rat_ade {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {θ₀ : ℝ} {ω : Fin K → ℕ → ℝ} {res : Fin K → ℕ → ℂ}
    (h : JointSimplePoleFamily K φ θ₀ ω res)
    {r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (RatFunc ℂ))
    (hP : jointFormalEvalRat (fun i => formalSeries (φ i)) P = 0) : P = 0 := by
  classical
  have hclear : polyToLaurent (clearDenomPolyJ P) *
        jointFormalEvalRat (fun i => formalSeries (φ i)) P =
      jointFormalEvalPoly (fun i => formalSeries (φ i)) (clearDenomMvPolyJ P) := by
    have hP_sum : P = ∑ α ∈ P.support, MvPolynomial.monomial α (P.coeff α) := MvPolynomial.as_sum P
    conv_lhs => arg 2; rw [hP_sum]
    unfold jointFormalEvalRat jointFormalEvalPoly clearDenomMvPolyJ
    rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
    simp_rw [MvPolynomial.eval₂_monomial]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [← mul_assoc]
    congr 1
    have hcoeff : polyToLaurent (clearDenomPolyJ P) * ratToLaurent (P.coeff α) =
        polyToLaurent ((P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom) := by
      have hdiv := RatFunc.num_div_denom (P.coeff α)
      have hrat_eq : ratToLaurent (P.coeff α) =
          polyToLaurent (P.coeff α).num / polyToLaurent (P.coeff α).denom := by
        conv_lhs => rw [← hdiv]
        rw [map_div₀]
        have hlift : ∀ p : Polynomial ℂ, ratToLaurent (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
            polyToLaurent p := fun p => by
          unfold ratToLaurent
          exact RatFunc.liftRingHom_algebraMap _ _ p
        rw [hlift, hlift]
      rw [hrat_eq]
      have hden_ne : polyToLaurent (P.coeff α).denom ≠ 0 := fun h0 =>
        RatFunc.denom_ne_zero (P.coeff α) (polyToLaurent_injectiveJ (h0.trans (map_zero _).symm))
      rw [clearDenomPolyJ, ← Finset.mul_prod_erase P.support (fun β => (P.coeff β).denom) hα,
        map_mul, map_mul]
      field_simp [hden_ne]
    exact hcoeff
  rw [hP, mul_zero] at hclear
  exact (clearDenomMvPolyJ_eq_zero_iff P).mp
    (joint_stokes_vandermonde_no_ade h (clearDenomMvPolyJ P) hclear.symm)

private lemma hasAsympExp_jointEvalW {K r : ℕ}
    {f : Fin K × Fin (r + 1) → ℝ → ℂ} {S : Fin K × Fin (r + 1) → PowerSeries ℂ}
    (hf : ∀ ij, HasAsympExp (f ij) (S ij))
    (Q : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ)) :
    HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun ij => f ij u) (jointEvalU Q (u : ℂ)⁻¹))
      (MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom S Q) := by
  induction Q using MvPolynomial.induction_on with
  | C q =>
    have hq : HasAsympExp (fun u : ℝ => q.eval (u : ℂ)⁻¹) (q : PowerSeries ℂ) := by
      intro N
      refine ⟨∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
      have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
      have hq_sum : q.eval (u : ℂ)⁻¹ =
          ∑ k ∈ Finset.range (max N (q.natDegree + 1)), q.coeff k * (u : ℂ)⁻¹ ^ k := by
        rw [Polynomial.eval_eq_sum_range' (lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right N _))]
      have hps_sum : ∑ k ∈ Finset.range N, PowerSeries.coeff k (q : PowerSeries ℂ) * (u : ℂ)⁻¹ ^ k =
          ∑ k ∈ Finset.range N, q.coeff k * (u : ℂ)⁻¹ ^ k := by
        refine Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_coe]
      rw [hq_sum, hps_sum]
      have hsub : (∑ k ∈ Finset.range (max N (q.natDegree + 1)), q.coeff k * (u : ℂ)⁻¹ ^ k) -
          (∑ k ∈ Finset.range N, q.coeff k * (u : ℂ)⁻¹ ^ k) =
          ∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N),
            q.coeff k * (u : ℂ)⁻¹ ^ k := by
        rw [Finset.sum_sdiff_eq_sub (Finset.range_mono (le_max_left N _))]
      rw [hsub]
      calc ‖∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N),
              q.coeff k * (u : ℂ)⁻¹ ^ k‖
          ≤ ∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N),
              ‖q.coeff k * (u : ℂ)⁻¹ ^ k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N),
              ‖q.coeff k‖ / u ^ N := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hkN : N ≤ k := not_lt.mp (Finset.mem_range.not.mp (Finset.mem_sdiff.mp hk).2)
            rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu_pos.le,
              inv_pow, ← div_eq_mul_inv]
            exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hu_pos N) (pow_le_pow_right₀ hu hkN)
        _ = (∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N), ‖q.coeff k‖) / u ^ N := by
            rw [Finset.sum_div]
        _ ≤ (∑ k ∈ Finset.range (q.natDegree + 1), ‖q.coeff k‖) / u ^ N := by
            refine div_le_div_of_nonneg_right ?_ (pow_nonneg hu_pos.le N)
            have hle : ∑ k ∈ (Finset.range (max N (q.natDegree + 1))) \ (Finset.range N), ‖q.coeff k‖ ≤
                ∑ k ∈ Finset.range (max N (q.natDegree + 1)), ‖q.coeff k‖ :=
              Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => norm_nonneg _
            refine hle.trans_eq ?_
            refine (Finset.sum_subset (Finset.range_mono (le_max_right N _)) fun k _ hnot => ?_).symm
            rw [Finset.mem_range, not_lt] at hnot
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]
    simpa [jointEvalU] using hq
  | add A B hA hB =>
    have h1 : (fun u : ℝ => MvPolynomial.eval (fun ij => f ij u) (jointEvalU (A + B) (u : ℂ)⁻¹)) =
        fun u => MvPolynomial.eval (fun ij => f ij u) (jointEvalU A (u : ℂ)⁻¹) +
          MvPolynomial.eval (fun ij => f ij u) (jointEvalU B (u : ℂ)⁻¹) := by
      funext u; simp only [jointEvalU, map_add]
    rw [h1, MvPolynomial.eval₂_add]
    exact hA.add hB
  | mul_X A ij hA =>
    have h1 : (fun u : ℝ => MvPolynomial.eval (fun ij' => f ij' u)
        (jointEvalU (A * MvPolynomial.X ij) (u : ℂ)⁻¹)) = fun u =>
        MvPolynomial.eval (fun ij' => f ij' u) (jointEvalU A (u : ℂ)⁻¹) * f ij u := by
      funext u; simp only [jointEvalU, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X]
    rw [h1, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact hA.mul (hf ij)

/-- **Asymptotic-Transfer Multi-Function Joint Differential Independence (`ℂ[u]`)**. -/
theorem joint_no_nonautonomous_ade_of_asymp {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {θ₀ : ℝ} {ω : Fin K → ℕ → ℝ} {res : Fin K → ℕ → ℂ}
    (h : JointSimplePoleFamily K φ θ₀ ω res)
    {f : Fin K → ℝ → ℂ}
    (hf_asymp : ∀ (i : Fin K) (j : ℕ), HasAsympExp (iteratedDeriv j (f i)) (d_u^[j] (formalSeries (φ i))))
    {r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (f ij.1) u)
        (jointEvalU P (u : ℂ)) = 0) : P = 0 := by
  let N := maxUDegJ P
  let Q := revMvPolyJ N P
  have hNP : ∀ α, (P.coeff α).natDegree ≤ N := natDegree_le_maxUDegJ P
  have hexp : HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (f ij.1) u)
        (jointEvalU Q (u : ℂ)⁻¹))
      (jointFormalEvalW (fun i => formalSeries (φ i)) Q) :=
    hasAsympExp_jointEvalW (fun ij => hf_asymp ij.1 ij.2.val) Q
  have hflat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in Filter.atTop,
      ‖MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (f ij.1) u)
        (jointEvalU Q (u : ℂ)⁻¹)‖ ≤ C / u ^ M := by
    intro M
    refine ⟨0, ?_⟩
    filter_upwards [hP, eventually_gt_atTop (0 : ℝ)] with u hu hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    rw [show Q = revMvPolyJ N P from rfl, jointEvalU_revMvPolyJ P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, hu, mul_zero, norm_zero, zero_div]
  have hW0 : jointFormalEvalW (fun i => formalSeries (φ i)) Q = 0 := hexp.eq_zero_of_flat hflat
  exact joint_stokes_vandermonde_no_ade h P
    ((jointFormalEvalW_eq_zero_iff_poly (fun i => formalSeries (φ i)) P hNP).mp hW0)

/-- **Asymptotic-Transfer Multi-Function Joint Differential Independence (`ℂ(u)`)**. -/
theorem joint_no_rat_ade_of_asymp {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {θ₀ : ℝ} {ω : Fin K → ℕ → ℝ} {res : Fin K → ℕ → ℂ}
    (h : JointSimplePoleFamily K φ θ₀ ω res)
    {f : Fin K → ℝ → ℂ}
    (hf_asymp : ∀ (i : Fin K) (j : ℕ), HasAsympExp (iteratedDeriv j (f i)) (d_u^[j] (formalSeries (φ i))))
    {r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (f ij.1) u)
        (jointEvalRatU P (u : ℂ)) = 0) : P = 0 := by
  have hden : ∀ᶠ u : ℝ in Filter.atTop, ∀ β ∈ P.support, (P.coeff β).denom.eval (u : ℂ) ≠ 0 :=
    (Filter.eventually_all_finset P.support).mpr fun β _ =>
      poly_eval_eventually_ne_zeroJ (RatFunc.denom_ne_zero _)
  have hP_clear : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) => iteratedDeriv ij.2.val (f ij.1) u)
        (jointEvalU (clearDenomMvPolyJ P) (u : ℂ)) = 0 := by
    filter_upwards [hP, hden] with u hu hdu
    rw [jointEvalU_clearDenomMvPolyJ P hdu, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      hu, mul_zero]
  exact (clearDenomMvPolyJ_eq_zero_iff P).mp
    (joint_no_nonautonomous_ade_of_asymp h hf_asymp (clearDenomMvPolyJ P) hP_clear)

/-- **Joint Bounded-Kernel Laplace Differential Independence over `ℂ(u)`**:
Any disjoint-pole `JointSimplePoleFamily` of analytic kernels continuous and bounded on `[0, ∞)`
produces a `K`-tuple of Laplace transforms that is unconditionally jointly differentially
independent over `ℂ(u)`. -/
theorem joint_laplaceTransform_no_rat_ade {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {θ₀ : ℝ} {ω : Fin K → ℕ → ℝ} {res : Fin K → ℕ → ℂ} {M : Fin K → ℝ}
    (h : JointSimplePoleFamily K φ θ₀ ω res)
    (hana : ∀ i : Fin K, AnalyticAt ℂ (φ i) 0)
    (hcont : ∀ i : Fin K, ContinuousOn (fun ξ : ℝ => φ i (ξ : ℂ)) (Set.Ici 0))
    (hbd : ∀ i : Fin K, ∀ ξ : ℝ, 0 ≤ ξ → ‖φ i (ξ : ℂ)‖ ≤ M i)
    {r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (laplaceTransform (φ ij.1)) u)
        (jointEvalRatU P (u : ℂ)) = 0) : P = 0 :=
  joint_no_rat_ade_of_asymp h (fun i j => laplaceTransform_hasAsympExp (hana i) (hcont i) (hbd i) j) P hP

private def JointSimplePoleFamily.half_scale {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {θ₀ : ℝ} {ω : Fin K → ℕ → ℝ} {res : Fin K → ℕ → ℂ}
    (h : JointSimplePoleFamily K φ θ₀ ω res) :
    JointSimplePoleFamily K (fun i z => (1 / 2 : ℂ) * φ i z) θ₀ ω (fun i m => (1 / 2 : ℂ) * res i m) where
  α₀ := h.α₀
  θ := h.θ
  ε := h.ε
  hθ_pos := h.hθ_pos
  hθ_lt := h.hθ_lt
  hα₀_lt := h.hα₀_lt
  hε_pos := h.hε_pos
  ω_pos := h.ω_pos
  ω_mono := h.ω_mono
  ω_unbounded := h.ω_unbounded
  ω_disjoint := h.ω_disjoint
  res_ne_zero := fun i m => mul_ne_zero (by norm_num) (h.res_ne_zero i m)
  analyticOn := fun i z hz => analyticAt_const.mul (h.analyticOn i z hz)
  pole_res := fun i m => by
    obtain ⟨L, hL⟩ := h.pole_res i m
    refine ⟨(1 / 2 : ℂ) * L, ?_⟩
    have hrew : (fun z : ℂ => (1 / 2 : ℂ) * φ i z -
        ((1 / 2 : ℂ) * res i m) / (z - Complex.exp (I * (θ₀ : ℂ)) * (ω i m : ℂ))) =
        fun z => (1 / 2 : ℂ) * (φ i z - res i m / (z - Complex.exp (I * (θ₀ : ℂ)) * (ω i m : ℂ))) := by
      funext z; ring
    rw [hrew]; exact hL.const_mul (1 / 2 : ℂ)
  expType_plus := fun i => by
    obtain ⟨C, B, hC, hB, hbd⟩ := h.expType_plus i
    refine ⟨(1 / 2 : ℝ) * C, B, by positivity, hB, fun v hv => ?_⟩
    have hpull : Minor.pull (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ))) (fun z => (1 / 2 : ℂ) * φ i z) v =
        (1 / 2 : ℂ) * Minor.pull (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ))) (φ i) v := by
      simp [Minor.pull]; ring
    rw [hpull, norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd v hv) (by norm_num)
  expType_minus := fun i => by
    obtain ⟨C, B, hC, hB, hbd⟩ := h.expType_minus i
    refine ⟨(1 / 2 : ℝ) * C, B, by positivity, hB, fun v hv => ?_⟩
    have hpull : Minor.pull (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ))) (fun z => (1 / 2 : ℂ) * φ i z) v =
        (1 / 2 : ℂ) * Minor.pull (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ))) (φ i) v := by
      simp [Minor.pull]; ring
    rw [hpull, norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hbd v hv) (by norm_num)

/-- **Joint Bounded-Kernel Mordell Differential Independence over `ℂ(u)`**:
Any disjoint-pole `JointSimplePoleFamily` of analytic kernels continuous and bounded on `[0, ∞)`
produces a `K`-tuple of Mordell integrals `mordellIntegral (φ i)` that is unconditionally
jointly differentially independent over `ℂ(u)`. -/
theorem joint_mordellIntegral_no_rat_ade {K : ℕ}
    {φ : Fin K → ℂ → ℂ} {θ₀ : ℝ} {ω : Fin K → ℕ → ℝ} {res : Fin K → ℕ → ℂ} {M : Fin K → ℝ}
    (h : JointSimplePoleFamily K φ θ₀ ω res)
    (hana : ∀ i : Fin K, AnalyticAt ℂ (φ i) 0)
    (hcont : ∀ i : Fin K, ContinuousOn (fun ξ : ℝ => φ i (ξ : ℂ)) (Set.Ici 0))
    (hbd : ∀ i : Fin K, ∀ ξ : ℝ, 0 ≤ ξ → ‖φ i (ξ : ℂ)‖ ≤ M i)
    {r : ℕ} (P : MvPolynomial (Fin K × Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (mordellIntegral (φ ij.1)) u)
        (jointEvalRatU P (u : ℂ)) = 0) : P = 0 := by
  have heq : ∀ i : Fin K, mordellIntegral (φ i) = laplaceTransform (fun z => (1 / 2 : ℂ) * φ i z) := by
    intro i; funext u
    rw [mordellIntegral_eq_half_laplace (φ i) u, laplaceTransform, laplaceTransform, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun ξ _ => by ring
  have hP' : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun ij : Fin K × Fin (r + 1) =>
        iteratedDeriv ij.2.val (laplaceTransform (fun z => (1 / 2 : ℂ) * φ ij.1 z)) u)
        (jointEvalRatU P (u : ℂ)) = 0 := by
    simpa only [heq] using hP
  refine joint_laplaceTransform_no_rat_ade h.half_scale (fun i => analyticAt_const.mul (hana i))
    (fun i => continuousOn_const.mul (hcont i)) (M := fun i => (1 / 2) * M i) (fun i ξ hξ => ?_) P hP'
  rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left (hbd i ξ hξ) (by norm_num)

/-! ### 2. Entire Even-Sinc Engine (`sinhSqrt`) & False Theta D-Transcendence Witnesses -/

private lemma exp_I_piF : Complex.exp (I * (Real.pi : ℂ)) = -1 := by
  rw [mul_comm]; exact Complex.exp_pi_mul_I

private lemma exp_neg_I_piF : Complex.exp (-I * (Real.pi : ℂ)) = -1 := by
  rw [neg_mul, Complex.exp_neg, exp_I_piF]; norm_num

private lemma norm_exp_I_realF (t : ℝ) : ‖Complex.exp (I * (t : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I t

private lemma real_one_le_coshF (x : ℝ) : 1 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have hprod : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [sq_nonneg (Real.exp x - 1), Real.exp_pos x]

private lemma real_cosh_mono_nonnegF {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.cosh a ≤ Real.cosh b := by
  rw [Real.cosh_eq, Real.cosh_eq]
  have h1 : Real.exp a ≤ Real.exp b := Real.exp_le_exp.mpr hab
  have h2 : Real.exp (-a - b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h3 : Real.exp (-b) = Real.exp a * Real.exp (-a - b) := by rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (-a) = Real.exp b * Real.exp (-a - b) := by rw [← Real.exp_add]; congr 1; ring
  rw [h3, h4]; nlinarith [Real.exp_pos a, Real.exp_pos b]

private lemma real_sinh_pos_of_posF {x : ℝ} (hx : 0 < x) : 0 < Real.sinh x := by
  rw [Real.sinh_eq]
  have h1 : 1 < Real.exp x := Real.one_lt_exp_iff.mpr hx
  have h2 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  linarith

private lemma real_sinh_monoF {a b : ℝ} (hab : a ≤ b) : Real.sinh a ≤ Real.sinh b := by
  rw [Real.sinh_eq, Real.sinh_eq]
  linarith [Real.exp_le_exp.mpr hab, Real.exp_le_exp.mpr (show -b ≤ -a by linarith)]

private lemma hasDerivAt_real_sinh (x : ℝ) : HasDerivAt Real.sinh (Real.cosh x) x := by
  have h1 : HasDerivAt (fun t : ℝ => (Real.exp t - Real.exp (-t)) / 2)
      ((Real.exp x - Real.exp (-x) * (-1)) / 2) x :=
    ((Real.hasDerivAt_exp x).sub ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x))).div_const 2
  have h2 : HasDerivAt Real.sinh ((Real.exp x - Real.exp (-x) * (-1)) / 2) x := by
    convert h1 using 1; funext t; exact Real.sinh_eq t
  exact h2.congr_deriv (by rw [Real.cosh_eq]; ring)

private lemma hasDerivAt_real_cosh (x : ℝ) : HasDerivAt Real.cosh (Real.sinh x) x := by
  have h1 : HasDerivAt (fun t : ℝ => (Real.exp t + Real.exp (-t)) / 2)
      ((Real.exp x + Real.exp (-x) * (-1)) / 2) x :=
    ((Real.hasDerivAt_exp x).add ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x))).div_const 2
  have h2 : HasDerivAt Real.cosh ((Real.exp x + Real.exp (-x) * (-1)) / 2) x := by
    convert h1 using 1; funext t; exact Real.cosh_eq t
  exact h2.congr_deriv (by rw [Real.sinh_eq]; ring)

private lemma real_le_sinh_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x ≤ Real.sinh x := by
  have hmono : Monotone (fun t : ℝ => Real.sinh t - t) := by
    refine monotone_of_deriv_nonneg ?_ ?_
    · exact fun t => (hasDerivAt_real_sinh t).differentiableAt.sub differentiableAt_id
    · intro t
      have hd : HasDerivAt (fun s : ℝ => Real.sinh s - s) (Real.cosh t - 1) t :=
        (hasDerivAt_real_sinh t).sub (hasDerivAt_id t)
      rw [hd.deriv]; linarith [real_one_le_coshF t]
  have h0 := hmono hx
  simpa using h0

private lemma real_sinh_le_mul_cosh {x : ℝ} (hx : 0 ≤ x) : Real.sinh x ≤ x * Real.cosh x := by
  have hmono : MonotoneOn (fun t : ℝ => t * Real.cosh t - Real.sinh t) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_id.mul Real.continuous_cosh).sub Real.continuous_sinh |>.continuousOn
    · exact fun t _ => ((differentiableAt_id.mul (hasDerivAt_real_cosh t).differentiableAt).sub
        (hasDerivAt_real_sinh t).differentiableAt).differentiableWithinAt
    · intro t ht
      have ht0 : 0 < t := by simpa [interior_Ici] using ht
      have hd : HasDerivAt (fun s : ℝ => s * Real.cosh s - Real.sinh s) (t * Real.sinh t) t := by
        have h1 : HasDerivAt (fun s : ℝ => s * Real.cosh s - Real.sinh s)
            (1 * Real.cosh t + t * Real.sinh t - Real.cosh t) t :=
          ((hasDerivAt_id t).mul (hasDerivAt_real_cosh t)).sub (hasDerivAt_real_sinh t)
        exact h1.congr_deriv (by ring)
      rw [hd.deriv]
      exact mul_nonneg ht0.le (real_sinh_pos_of_posF ht0).le
  have h0 := hmono (le_rfl : (0 : ℝ) ∈ Set.Ici 0) hx hx
  simp only [zero_mul, Real.sinh_zero, sub_self, sub_nonneg] at h0
  exact h0

private lemma sinh_re_le_norm_coshF (w : ℂ) : Real.sinh w.re ≤ ‖Complex.cosh w‖ := by
  rw [Complex.cosh, norm_div, Complex.norm_ofNat, Real.sinh_eq]
  have h1 : ‖Complex.exp w‖ - ‖Complex.exp (-w)‖ ≤ ‖Complex.exp w + Complex.exp (-w)‖ := by
    have htri := norm_sub_le (Complex.exp w + Complex.exp (-w)) (Complex.exp (-w))
    rw [add_sub_cancel_right] at htri; linarith
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h1; linarith

private lemma sinh_re_le_norm_sinhF (w : ℂ) : Real.sinh w.re ≤ ‖Complex.sinh w‖ := by
  rw [Complex.sinh, norm_div, Complex.norm_ofNat, Real.sinh_eq]
  have h1 : ‖Complex.exp w‖ - ‖Complex.exp (-w)‖ ≤ ‖Complex.exp w - Complex.exp (-w)‖ := by
    have htri := norm_add_le (Complex.exp w - Complex.exp (-w)) (Complex.exp (-w))
    rw [sub_add_cancel] at htri; linarith
  rw [Complex.norm_exp, Complex.norm_exp, Complex.neg_re] at h1; linarith

private lemma real_sinh_two_gt_twoF : (2 : ℝ) < Real.sinh 2 := by
  rw [Real.sinh_eq]
  have he1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 3
    simp [Finset.sum_range_succ, Nat.factorial] at h; linarith
  have he2 : (25 / 4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
  have hneg : Real.exp (-2) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

private lemma exists_sqrt_on_flank_rayF (s : ℝ) (hs : s = 1 ∨ s = -1) {v : ℝ} (hv : 0 ≤ v) :
    ∃ w : ℂ, w ^ 2 = Complex.exp (I * ((Real.pi + s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ) ∧
      w.re = (1 / 2) * Real.sqrt v ∧ ‖w‖ = Real.sqrt v := by
  let φ : ℝ := -s * (Real.pi / 3)
  let w : ℂ := (Real.sqrt v : ℂ) * Complex.exp (I * (φ : ℂ))
  refine ⟨w, ?_, ?_, ?_⟩
  · dsimp only [w]
    rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hv, ← Complex.exp_nat_mul, mul_comm (v : ℂ)]
    congr 1; rw [Complex.exp_eq_exp_iff_exists_int]
    rcases hs with rfl | rfl
    · refine ⟨-1, ?_⟩; dsimp only [φ]; push_cast; ring
    · refine ⟨0, ?_⟩; dsimp only [φ]; push_cast; ring
  · dsimp only [w, φ]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      mul_comm I, Complex.exp_ofReal_mul_I_re]
    rcases hs with rfl | rfl
    · rw [show -(1 : ℝ) * (Real.pi / 3) = -(Real.pi / 3) by ring, Real.cos_neg, Real.cos_pi_div_three]; ring
    · rw [show -(-1 : ℝ) * (Real.pi / 3) = Real.pi / 3 by ring, Real.cos_pi_div_three]; ring
  · dsimp only [w]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg v), norm_exp_I_realF, mul_one]

private lemma simple_pole_tendsto_of_analyticF {N D : ℂ → ℂ} {z₀ : ℂ}
    (hN : AnalyticAt ℂ N z₀) (hD : AnalyticAt ℂ D z₀)
    (hD0 : D z₀ = 0) (hD' : deriv D z₀ ≠ 0) :
    ∃ L : ℂ, Filter.Tendsto (fun z : ℂ => N z / D z - (N z₀ / deriv D z₀) / (z - z₀))
      (𝓝[≠] z₀) (𝓝 L) := by
  have hD_sl : AnalyticAt ℂ (dslope D z₀) z₀ := by
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hD.eventually_analyticAt
    have hdiff : DifferentiableOn ℂ (dslope D z₀) (Metric.ball z₀ r) :=
      (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).mpr
        (fun z hz => (hball hz).differentiableAt.differentiableWithinAt)
    exact (hdiff.analyticOnNhd Metric.isOpen_ball) z₀ (Metric.mem_ball_self hr)
  have hN_sl : AnalyticAt ℂ (dslope N z₀) z₀ := by
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hN.eventually_analyticAt
    have hdiff : DifferentiableOn ℂ (dslope N z₀) (Metric.ball z₀ r) :=
      (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).mpr
        (fun z hz => (hball hz).differentiableAt.differentiableWithinAt)
    exact (hdiff.analyticOnNhd Metric.isOpen_ball) z₀ (Metric.mem_ball_self hr)
  have hD_sl0 : dslope D z₀ z₀ = deriv D z₀ := dslope_same D z₀
  let F : ℂ → ℂ := fun z => N z * deriv D z₀ - N z₀ * dslope D z₀ z
  have hF_an : AnalyticAt ℂ F z₀ := (hN.mul analyticAt_const).sub (analyticAt_const.mul hD_sl)
  have hF0 : F z₀ = 0 := by simp [F]
  have hF_sl : AnalyticAt ℂ (dslope F z₀) z₀ := by
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hF_an.eventually_analyticAt
    have hdiff : DifferentiableOn ℂ (dslope F z₀) (Metric.ball z₀ r) :=
      (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).mpr
        (fun z hz => (hball hz).differentiableAt.differentiableWithinAt)
    exact (hdiff.analyticOnNhd Metric.isOpen_ball) z₀ (Metric.mem_ball_self hr)
  let G : ℂ → ℂ := fun z => dslope F z₀ z / (dslope D z₀ z * deriv D z₀)
  have hG_an : AnalyticAt ℂ G z₀ :=
    hF_sl.div (hD_sl.mul analyticAt_const) (mul_ne_zero (hD_sl0.symm ▸ hD') hD')
  refine ⟨G z₀, hG_an.continuousAt.continuousWithinAt.tendsto.congr' ?_⟩
  have hd_ne : ∀ᶠ z in 𝓝 z₀, dslope D z₀ z ≠ 0 :=
    hD_sl.continuousAt.eventually_ne (hD_sl0.symm ▸ hD')
  filter_upwards [nhdsWithin_le_nhds hd_ne, self_mem_nhdsWithin] with z hdz hzne
  have hsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hzne
  have hDz : D z = (z - z₀) * dslope D z₀ z := by
    have := sub_smul_dslope D z₀ z; rw [smul_eq_mul, hD0, sub_zero] at this; exact this.symm
  have hFz : F z = (z - z₀) * dslope F z₀ z := by
    have := sub_smul_dslope F z₀ z; rw [smul_eq_mul, hF0, sub_zero] at this; exact this.symm
  dsimp only [G]; rw [hDz]; field_simp [hsub, hdz, hD']
  dsimp only [F] at hFz; linear_combination -hFz

private lemma expType_div_of_flank_boundF {N D : ℂ → ℂ} {d : ℂ} {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) (hd : ‖d‖ = 1)
    (hD_cont : Continuous (fun v : ℝ => D (d * (v : ℂ))))
    (hD_ne : ∀ v : ℝ, 0 ≤ v → D (d * (v : ℂ)) ≠ 0)
    (hD_far : ∀ v : ℝ, R₀ ≤ v → 1 ≤ ‖D (d * (v : ℂ))‖)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hN_bd : ∀ v : ℝ, 0 ≤ v → ‖N (d * (v : ℂ))‖ ≤ A * Real.exp (B * v)) :
    ExpType (Minor.pull d (fun z => N z / D z)) := by
  have hcomp : IsCompact (Set.Icc (0 : ℝ) R₀) := isCompact_Icc
  have hne : (Set.Icc (0 : ℝ) R₀).Nonempty := ⟨0, le_rfl, hR₀⟩
  obtain ⟨v₀, hv₀_mem, hv₀_min⟩ :=
    hcomp.exists_isMinOn hne (continuous_norm.comp hD_cont).continuousOn
  have hm_pos : 0 < ‖D (d * (v₀ : ℂ))‖ := norm_pos_iff.mpr (hD_ne v₀ hv₀_mem.1)
  let c : ℝ := min 1 ‖D (d * (v₀ : ℂ))‖
  have hc_pos : 0 < c := lt_min one_pos hm_pos
  have hD_ge : ∀ v : ℝ, 0 ≤ v → c ≤ ‖D (d * (v : ℂ))‖ := fun v hv => by
    by_cases hvR : v ≤ R₀
    · exact le_trans (min_le_right _ _) (hv₀_min ⟨hv, hvR⟩)
    · push Not at hvR; exact le_trans (min_le_left _ _) (hD_far v hvR.le)
  refine ⟨A / c, B, by positivity, hB, fun v hv => ?_⟩
  rw [Minor.pull, norm_mul, hd, one_mul, norm_div]
  calc ‖N (d * (v : ℂ))‖ / ‖D (d * (v : ℂ))‖
      ≤ (A * Real.exp (B * v)) / c :=
        div_le_div₀ (by positivity) (hN_bd v hv) hc_pos (hD_ge v hv)
    _ = (A / c) * Real.exp (B * v) := by ring

private lemma flank_ray_im_ne_zero (s : ℝ) (hs : s = 1 ∨ s = -1) {v pos : ℝ}
    (hv : 0 ≤ v) (hpos : 0 < pos)
    (h0 : Complex.exp (I * ((Real.pi + s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ) = -(pos : ℂ)) :
    False := by
  have him := congrArg Complex.im h0
  have hv_ne : v ≠ 0 := by
    intro hv0; rw [hv0, Complex.ofReal_zero, mul_zero] at h0
    exact hpos.ne' (Complex.ofReal_eq_zero.mp (neg_eq_zero.mp h0.symm))
  have hv_pos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv_ne)
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add,
    mul_comm I, Complex.exp_ofReal_mul_I_im] at him
  simp only [Complex.neg_im, Complex.ofReal_im, neg_zero] at him
  have hsq3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rcases hs with rfl | rfl
  · rw [show Real.pi + 1 * (Real.pi / 3) = Real.pi / 3 + Real.pi by ring,
      Real.sin_add_pi, Real.sin_pi_div_three] at him
    nlinarith
  · rw [show Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring,
      Real.sin_pi_sub, Real.sin_pi_div_three] at him
    nlinarith

/-! #### 2A. Entire Even-Sinc Function `sinhSqrt(z) = ∑ z^n / (2n + 1)!` -/

/-- Entire function `S(z) = ∑_{n ≥ 0} z^n / (2n + 1)!`, satisfying `w * S(w^2) = sinh w`. -/
@[expose] def sinhSqrt (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / ((2 * n + 1).factorial : ℂ)

private lemma sinhSqrt_term_norm_le (R : ℝ) (n : ℕ) {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) R) :
    ‖z ^ n / ((2 * n + 1).factorial : ℂ)‖ ≤ R ^ n / (n.factorial : ℝ) := by
  have hzR : ‖z‖ ≤ R := (by simpa [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < R).le
  rw [norm_div, norm_pow, Complex.norm_natCast]
  have hfac : (n.factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (by omega : n ≤ 2 * n + 1)
  calc ‖z‖ ^ n / ((2 * n + 1).factorial : ℝ)
      ≤ R ^ n / ((2 * n + 1).factorial : ℝ) :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg z) hzR n) (by positivity)
    _ ≤ R ^ n / (n.factorial : ℝ) :=
        div_le_div_of_nonneg_left (pow_nonneg (le_trans (norm_nonneg z) hzR) n) (by positivity) hfac

lemma sinhSqrt_differentiable : Differentiable ℂ sinhSqrt := by
  intro z₀
  let R : ℝ := ‖z₀‖ + 1
  have hdiffOn : DifferentiableOn ℂ sinhSqrt (Metric.ball (0 : ℂ) R) :=
    Complex.differentiableOn_tsum_of_summable_norm (Real.summable_pow_div_factorial R)
      (fun n => (differentiableOn_pow n).div_const _) Metric.isOpen_ball
      (fun n z hz => sinhSqrt_term_norm_le R n hz)
  exact hdiffOn.differentiableAt (Metric.isOpen_ball.mem_nhds
    (by simp [Metric.mem_ball, dist_zero_right, R]))

lemma sinhSqrt_analyticAt (z₀ : ℂ) : AnalyticAt ℂ sinhSqrt z₀ :=
  (sinhSqrt_differentiable.differentiableOn.analyticOnNhd isOpen_univ) z₀ (Set.mem_univ z₀)

lemma sinhSqrt_zero : sinhSqrt 0 = 1 := by
  unfold sinhSqrt
  rw [tsum_eq_single 0]
  · simp
  · intro n hn; simp [zero_pow hn]

lemma norm_sinhSqrt_le_exp (z : ℂ) : ‖sinhSqrt z‖ ≤ Real.exp ‖z‖ := by
  have hdom : Summable (fun n : ℕ => ‖z‖ ^ n / (n.factorial : ℝ)) :=
    Real.summable_pow_div_factorial ‖z‖
  have hterm : ∀ n : ℕ, ‖z ^ n / ((2 * n + 1).factorial : ℂ)‖ ≤ ‖z‖ ^ n / (n.factorial : ℝ) := by
    intro n; rw [norm_div, norm_pow, Complex.norm_natCast]
    have hfac : (n.factorial : ℝ) ≤ ((2 * n + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega : n ≤ 2 * n + 1)
    exact div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg z) n) (by positivity) hfac
  have hsumm : Summable (fun n : ℕ => ‖z ^ n / ((2 * n + 1).factorial : ℂ)‖) :=
    hdom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  calc ‖sinhSqrt z‖
      ≤ ∑' n : ℕ, ‖z ^ n / ((2 * n + 1).factorial : ℂ)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, ‖z‖ ^ n / (n.factorial : ℝ) := hsumm.tsum_le_tsum hterm hdom
    _ = Real.exp ‖z‖ := by rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-- Exact identity `w * sinhSqrt (w^2) = sinh w` for all `w ∈ ℂ`. -/
theorem mul_sinhSqrt_sq (w : ℂ) : w * sinhSqrt (w ^ 2) = Complex.sinh w := by
  rw [Complex.sinh, Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  have h1 : Summable (fun k : ℕ => w ^ k / (k.factorial : ℂ)) :=
    Summable.of_norm (by simpa [norm_div, norm_pow, Complex.norm_natCast] using Real.summable_pow_div_factorial ‖w‖)
  have h2 : Summable (fun k : ℕ => (-w) ^ k / (k.factorial : ℂ)) :=
    Summable.of_norm (by simpa [norm_div, norm_pow, norm_neg, Complex.norm_natCast] using Real.summable_pow_div_factorial ‖w‖)
  rw [← h1.tsum_sub h2, ← tsum_div_const]
  unfold sinhSqrt
  rw [← tsum_mul_left]
  symm
  refine tsum_eq_tsum_of_ne_zero_bij (fun n => 2 * n.1 + 1) ?_ ?_ ?_
  · intro a b hab; exact Subtype.ext (by dsimp at hab; omega)
  · intro k hk
    have hk' : (w ^ k / (k.factorial : ℂ) - (-w) ^ k / (k.factorial : ℂ)) / 2 ≠ 0 := hk
    have hkodd : k % 2 = 1 := by
      by_contra hev
      have hmod : k % 2 = 0 := by omega
      have hpos : (-w) ^ k = w ^ k := by rw [neg_pow, Even.neg_one_pow (Nat.even_iff.mpr hmod), one_mul]
      exact hk' (by rw [hpos]; ring)
    have hne : w * ((w ^ 2) ^ (k / 2) / ((2 * (k / 2) + 1).factorial : ℂ)) ≠ 0 := by
      intro h0; apply hk'
      have hk2 : 2 * (k / 2) + 1 = k := by omega
      have hodd : (-w) ^ k = -(w ^ k) := by rw [neg_pow, Odd.neg_one_pow (Nat.odd_iff.mpr hkodd)]; ring
      rw [hodd, show (w ^ k / (k.factorial : ℂ) - -w ^ k / (k.factorial : ℂ)) / 2 =
          w ^ k / (k.factorial : ℂ) by ring]
      have hrew : w * ((w ^ 2) ^ (k / 2) / ((2 * (k / 2) + 1).factorial : ℂ)) = w ^ k / (k.factorial : ℂ) := by
        rw [← pow_mul, hk2, mul_div_assoc', ← pow_succ', show 2 * (k / 2) + 1 = k by omega]
      exact hrew ▸ h0
    exact ⟨⟨k / 2, hne⟩, by dsimp; omega⟩
  · intro n
    have hodd : (-w) ^ (2 * n.1 + 1) = -(w ^ (2 * n.1 + 1)) := by
      rw [neg_pow, Odd.neg_one_pow ⟨n.1, by omega⟩]; ring
    rw [hodd, ← pow_mul, mul_div_assoc', ← pow_succ', show 2 * n.1 + 1 = 2 * n.1 + 1 from rfl]
    ring

private lemma hasDerivAt_complex_sinh (w : ℂ) : HasDerivAt Complex.sinh (Complex.cosh w) w := by
  have h1 : HasDerivAt Complex.exp (Complex.exp w) w := Complex.hasDerivAt_exp w
  have h2 : HasDerivAt (fun z : ℂ => Complex.exp (-z)) (-Complex.exp (-w)) w := by
    simpa using (hasDerivAt_id w).neg.cexp
  have h3 := (h1.sub h2).div_const 2
  convert h3 using 1
  · funext z; rw [Complex.sinh]; rfl
  · rw [Complex.cosh]; ring

lemma deriv_sinhSqrt_sq (w : ℂ) :
    2 * w ^ 2 * deriv sinhSqrt (w ^ 2) + sinhSqrt (w ^ 2) = Complex.cosh w := by
  have h1 : HasDerivAt (fun z : ℂ => z * sinhSqrt (z ^ 2))
      (1 * sinhSqrt (w ^ 2) + w * (deriv sinhSqrt (w ^ 2) * (2 * w))) w := by
    have hd1 : HasDerivAt sinhSqrt (deriv sinhSqrt (w ^ 2)) (w ^ 2) :=
      (sinhSqrt_differentiable (w ^ 2)).hasDerivAt
    have hd2 : HasDerivAt (fun z : ℂ => z ^ 2) (2 * w) w := by simpa using hasDerivAt_pow 2 w
    exact (hasDerivAt_id w).mul (HasDerivAt.comp (h := fun z : ℂ => z ^ 2) (h₂ := sinhSqrt) w hd1 hd2)
  have h2 : HasDerivAt (fun z : ℂ => z * sinhSqrt (z ^ 2)) (Complex.cosh w) w := by
    rw [show (fun z : ℂ => z * sinhSqrt (z ^ 2)) = Complex.sinh from funext mul_sinhSqrt_sq]
    exact hasDerivAt_complex_sinh w
  linear_combination h1.unique h2

/-! #### 2B. Witness 1 — Weight-3/2 False Theta `∑ n q^{n²}` Mordell Integral `∫ e^{-u x²} (x² / sinh x) dx` -/

/-- Borel kernel `φ_sinh(z) = √z / sinh(√z) = (sinhSqrt z)⁻¹` for the weight-`3/2` false theta
Mordell integral. -/
@[expose] def falseThetaSinhBorel (z : ℂ) : ℂ := (sinhSqrt z)⁻¹

/-- Pole frequencies `ω_k = (π (k + 1))²` of `falseThetaSinhBorel` along `θ₀ = π`. -/
@[expose] def falseThetaSinhFreq (k : ℕ) : ℝ := (Real.pi * ((k : ℝ) + 1)) ^ 2

/-- Weight-`3/2` false theta Mordell integral `∫_0^∞ e^{-u x²} (x² / sinh x) dx`. -/
@[expose] def falseThetaSinhMordell (u : ℝ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) ^ 2 / Complex.sinh (x : ℂ)

lemma falseThetaSinhMordell_eq (u : ℝ) :
    falseThetaSinhMordell u = mordellIntegral falseThetaSinhBorel u := by
  unfold falseThetaSinhMordell mordellIntegral falseThetaSinhBorel
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Set.mem_Ioi.mp hx).ne'
  rw [← mul_sinhSqrt_sq (x : ℂ)]
  have hsne : sinhSqrt ((x : ℂ) ^ 2) ≠ 0 := by
    intro h0
    have hsh := mul_sinhSqrt_sq (x : ℂ)
    rw [h0, mul_zero, ← Complex.ofReal_sinh] at hsh
    exact (real_sinh_pos_of_posF (Set.mem_Ioi.mp hx)).ne' (Complex.ofReal_eq_zero.mp hsh.symm)
  field_simp [hx0, hsne]

private lemma sinhSqrt_eq_zero_iff (z : ℂ) :
    sinhSqrt z = 0 ↔ ∃ k : ℕ, z = -(falseThetaSinhFreq k : ℂ) := by
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := exists_sq_eq z
    have hw_ne : w ≠ 0 := by
      intro hw0; subst hw0; simp [sinhSqrt_zero] at hz
    have hsh : Complex.sinh w = 0 := by rw [← mul_sinhSqrt_sq, hz, mul_zero]
    rw [Complex.sinh] at hsh
    have hsub : Complex.exp w - Complex.exp (-w) = 0 := by
      have := congrArg (· * 2) hsh; simpa using this
    have hexp2 : Complex.exp (2 * w) = Complex.exp 0 := by
      rw [Complex.exp_zero, show 2 * w = w + w by ring, Complex.exp_add]
      have hprod : Complex.exp w * Complex.exp (-w) = 1 := by rw [← Complex.exp_add]; simp
      linear_combination Complex.exp w * hsub + hprod
    rw [Complex.exp_eq_exp_iff_exists_int] at hexp2
    obtain ⟨j, hj⟩ := hexp2
    have hw : w = I * (Real.pi * (j : ℂ)) := by linear_combination hj / 2
    have hj_ne : j ≠ 0 := by
      intro hj0; subst hj0; apply hw_ne; simp [hw]
    have hnat_pos : 0 < j.natAbs := Int.natAbs_pos.mpr hj_ne
    refine ⟨j.natAbs - 1, ?_⟩
    rw [hw, falseThetaSinhFreq]
    have hsq_j : (((j.natAbs - 1 : ℕ) : ℝ) + 1) ^ 2 = (j : ℝ) ^ 2 := by
      have h1 : ((j.natAbs - 1 : ℕ) : ℝ) + 1 = (j.natAbs : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hnat_pos
      rw [h1]
      have h2 : (j.natAbs : ℝ) = |(j : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [h2, sq_abs]
    have hsq_jC : ((((j.natAbs - 1 : ℕ) : ℝ) + 1 : ℝ) : ℂ) ^ 2 = (j : ℂ) ^ 2 := by exact_mod_cast hsq_j
    have hLHS : (I * (Real.pi * (j : ℂ))) ^ 2 = -((Real.pi : ℂ) ^ 2 * (j : ℂ) ^ 2) := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [hLHS, ← hsq_jC]; push_cast; ring
  · rintro ⟨k, rfl⟩
    let r : ℝ := Real.pi * ((k : ℝ) + 1)
    have hr_pos : 0 < r := by dsimp only [r]; positivity
    have hsq : (I * (r : ℂ)) ^ 2 = -(falseThetaSinhFreq k : ℂ) := by
      rw [falseThetaSinhFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    have hmul := mul_sinhSqrt_sq (I * (r : ℂ))
    rw [hsq, show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.sinh_mul_I, ← Complex.ofReal_sin] at hmul
    have hsin0 : Real.sin r = 0 := Real.sin_eq_zero_iff.mpr ⟨(k + 1 : ℤ), by dsimp only [r]; push_cast; ring⟩
    rw [hsin0, Complex.ofReal_zero, zero_mul] at hmul
    have hir_ne : (r : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr_pos.ne') Complex.I_ne_zero
    exact (mul_eq_zero.mp hmul).resolve_left hir_ne

private lemma deriv_sinhSqrt_ne_zero (k : ℕ) :
    deriv sinhSqrt (-(falseThetaSinhFreq k : ℂ)) ≠ 0 := by
  let r : ℝ := Real.pi * ((k : ℝ) + 1)
  have hsq : (I * (r : ℂ)) ^ 2 = -(falseThetaSinhFreq k : ℂ) := by
    rw [falseThetaSinhFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hd := deriv_sinhSqrt_sq (I * (r : ℂ))
  have h0 : sinhSqrt (-(falseThetaSinhFreq k : ℂ)) = 0 := (sinhSqrt_eq_zero_iff _).mpr ⟨k, rfl⟩
  rw [hsq, h0, add_zero] at hd
  intro hd0; rw [hd0, mul_zero] at hd
  rw [show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.cosh_mul_I, ← Complex.ofReal_cos] at hd
  have hcos0 : Real.cos r = 0 := Complex.ofReal_eq_zero.mp hd.symm
  obtain ⟨m, hm⟩ := Real.cos_eq_zero_iff.mp hcos0
  have hint : 2 * ((k : ℤ) + 1) = 2 * m + 1 := by
    have hreal : ((2 * ((k : ℤ) + 1) : ℤ) : ℝ) = ((2 * m + 1 : ℤ) : ℝ) := by
      push_cast; dsimp only [r] at hm; nlinarith [Real.pi_pos]
    exact_mod_cast hreal
  omega

private lemma falseThetaSinhFreq_mono : StrictMono falseThetaSinhFreq := fun a b hab => by
  unfold falseThetaSinhFreq
  have hlt : (a : ℝ) < b := by exact_mod_cast hab
  have h1 : Real.pi * ((a : ℝ) + 1) < Real.pi * ((b : ℝ) + 1) := mul_lt_mul_of_pos_left (by linarith) Real.pi_pos
  have hpos : 0 < Real.pi * ((a : ℝ) + 1) := by positivity
  nlinarith

private lemma falseThetaSinh_flank_far {v : ℝ} (hv : 36 ≤ v) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    1 ≤ ‖sinhSqrt (Complex.exp (I * ((Real.pi + s * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ))‖ := by
  obtain ⟨w, hw_sq, hw_re, hw_norm⟩ := exists_sqrt_on_flank_rayF s hs (by linarith)
  rw [← hw_sq]
  have h6 : (6 : ℝ) ≤ Real.sqrt v := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)]
    exact Real.sqrt_le_sqrt (by linarith : (6 : ℝ) ^ 2 ≤ v)
  have hw_pos : 0 < ‖w‖ := by linarith
  have hmul : ‖w‖ * ‖sinhSqrt (w ^ 2)‖ = ‖Complex.sinh w‖ := by
    rw [← norm_mul, mul_sinhSqrt_sq]
  have hsinh_ge : ‖w‖ ≤ ‖Complex.sinh w‖ := by
    refine le_trans ?_ (sinh_re_le_norm_sinhF w)
    rw [hw_re, hw_norm, Real.sinh_eq]
    set y : ℝ := (1 / 2) * Real.sqrt v with hy_def
    have hy3 : (3 : ℝ) ≤ y := by linarith
    have hexp_ge := Real.sum_le_exp_of_nonneg (by linarith : 0 ≤ y) 4
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, Nat.factorial] at hexp_ge
    norm_num at hexp_ge
    have hexp_neg : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [sq_nonneg (y - 3)]
  nlinarith

/-- Concrete `HigherOrderBorelData` witness for the weight-`3/2` false theta Mordell kernel
`√z / sinh(√z)` along `θ₀ = π` with simple poles at `-π² (k + 1)²`. -/
def falseThetaSinh_borelData :
    HigherOrderBorelData falseThetaSinhBorel Real.pi falseThetaSinhFreq (fun _ => 1)
      (fun k s => if s = 1 then (deriv sinhSqrt (-(falseThetaSinhFreq k : ℂ)))⁻¹ else 0) where
  α₀ := 5 * Real.pi / 12
  θ := Real.pi / 3
  ε := 1 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by unfold falseThetaSinhFreq; positivity
  ω_mono := falseThetaSinhFreq_mono
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun k => by simpa using inv_ne_zero (deriv_sinhSqrt_ne_zero k)
  analyticOn := by
    intro z hz
    simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
    have hz' := hz.2; rw [exp_neg_I_piF] at hz'
    have hne : sinhSqrt z ≠ 0 := by
      intro h0; obtain ⟨k, hk⟩ := (sinhSqrt_eq_zero_iff z).mp h0
      exact hz' ⟨k, by rw [hk]; ring⟩
    exact (sinhSqrt_analyticAt z).inv hne
  pole_principalPart := fun k => by
    have hpole : Complex.exp (I * (Real.pi : ℂ)) * (falseThetaSinhFreq k : ℂ) = -(falseThetaSinhFreq k : ℂ) := by
      rw [exp_I_piF]; ring
    rw [hpole]; simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one]
    have hzero : sinhSqrt (-(falseThetaSinhFreq k : ℂ)) = 0 := (sinhSqrt_eq_zero_iff _).mpr ⟨k, rfl⟩
    simpa [falseThetaSinhBorel, one_div] using simple_pole_tendsto_of_analyticF (N := fun _ => (1 : ℂ))
      analyticAt_const (sinhSqrt_analyticAt _) hzero (deriv_sinhSqrt_ne_zero k)
  expType_plus := by
    rw [show falseThetaSinhBorel = fun z => (1 : ℂ) / sinhSqrt z from
      funext fun z => by simp [falseThetaSinhBorel, one_div] ]
    refine expType_div_of_flank_boundF (R₀ := 36) (by norm_num) (norm_exp_I_realF _)
      (sinhSqrt_differentiable.continuous.comp (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 1) (B := 0) (by norm_num) (by norm_num) (fun _ _ => by simp)
    · obtain ⟨k, hk⟩ := (sinhSqrt_eq_zero_iff _).mp h0
      exact flank_ray_im_ne_zero 1 (Or.inl rfl) hv (pos := falseThetaSinhFreq k)
        (by unfold falseThetaSinhFreq; positivity) (by simpa using hk)
    · simpa using falseThetaSinh_flank_far hv 1 (Or.inl rfl)
  expType_minus := by
    rw [show falseThetaSinhBorel = fun z => (1 : ℂ) / sinhSqrt z from
      funext fun z => by simp [falseThetaSinhBorel, one_div] ]
    refine expType_div_of_flank_boundF (R₀ := 36) (by norm_num) (norm_exp_I_realF _)
      (sinhSqrt_differentiable.continuous.comp (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 1) (B := 0) (by norm_num) (by norm_num) (fun _ _ => by simp)
    · obtain ⟨k, hk⟩ := (sinhSqrt_eq_zero_iff _).mp h0
      exact flank_ray_im_ne_zero (-1) (Or.inr rfl) hv (pos := falseThetaSinhFreq k)
        (by unfold falseThetaSinhFreq; positivity)
        (by rw [show Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring]; exact hk)
    · have h := falseThetaSinh_flank_far hv (-1) (Or.inr rfl)
      rwa [show Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring] at h

private lemma falseThetaSinhBorel_real_bound (ξ : ℝ) (hξ : 0 ≤ ξ) :
    ‖falseThetaSinhBorel (ξ : ℂ)‖ ≤ 1 := by
  unfold falseThetaSinhBorel
  rcases eq_or_lt_of_le hξ with rfl | hξ_pos
  · simp [sinhSqrt_zero]
  · have hsq : ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 = (ξ : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hξ]
    have hsr : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr hξ_pos
    have hmul := mul_sinhSqrt_sq ((Real.sqrt ξ : ℝ) : ℂ)
    rw [hsq, ← Complex.ofReal_sinh] at hmul
    have hval : sinhSqrt (ξ : ℂ) = ((Real.sinh (Real.sqrt ξ) / Real.sqrt ξ : ℝ) : ℂ) := by
      have hsrC : ((Real.sqrt ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsr.ne'
      rw [Complex.ofReal_div]
      exact (eq_div_iff hsrC).mpr (by rw [mul_comm]; exact hmul)
    rw [hval, norm_inv, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (real_sinh_pos_of_posF hsr).le hsr.le)]
    exact inv_le_one_of_one_le₀ ((one_le_div hsr).mpr (real_le_sinh_of_nonneg hsr.le))

private lemma falseThetaSinhBorel_cont :
    ContinuousOn (fun ξ : ℝ => falseThetaSinhBorel (ξ : ℂ)) (Set.Ici 0) := by
  intro ξ hξ
  have hne : sinhSqrt (ξ : ℂ) ≠ 0 := by
    intro h0; obtain ⟨k, hk⟩ := (sinhSqrt_eq_zero_iff _).mp h0
    have hre := congrArg Complex.re hk; simp at hre
    have hpos : 0 < falseThetaSinhFreq k := by unfold falseThetaSinhFreq; positivity
    linarith [Set.mem_Ici.mp hξ]
  exact ((sinhSqrt_analyticAt (ξ : ℂ)).inv hne).continuousAt.comp
    Complex.continuous_ofReal.continuousAt |>.continuousWithinAt

/-- **Theorem 1 (Weight-3/2 False Theta `∑ n q^{n²}` Mordell Integral D-Transcendence over `ℂ(u)`)**:
`∫_0^∞ e^{-u x²} (x² / sinh x) dx` satisfies NO nonzero rational-coefficient differential equation
over `ℂ(u)`. -/
theorem falseThetaSinhMordell_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val falseThetaSinhMordell u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 := by
  have hP' : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (mordellIntegral falseThetaSinhBorel) u)
        (evalRatU P (u : ℂ)) = 0 := by
    simpa only [show falseThetaSinhMordell = mordellIntegral falseThetaSinhBorel from
      funext falseThetaSinhMordell_eq] using hP
  exact mordellIntegral_no_rat_ade falseThetaSinh_borelData
    ((sinhSqrt_analyticAt 0).inv (by rw [sinhSqrt_zero]; exact one_ne_zero))
    falseThetaSinhBorel_cont falseThetaSinhBorel_real_bound P hP'

/-! #### 2C. Witness 2 — Kontsevich / `χ₁₂` False Theta Mordell Integral `∫ e^{-u x²} (sinh(2x) / (2 cosh(3x))) dx` -/

/-- Borel kernel `φ_Kont(z) = sinhSqrt z / (2 coshSqrt (4 z) - 1)` for the Kontsevich / `χ₁₂`
false-theta Mordell integral. -/
@[expose] def kontsevichFalseBorel (z : ℂ) : ℂ := sinhSqrt z / (2 * coshSqrt (4 * z) - 1)

/-- Pole frequencies `ω_k = (π n_k / 6)²` (`n_k ≡ ±1 mod 6`) of `kontsevichFalseBorel` along `θ₀ = π`. -/
@[expose] def kontsevichFalseFreq (k : ℕ) : ℝ := (Real.pi * (coprimeSixSeq k : ℝ) / 6) ^ 2

/-- Kontsevich / `χ₁₂` false-theta Mordell integral `∫_0^∞ e^{-u x²} (sinh(2x) / (2 cosh(3x))) dx`. -/
@[expose] def kontsevichFalseMordell (u : ℝ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) *
    Complex.sinh (2 * (x : ℂ)) / (2 * Complex.cosh (3 * (x : ℂ)))

private lemma sinh_double_cosh_triple (x : ℂ) :
    Complex.sinh (2 * x) = 2 * Complex.sinh x * Complex.cosh x ∧
    Complex.cosh (3 * x) = Complex.cosh x * (2 * Complex.cosh (2 * x) - 1) := by
  have h1 : Complex.exp (3 * x) = Complex.exp x ^ 3 := by rw [← Complex.exp_nat_mul]; push_cast; rfl
  have h2 : Complex.exp (-(3 * x)) = Complex.exp (-x) ^ 3 := by rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Complex.exp (2 * x) = Complex.exp x ^ 2 := by rw [← Complex.exp_nat_mul]; push_cast; rfl
  have h4 : Complex.exp (-(2 * x)) = Complex.exp (-x) ^ 2 := by rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hprod : Complex.exp x * Complex.exp (-x) = 1 := by rw [← Complex.exp_add]; simp
  constructor
  · rw [Complex.sinh, Complex.sinh, Complex.cosh, h3, h4]; ring
  · rw [Complex.cosh, Complex.cosh, Complex.cosh, h1, h2, h3, h4]
    linear_combination -(Complex.exp x + Complex.exp (-x)) / 2 * hprod

lemma kontsevichFalseMordell_eq (u : ℝ) :
    kontsevichFalseMordell u = mordellIntegral kontsevichFalseBorel u := by
  unfold kontsevichFalseMordell mordellIntegral kontsevichFalseBorel
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  have h4 : 4 * (x : ℂ) ^ 2 = (2 * (x : ℂ)) ^ 2 := by ring
  rw [h4, coshSqrt_sq]
  obtain ⟨hd, ht⟩ := sinh_double_cosh_triple (x : ℂ)
  rw [hd, ht]
  have hc : Complex.cosh (x : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cosh]; exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos x).ne'
  have hd2 : 2 * Complex.cosh (2 * (x : ℂ)) - 1 ≠ 0 := by
    rw [show 2 * (x : ℂ) = ((2 * x : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cosh,
      show (2 : ℂ) * (Real.cosh (2 * x) : ℂ) - 1 = ((2 * Real.cosh (2 * x) - 1 : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_ne_zero.mpr (by linarith [real_one_le_coshF (2 * x)])
  have hsh := mul_sinhSqrt_sq (x : ℂ)
  field_simp [hc, hd2]
  rw [← hsh]

private lemma coprimeSixSeq_monoF : StrictMono coprimeSixSeq := fun a b hab => by
  unfold coprimeSixSeq; split_ifs <;> omega

private lemma coprimeSixSeq_posF (k : ℕ) : 0 < coprimeSixSeq k := by
  unfold coprimeSixSeq; split_ifs <;> omega

private lemma coprimeSixSeq_mod_six (k : ℕ) : coprimeSixSeq k % 6 = 1 ∨ coprimeSixSeq k % 6 = 5 := by
  unfold coprimeSixSeq; split_ifs <;> omega

private lemma exists_coprimeSixSeq_of_mod_sixF (m : ℤ) (hm : m % 6 = 1 ∨ m % 6 = 5) :
    ∃ k : ℕ, (coprimeSixSeq k : ℤ) = |m| := by
  have hnat : m.natAbs % 6 = 1 ∨ m.natAbs % 6 = 5 := by omega
  rcases hnat with h1 | h5
  · refine ⟨2 * (m.natAbs / 6), ?_⟩
    unfold coprimeSixSeq
    rw [show 2 * (m.natAbs / 6) / 2 = m.natAbs / 6 by omega,
        show 2 * (m.natAbs / 6) % 2 = 0 by omega, ite_eq_left_iff.mpr (fun h => absurd rfl h),
        show 6 * (m.natAbs / 6) + 1 = m.natAbs by omega, Int.natCast_natAbs]
  · refine ⟨2 * (m.natAbs / 6) + 1, ?_⟩
    unfold coprimeSixSeq
    rw [show (2 * (m.natAbs / 6) + 1) / 2 = m.natAbs / 6 by omega,
        show (2 * (m.natAbs / 6) + 1) % 2 = 1 by omega, ite_eq_right_iff.mpr (fun h => by omega),
        show 6 * (m.natAbs / 6) + 5 = m.natAbs by omega, Int.natCast_natAbs]

private lemma two_coshSqrt_sub_one_eq_zero_iffF (z : ℂ) :
    2 * coshSqrt z - 1 = 0 ↔ ∃ k : ℕ, z = -(mockThetaOmegaFreq k : ℂ) := by
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := exists_sq_eq z
    rw [coshSqrt_sq, Complex.cosh] at hz
    have hsum : Complex.exp w + Complex.exp (-w) = 1 := by linear_combination hz
    have hprod : Complex.exp w * Complex.exp (-w) = 1 := by rw [← Complex.exp_add]; simp
    have hquad : Complex.exp w ^ 2 - Complex.exp w + 1 = 0 := by
      linear_combination Complex.exp w * hsum - hprod
    let ζ : ℂ := Complex.exp (I * ((Real.pi / 3 : ℝ) : ℂ))
    have hζ_sum : ζ + ζ⁻¹ = 1 := by
      dsimp only [ζ]; rw [← Complex.exp_neg]
      have h1 : Complex.exp (I * ((Real.pi / 3 : ℝ) : ℂ)) + Complex.exp (-(I * ((Real.pi / 3 : ℝ) : ℂ))) =
          2 * Complex.cos ((Real.pi / 3 : ℝ) : ℂ) := by
        rw [Complex.cos, show I * ((Real.pi / 3 : ℝ) : ℂ) = ((Real.pi / 3 : ℝ) : ℂ) * I by ring, ← neg_mul]; ring
      rw [h1, ← Complex.ofReal_cos, Real.cos_pi_div_three]; push_cast; ring
    have hfac : (Complex.exp w - ζ) * (Complex.exp w - ζ⁻¹) = 0 := by
      have hζ_ne : ζ ≠ 0 := Complex.exp_ne_zero _
      linear_combination hquad - Complex.exp w * hζ_sum + mul_inv_cancel₀ hζ_ne
    rcases mul_eq_zero.mp hfac with hL | hR
    · have hexp := Complex.exp_eq_exp_iff_exists_int.mp (sub_eq_zero.mp hL)
      obtain ⟨j, hj⟩ := hexp
      let m : ℤ := 6 * j + 1
      have hw : w = I * ((Real.pi * (m : ℝ) / 3 : ℝ) : ℂ) := by dsimp only [m]; rw [hj]; push_cast; ring
      obtain ⟨k, hk⟩ := exists_coprimeSixSeq_of_mod_sixF m (Or.inl (by omega))
      refine ⟨k, ?_⟩; rw [hw, mockThetaOmegaFreq]
      have hsq_m : ((coprimeSixSeq k : ℝ)) ^ 2 = (m : ℝ) ^ 2 := by
        have h1 : (coprimeSixSeq k : ℝ) = |(m : ℝ)| := by exact_mod_cast hk
        rw [h1, sq_abs]
      have hsq_mC : (coprimeSixSeq k : ℂ) ^ 2 = (m : ℂ) ^ 2 := by exact_mod_cast hsq_m
      have hLHS : (I * ((Real.pi * (m : ℝ) / 3 : ℝ) : ℂ)) ^ 2 = -((Real.pi : ℂ) * (m : ℂ) / 3) ^ 2 := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [hLHS]; push_cast; linear_combination -(Real.pi : ℂ) ^ 2 / 9 * hsq_mC.symm
    · have hexp : Complex.exp w = Complex.exp (-(I * ((Real.pi / 3 : ℝ) : ℂ))) := by
        rw [Complex.exp_neg]; exact sub_eq_zero.mp hR
      obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
      let m : ℤ := 6 * j - 1
      have hw : w = I * ((Real.pi * (m : ℝ) / 3 : ℝ) : ℂ) := by dsimp only [m]; rw [hj]; push_cast; ring
      obtain ⟨k, hk⟩ := exists_coprimeSixSeq_of_mod_sixF m (Or.inr (by omega))
      refine ⟨k, ?_⟩; rw [hw, mockThetaOmegaFreq]
      have hsq_m : ((coprimeSixSeq k : ℝ)) ^ 2 = (m : ℝ) ^ 2 := by
        have h1 : (coprimeSixSeq k : ℝ) = |(m : ℝ)| := by exact_mod_cast hk
        rw [h1, sq_abs]
      have hsq_mC : (coprimeSixSeq k : ℂ) ^ 2 = (m : ℂ) ^ 2 := by exact_mod_cast hsq_m
      have hLHS : (I * ((Real.pi * (m : ℝ) / 3 : ℝ) : ℂ)) ^ 2 = -((Real.pi : ℂ) * (m : ℂ) / 3) ^ 2 := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [hLHS]; push_cast; linear_combination -(Real.pi : ℂ) ^ 2 / 9 * hsq_mC.symm
  · rintro ⟨k, rfl⟩
    let r : ℝ := Real.pi * (coprimeSixSeq k : ℝ) / 3
    have hsq : (I * (r : ℂ)) ^ 2 = -(mockThetaOmegaFreq k : ℂ) := by
      rw [mockThetaOmegaFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [← hsq, coshSqrt_sq, show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.cosh_mul_I, ← Complex.ofReal_cos]
    have hcos : Real.cos r = 1 / 2 := by
      dsimp only [r, coprimeSixSeq]; split_ifs
      · rw [show Real.pi * ((6 * (k / 2) + 1 : ℕ) : ℝ) / 3 =
            Real.pi / 3 + ((k / 2 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring,
          Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_three]
      · rw [show Real.pi * ((6 * (k / 2) + 5 : ℕ) : ℝ) / 3 =
            -(Real.pi / 3) + ((k / 2 + 1 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring,
          Real.cos_add_nat_mul_two_pi, Real.cos_neg, Real.cos_pi_div_three]
    rw [hcos]; push_cast; ring

private lemma kontsevich_denom_eq_zero_iff (z : ℂ) :
    2 * coshSqrt (4 * z) - 1 = 0 ↔ ∃ k : ℕ, z = -(kontsevichFalseFreq k : ℂ) := by
  rw [two_coshSqrt_sub_one_eq_zero_iffF (4 * z)]
  refine exists_congr fun k => ?_
  have hfreq : (mockThetaOmegaFreq k : ℂ) = 4 * (kontsevichFalseFreq k : ℂ) := by
    unfold mockThetaOmegaFreq kontsevichFalseFreq; push_cast; ring
  rw [hfreq]; constructor
  · intro h; linear_combination h / 4
  · intro h; linear_combination 4 * h

private lemma kontsevich_num_ne_zero (k : ℕ) :
    sinhSqrt (-(kontsevichFalseFreq k : ℂ)) ≠ 0 := by
  intro h0
  obtain ⟨m, hm⟩ := (sinhSqrt_eq_zero_iff _).mp h0
  have hreal : kontsevichFalseFreq k = falseThetaSinhFreq m :=
    Complex.ofReal_injective (neg_inj.mp hm)
  unfold kontsevichFalseFreq falseThetaSinhFreq at hreal
  have hpos1 : 0 < Real.pi * (coprimeSixSeq k : ℝ) / 6 := by have := coprimeSixSeq_posF k; positivity
  have hpos2 : 0 < Real.pi * ((m : ℝ) + 1) := by positivity
  have hlin : Real.pi * (coprimeSixSeq k : ℝ) / 6 = Real.pi * ((m : ℝ) + 1) := by nlinarith
  have hint : (coprimeSixSeq k : ℤ) = 6 * ((m : ℤ) + 1) := by
    have : ((coprimeSixSeq k : ℤ) : ℝ) = ((6 * ((m : ℤ) + 1) : ℤ) : ℝ) := by
      push_cast; nlinarith [Real.pi_pos]
    exact_mod_cast this
  rcases coprimeSixSeq_mod_six k with h1 | h5 <;> omega

private lemma kontsevich_deriv_denom_ne_zero (k : ℕ) :
    deriv (fun z => 2 * coshSqrt (4 * z) - 1) (-(kontsevichFalseFreq k : ℂ)) ≠ 0 := by
  let z₀ : ℂ := -(kontsevichFalseFreq k : ℂ)
  have hd_eq : deriv (fun z => 2 * coshSqrt (4 * z) - 1) z₀ = 8 * deriv coshSqrt (4 * z₀) := by
    have h1 : HasDerivAt (fun z : ℂ => coshSqrt (4 * z)) (deriv coshSqrt (4 * z₀) * 4) z₀ :=
      (coshSqrt_differentiable (4 * z₀)).hasDerivAt.comp z₀
        (((hasDerivAt_id z₀).const_mul (4 : ℂ)).congr_deriv (mul_one _))
    have h2 := (h1.const_mul (2 : ℂ)).sub_const (1 : ℂ)
    rw [h2.deriv]; ring
  rw [hd_eq]; refine mul_ne_zero (by norm_num) ?_
  let r : ℝ := Real.pi * (coprimeSixSeq k : ℝ) / 3
  have hsq : (I * (r : ℂ)) ^ 2 = 4 * z₀ := by
    dsimp only [z₀, r]; unfold kontsevichFalseFreq; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hd := deriv_coshSqrt_sq (I * (r : ℂ))
  rw [hsq] at hd; intro h0; rw [h0, mul_zero] at hd
  rw [show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.sinh_mul_I, ← Complex.ofReal_sin] at hd
  have hsin0 : Real.sin r = 0 := Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_right Complex.I_ne_zero)
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin0
  have h3m : 3 * m = (coprimeSixSeq k : ℤ) := by
    have hreal : ((3 * m : ℤ) : ℝ) = ((coprimeSixSeq k : ℤ) : ℝ) := by
      push_cast; dsimp only [r] at hm; nlinarith [Real.pi_pos]
    exact_mod_cast hreal
  rcases coprimeSixSeq_mod_six k with h1 | h5 <;> omega

private lemma kontsevichFalseFreq_mono : StrictMono kontsevichFalseFreq := fun a b hab => by
  unfold kontsevichFalseFreq
  have hlt : (coprimeSixSeq a : ℝ) < (coprimeSixSeq b : ℝ) := by exact_mod_cast coprimeSixSeq_monoF hab
  have h1 : Real.pi * (coprimeSixSeq a : ℝ) / 6 < Real.pi * (coprimeSixSeq b : ℝ) / 6 := by
    have := mul_lt_mul_of_pos_left hlt Real.pi_pos; linarith
  have hpos : 0 < Real.pi * (coprimeSixSeq a : ℝ) / 6 := by have := coprimeSixSeq_posF a; positivity
  nlinarith

/-- Concrete `HigherOrderBorelData` witness for the Kontsevich / `χ₁₂` false-theta Borel kernel
`sinhSqrt z / (2 coshSqrt (4 z) - 1)` along `θ₀ = π` with simple poles at `-(π (6k ± 1)/6)²`. -/
def kontsevichFalse_borelData :
    HigherOrderBorelData kontsevichFalseBorel Real.pi kontsevichFalseFreq (fun _ => 1)
      (fun k s => if s = 1 then
        sinhSqrt (-(kontsevichFalseFreq k : ℂ)) /
          deriv (fun z => 2 * coshSqrt (4 * z) - 1) (-(kontsevichFalseFreq k : ℂ)) else 0) where
  α₀ := 5 * Real.pi / 12
  θ := Real.pi / 3
  ε := 1 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by unfold kontsevichFalseFreq; have := coprimeSixSeq_posF 0; positivity
  ω_mono := kontsevichFalseFreq_mono
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun k => by simpa using div_ne_zero (kontsevich_num_ne_zero k) (kontsevich_deriv_denom_ne_zero k)
  analyticOn := by
    intro z hz
    simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
    have hz' := hz.2; rw [exp_neg_I_piF] at hz'
    have hne : 2 * coshSqrt (4 * z) - 1 ≠ 0 := by
      intro h0; obtain ⟨k, hk⟩ := (kontsevich_denom_eq_zero_iff z).mp h0
      exact hz' ⟨k, by rw [hk]; ring⟩
    have hD : AnalyticAt ℂ (fun ζ => 2 * coshSqrt (4 * ζ) - 1) z :=
      (analyticAt_const.mul (AnalyticAt.comp (f := fun ζ : ℂ => 4 * ζ) (g := coshSqrt)
        (coshSqrt_analyticAt (4 * z)) (analyticAt_const.mul analyticAt_id))).sub analyticAt_const
    exact (sinhSqrt_analyticAt z).div hD hne
  pole_principalPart := fun k => by
    have hpole : Complex.exp (I * (Real.pi : ℂ)) * (kontsevichFalseFreq k : ℂ) = -(kontsevichFalseFreq k : ℂ) := by
      rw [exp_I_piF]; ring
    rw [hpole]; simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one]
    have hzero : 2 * coshSqrt (4 * -(kontsevichFalseFreq k : ℂ)) - 1 = 0 :=
      (kontsevich_denom_eq_zero_iff _).mpr ⟨k, rfl⟩
    have hD : AnalyticAt ℂ (fun ζ => 2 * coshSqrt (4 * ζ) - 1) (-(kontsevichFalseFreq k : ℂ)) :=
      (analyticAt_const.mul (AnalyticAt.comp (f := fun ζ : ℂ => 4 * ζ) (g := coshSqrt)
        (coshSqrt_analyticAt _) (analyticAt_const.mul analyticAt_id))).sub analyticAt_const
    exact simple_pole_tendsto_of_analyticF (sinhSqrt_analyticAt _) hD hzero (kontsevich_deriv_denom_ne_zero k)
  expType_plus := by
    refine expType_div_of_flank_boundF (R₀ := 4) (by norm_num) (norm_exp_I_realF _)
      (((continuous_const.mul (coshSqrt_differentiable.continuous.comp (continuous_const.mul continuous_id))).sub
        continuous_const).comp (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 1) (B := 1) (by norm_num) (by norm_num) (fun v hv => ?_)
    · obtain ⟨k, hk⟩ := (kontsevich_denom_eq_zero_iff _).mp h0
      exact flank_ray_im_ne_zero 1 (Or.inl rfl) hv (pos := kontsevichFalseFreq k)
        (by unfold kontsevichFalseFreq; have := coprimeSixSeq_posF k; positivity) (by simpa using hk)
    · obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_rayF 1 (Or.inl rfl) (by linarith)
      have h4sq : 4 * (Complex.exp (I * ((Real.pi + Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ)) = (2 * w) ^ 2 := by
        rw [mul_pow, show (2 : ℂ) ^ 2 = 4 by norm_num, hw_sq]; simp
      rw [h4sq, coshSqrt_sq]
      have h2re : (2 * w).re = Real.sqrt v := by simp [hw_re]
      have hge2 : 2 ≤ (2 * w).re := by
        rw [h2re, ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by linarith : (2 : ℝ) ^ 2 ≤ v)
      have htri := norm_add_le (2 * Complex.cosh (2 * w) - 1) (1 : ℂ)
      rw [sub_add_cancel, norm_mul, Complex.norm_ofNat, norm_one] at htri
      linarith [real_sinh_two_gt_twoF, real_sinh_monoF hge2, sinh_re_le_norm_coshF (2 * w)]
    · rw [one_mul, one_mul]
      refine (norm_sinhSqrt_le_exp _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, norm_exp_I_realF, one_mul, Complex.norm_real, Real.norm_of_nonneg hv]
  expType_minus := by
    refine expType_div_of_flank_boundF (R₀ := 4) (by norm_num) (norm_exp_I_realF _)
      (((continuous_const.mul (coshSqrt_differentiable.continuous.comp (continuous_const.mul continuous_id))).sub
        continuous_const).comp (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 1) (B := 1) (by norm_num) (by norm_num) (fun v hv => ?_)
    · obtain ⟨k, hk⟩ := (kontsevich_denom_eq_zero_iff _).mp h0
      exact flank_ray_im_ne_zero (-1) (Or.inr rfl) hv (pos := kontsevichFalseFreq k)
        (by unfold kontsevichFalseFreq; have := coprimeSixSeq_posF k; positivity)
        (by rw [show Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring]; exact hk)
    · obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_rayF (-1) (Or.inr rfl) (by linarith)
      have h4sq : 4 * (Complex.exp (I * ((Real.pi - Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ)) = (2 * w) ^ 2 := by
        rw [mul_pow, show (2 : ℂ) ^ 2 = 4 by norm_num, hw_sq]
        have : Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 := by ring
        rw [this]
      rw [h4sq, coshSqrt_sq]
      have h2re : (2 * w).re = Real.sqrt v := by simp [hw_re]
      have hge2 : 2 ≤ (2 * w).re := by
        rw [h2re, ← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by linarith : (2 : ℝ) ^ 2 ≤ v)
      have htri := norm_add_le (2 * Complex.cosh (2 * w) - 1) (1 : ℂ)
      rw [sub_add_cancel, norm_mul, Complex.norm_ofNat, norm_one] at htri
      linarith [real_sinh_two_gt_twoF, real_sinh_monoF hge2, sinh_re_le_norm_coshF (2 * w)]
    · rw [one_mul, one_mul]
      refine (norm_sinhSqrt_le_exp _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul, norm_exp_I_realF, one_mul, Complex.norm_real, Real.norm_of_nonneg hv]

private lemma kontsevichFalseBorel_real_bound (ξ : ℝ) (hξ : 0 ≤ ξ) :
    ‖kontsevichFalseBorel (ξ : ℂ)‖ ≤ 1 := by
  unfold kontsevichFalseBorel
  have h4sq : 4 * (ξ : ℂ) = ((2 * Real.sqrt ξ : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, mul_pow, Real.sq_sqrt hξ]; push_cast; ring
  rw [h4sq, coshSqrt_sq, ← Complex.ofReal_cosh,
    show (2 : ℂ) * (Real.cosh (2 * Real.sqrt ξ) : ℂ) - 1 = ((2 * Real.cosh (2 * Real.sqrt ξ) - 1 : ℝ) : ℂ) by
      push_cast; rfl]
  have hden_pos : 0 < 2 * Real.cosh (2 * Real.sqrt ξ) - 1 := by linarith [real_one_le_coshF (2 * Real.sqrt ξ)]
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hden_pos.le, div_le_one hden_pos]
  rcases eq_or_lt_of_le hξ with rfl | hξ_pos
  · simp [sinhSqrt_zero]; norm_num
  · have hsr : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr hξ_pos
    have hsq : ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 = (ξ : ℂ) := by rw [← Complex.ofReal_pow, Real.sq_sqrt hξ]
    have hmul := mul_sinhSqrt_sq ((Real.sqrt ξ : ℝ) : ℂ)
    rw [hsq, ← Complex.ofReal_sinh] at hmul
    have hval : sinhSqrt (ξ : ℂ) = ((Real.sinh (Real.sqrt ξ) / Real.sqrt ξ : ℝ) : ℂ) := by
      have hsrC : ((Real.sqrt ξ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsr.ne'
      rw [Complex.ofReal_div]
      exact (eq_div_iff hsrC).mpr (by rw [mul_comm]; exact hmul)
    rw [hval, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (real_sinh_pos_of_posF hsr).le hsr.le)]
    have h1 : Real.sinh (Real.sqrt ξ) / Real.sqrt ξ ≤ Real.cosh (Real.sqrt ξ) :=
      (div_le_iff₀ hsr).mpr (by simpa [mul_comm] using real_sinh_le_mul_cosh hsr.le)
    have h2 : Real.cosh (Real.sqrt ξ) ≤ Real.cosh (2 * Real.sqrt ξ) :=
      real_cosh_mono_nonnegF hsr.le (by linarith)
    linarith [real_one_le_coshF (2 * Real.sqrt ξ)]

private lemma kontsevichFalseBorel_cont :
    ContinuousOn (fun ξ : ℝ => kontsevichFalseBorel (ξ : ℂ)) (Set.Ici 0) := by
  intro ξ hξ
  have hne : 2 * coshSqrt (4 * (ξ : ℂ)) - 1 ≠ 0 := by
    intro h0; obtain ⟨k, hk⟩ := (kontsevich_denom_eq_zero_iff _).mp h0
    have hre := congrArg Complex.re hk; simp at hre
    have hpos : 0 < kontsevichFalseFreq k := by unfold kontsevichFalseFreq; have := coprimeSixSeq_posF k; positivity
    linarith [Set.mem_Ici.mp hξ]
  have hD : AnalyticAt ℂ (fun ζ => 2 * coshSqrt (4 * ζ) - 1) (ξ : ℂ) :=
    (analyticAt_const.mul (AnalyticAt.comp (f := fun ζ : ℂ => 4 * ζ) (g := coshSqrt)
      (coshSqrt_analyticAt _) (analyticAt_const.mul analyticAt_id))).sub analyticAt_const
  exact ((sinhSqrt_analyticAt (ξ : ℂ)).div hD hne).continuousAt.comp
    Complex.continuous_ofReal.continuousAt |>.continuousWithinAt

/-- **Theorem 2 (Kontsevich / `χ₁₂` False Theta Mordell Integral D-Transcendence over `ℂ(u)`)**:
`∫_0^∞ e^{-u x²} (sinh(2x) / (2 cosh(3x))) dx` satisfies NO nonzero rational-coefficient
differential equation over `ℂ(u)`. -/
theorem kontsevichFalseMordell_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val kontsevichFalseMordell u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 := by
  have hP' : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (mordellIntegral kontsevichFalseBorel) u)
        (evalRatU P (u : ℂ)) = 0 := by
    simpa only [show kontsevichFalseMordell = mordellIntegral kontsevichFalseBorel from
      funext kontsevichFalseMordell_eq] using hP
  have hana0 : AnalyticAt ℂ kontsevichFalseBorel 0 := by
    have h0 : 2 * coshSqrt (4 * (0 : ℂ)) - 1 ≠ 0 := by
      have : coshSqrt ((0 : ℂ) ^ 2) = Complex.cosh 0 := coshSqrt_sq 0
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Complex.cosh_zero] at this
      rw [mul_zero, this]; norm_num
    have hD : AnalyticAt ℂ (fun ζ => 2 * coshSqrt (4 * ζ) - 1) 0 :=
      (analyticAt_const.mul (AnalyticAt.comp (f := fun ζ : ℂ => 4 * ζ) (g := coshSqrt)
        (coshSqrt_analyticAt _) (analyticAt_const.mul analyticAt_id))).sub analyticAt_const
    exact (sinhSqrt_analyticAt 0).div hD h0
  exact mordellIntegral_no_rat_ade kontsevichFalse_borelData hana0 kontsevichFalseBorel_cont
    kontsevichFalseBorel_real_bound P hP'

/-! #### 2D. Witness 3 — Literal Rogers False Theta `ψ_Rogers(t) = ∑ (-1)^n e^{-(n+1/2)² t}` Stieltjes Integral -/

/-- Exact pole frequencies `ω_n = (n + 1/2)²` of Rogers's false theta `e^{-t/4} Ψ(e^{-2t})`. -/
@[expose] def rogersFalseThetaFreq (n : ℕ) : ℝ := ((n : ℝ) + 1 / 2) ^ 2

/-- Literal Rogers false theta function `ψ_Rogers(t) = ∑_{n ≥ 0} (-1)^n e^{-(n + 1/2)² t} = e^{-t/4} Ψ(e^{-2t})`. -/
@[expose] def rogersFalseTheta (t : ℝ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * Complex.exp (-(rogersFalseThetaFreq n : ℂ) * (t : ℂ))

/-- Exact Laplace transform (Borel kernel) of Rogers's false theta:
`B_Ψ(z) = ∑_{n ≥ 0} (-1)^n / (z + (n + 1/2)²)`, with simple poles at `-(n + 1/2)²` and residues `(-1)^n`. -/
@[expose] def rogersFalseThetaBorel (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n / (z + (rogersFalseThetaFreq n : ℂ))

/-- Exact Stieltjes transform of Rogers's false theta:
`S_Ψ(u) = ∫_0^∞ ψ_Rogers(t) / (u + t) dt`. -/
@[expose] def rogersFalseThetaStieltjes (u : ℝ) : ℂ :=
  ∫ t in Set.Ioi (0 : ℝ), rogersFalseTheta t / ((u : ℂ) + (t : ℂ))

private lemma rogersFalseThetaFreq_pos (n : ℕ) : 0 < rogersFalseThetaFreq n := by
  unfold rogersFalseThetaFreq; positivity

private lemma rogersFalseThetaFreq_mono : StrictMono rogersFalseThetaFreq := fun a b hab => by
  unfold rogersFalseThetaFreq
  have hlt : (a : ℝ) < b := by exact_mod_cast hab
  have hpos : 0 < (a : ℝ) + 1 / 2 := by positivity
  nlinarith

private lemma summable_inv_rogersFalseThetaFreq : Summable (fun n : ℕ => (rogersFalseThetaFreq n)⁻¹) := by
  have hbase : Summable (fun n : ℕ => (4 : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ))) :=
    ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr (by norm_num))).mul_left 4
  refine hbase.of_nonneg_of_le (fun n => inv_nonneg.mpr (rogersFalseThetaFreq_pos n).le) fun n => ?_
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hle : (((n + 1 : ℕ) : ℝ) / 2) ^ 2 ≤ rogersFalseThetaFreq n := by
    unfold rogersFalseThetaFreq; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  calc (rogersFalseThetaFreq n)⁻¹
      ≤ ((((n + 1 : ℕ) : ℝ) / 2) ^ 2)⁻¹ := inv_anti₀ (by positivity) hle
    _ = 4 * ((n + 1 : ℕ) : ℝ) ^ (-(2 : ℝ)) := by
        rw [div_pow, inv_div, Real.rpow_neg hpos.le, Real.rpow_two, div_eq_mul_inv]; ring

private lemma rogers_tail_ge (w : ℂ) (R : ℝ) :
    ∃ N : ℕ, ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w R →
      rogersFalseThetaFreq (k + N) / 2 ≤ ‖z + (rogersFalseThetaFreq (k + N) : ℂ)‖ := by
  let N : ℕ := Nat.ceil (2 * (‖w‖ + R))
  refine ⟨N, fun k z hz => ?_⟩
  have hN : 2 * (‖w‖ + R) ≤ (N : ℝ) := Nat.le_ceil _
  have hz' : ‖z‖ ≤ ‖w‖ + R := by
    have hball : ‖z - w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
      _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ R + ‖w‖ := by linarith
      _ = ‖w‖ + R := by ring
  have hfr : (N : ℝ) ≤ rogersFalseThetaFreq (k + N) := by
    unfold rogersFalseThetaFreq; push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have htri := norm_sub_le (z + (rogersFalseThetaFreq (k + N) : ℂ)) z
  rw [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (rogersFalseThetaFreq_pos _).le] at htri
  linarith

private lemma rogers_borel_analyticAt {w : ℂ} (hw : ∀ n : ℕ, w + (rogersFalseThetaFreq n : ℂ) ≠ 0) :
    AnalyticAt ℂ rogersFalseThetaBorel w := by
  obtain ⟨N, hN⟩ := rogers_tail_ge w 1
  let head : ℂ → ℂ := fun z => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n / (z + (rogersFalseThetaFreq n : ℂ))
  let tail : ℂ → ℂ := fun z => ∑' k : ℕ, (-1 : ℂ) ^ (k + N) / (z + (rogersFalseThetaFreq (k + N) : ℂ))
  have hdom : Summable (fun k : ℕ => 2 * (rogersFalseThetaFreq (k + N))⁻¹) :=
    ((summable_nat_add_iff N).2 summable_inv_rogersFalseThetaFreq).mul_left 2
  have hterm : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w 1 →
      ‖(-1 : ℂ) ^ (k + N) / (z + (rogersFalseThetaFreq (k + N) : ℂ))‖ ≤ 2 * (rogersFalseThetaFreq (k + N))⁻¹ := by
    intro k z hz
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
    have hge := hN k z hz
    have hpos : 0 < rogersFalseThetaFreq (k + N) / 2 := half_pos (rogersFalseThetaFreq_pos _)
    calc ‖z + (rogersFalseThetaFreq (k + N) : ℂ)‖⁻¹
        ≤ (rogersFalseThetaFreq (k + N) / 2)⁻¹ := inv_anti₀ hpos hge
      _ = 2 * (rogersFalseThetaFreq (k + N))⁻¹ := by rw [inv_div, div_eq_mul_inv]
  have htail_diff : DifferentiableOn ℂ tail (Metric.ball w 1) := by
    refine Complex.differentiableOn_tsum_of_summable_norm hdom (fun k => ?_) Metric.isOpen_ball hterm
    refine DifferentiableOn.div (differentiableOn_const _) (differentiableOn_id.add (differentiableOn_const _))
      fun z hz h0 => ?_
    have h1 := hN k z hz; rw [h0, norm_zero] at h1
    linarith [rogersFalseThetaFreq_pos (k + N)]
  have htail_an : AnalyticAt ℂ tail w :=
    (htail_diff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self zero_lt_one)
  have hhead_an : AnalyticAt ℂ head w :=
    Finset.analyticAt_fun_sum (Finset.range N) fun n _ =>
      analyticAt_const.div (analyticAt_id.add analyticAt_const) (hw n)
  have hev : rogersFalseThetaBorel =ᶠ[𝓝 w] fun z => head z + tail z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one)] with z hz
    have hts : Summable (fun k : ℕ => (-1 : ℂ) ^ (k + N) / (z + (rogersFalseThetaFreq (k + N) : ℂ))) :=
      hdom.of_norm_bounded fun k => hterm k z hz
    exact ((summable_nat_add_iff N).1 hts |>.sum_add_tsum_nat_add N).symm
  exact (hhead_an.add htail_an).congr hev.symm

private lemma rogers_norm_add_ray_ge (n : ℕ) {d : ℂ} (hd : ‖d‖ = 1) (v : ℝ) :
    rogersFalseThetaFreq n * |d.im| ≤ ‖d * (v : ℂ) + (rogersFalseThetaFreq n : ℂ)‖ := by
  have hns : d.re * d.re + d.im * d.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hd]; norm_num
  rw [Complex.norm_def]
  refine Real.le_sqrt_of_sq_le ?_
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.add_im, Complex.mul_im, zero_add, add_zero]
  have key : (d.re * v + rogersFalseThetaFreq n) * (d.re * v + rogersFalseThetaFreq n) +
      d.im * v * (d.im * v) =
      (v + rogersFalseThetaFreq n * d.re) ^ 2 + (rogersFalseThetaFreq n * d.im) ^ 2 := by
    linear_combination (v ^ 2 - (rogersFalseThetaFreq n) ^ 2) * hns
  rw [key, mul_pow, sq_abs]; nlinarith [sq_nonneg (v + rogersFalseThetaFreq n * d.re)]

/-- Concrete `HigherOrderBorelData` witness for Rogers's false theta Borel transform
`B_Ψ(z) = ∑_{n ≥ 0} (-1)^n / (z + (n + 1/2)²)` along `θ₀ = π` with simple poles at `-(n + 1/2)²`. -/
def rogersFalseTheta_borelData :
    HigherOrderBorelData rogersFalseThetaBorel Real.pi rogersFalseThetaFreq (fun _ => 1)
      (fun n s => if s = 1 then (-1 : ℂ) ^ n else 0) where
  α₀ := Real.pi / 4
  θ := Real.pi / 6
  ε := 1 / 8
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := rogersFalseThetaFreq_pos 0
  ω_mono := rogersFalseThetaFreq_mono
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun n => by simp
  analyticOn := by
    intro z hz
    simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
    have hz' := hz.2; rw [exp_neg_I_piF] at hz'
    exact rogers_borel_analyticAt fun n h0 => hz' ⟨n, by linear_combination h0⟩
  pole_principalPart := fun m => by
    have hpole : Complex.exp (I * (Real.pi : ℂ)) * (rogersFalseThetaFreq m : ℂ) = -(rogersFalseThetaFreq m : ℂ) := by
      rw [exp_I_piF]; ring
    rw [hpole]; simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one, sub_neg_eq_add]
    let z₀ : ℂ := -(rogersFalseThetaFreq m : ℂ)
    obtain ⟨N₀, hN₀⟩ := rogers_tail_ge z₀ (1 / 8)
    let N₁ : ℕ := max N₀ (m + 1)
    have hN₁ : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball z₀ (1 / 8) →
        rogersFalseThetaFreq (k + N₁) / 2 ≤ ‖z + (rogersFalseThetaFreq (k + N₁) : ℂ)‖ := by
      intro k z hz
      have hk := hN₀ (k + (N₁ - N₀)) z hz
      rwa [show k + (N₁ - N₀) + N₀ = k + N₁ by omega] at hk
    let mid : ℂ → ℂ := fun z => ∑ n ∈ (Finset.range N₁).erase m, (-1 : ℂ) ^ n / (z + (rogersFalseThetaFreq n : ℂ))
    let tail : ℂ → ℂ := fun z => ∑' k : ℕ, (-1 : ℂ) ^ (k + N₁) / (z + (rogersFalseThetaFreq (k + N₁) : ℂ))
    have hdom : Summable (fun k : ℕ => 2 * (rogersFalseThetaFreq (k + N₁))⁻¹) :=
      ((summable_nat_add_iff N₁).2 summable_inv_rogersFalseThetaFreq).mul_left 2
    have hterm : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball z₀ (1 / 8) →
        ‖(-1 : ℂ) ^ (k + N₁) / (z + (rogersFalseThetaFreq (k + N₁) : ℂ))‖ ≤ 2 * (rogersFalseThetaFreq (k + N₁))⁻¹ := by
      intro k z hz
      rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
      calc ‖z + (rogersFalseThetaFreq (k + N₁) : ℂ)‖⁻¹
          ≤ (rogersFalseThetaFreq (k + N₁) / 2)⁻¹ := inv_anti₀ (half_pos (rogersFalseThetaFreq_pos _)) (hN₁ k z hz)
        _ = 2 * (rogersFalseThetaFreq (k + N₁))⁻¹ := by rw [inv_div, div_eq_mul_inv]
    have htail_diff : DifferentiableOn ℂ tail (Metric.ball z₀ (1 / 8)) := by
      refine Complex.differentiableOn_tsum_of_summable_norm hdom (fun k => ?_) Metric.isOpen_ball hterm
      refine DifferentiableOn.div (differentiableOn_const _) (differentiableOn_id.add (differentiableOn_const _))
        fun z hz h0 => by have := hN₁ k z hz; rw [h0, norm_zero] at this; linarith [rogersFalseThetaFreq_pos (k + N₁)]
    have htail_cont : ContinuousAt tail z₀ :=
      (htail_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num)))).continuousAt
    have hmid_cont : ContinuousAt mid z₀ := by
      have hd : DifferentiableAt ℂ mid z₀ :=
        DifferentiableAt.fun_sum fun n hn =>
          (differentiableAt_const _).div (differentiableAt_id.add (differentiableAt_const _)) fun h0 =>
            rogersFalseThetaFreq_mono.injective.ne (Finset.mem_erase.mp hn).1
              (Complex.ofReal_injective (by dsimp only [z₀] at h0; linear_combination h0))
      exact hd.continuousAt
    refine ⟨mid z₀ + tail z₀, ((hmid_cont.add htail_cont).continuousWithinAt.tendsto).congr' ?_⟩
    filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 8)))]
      with z hz
    have hts : Summable (fun k : ℕ => (-1 : ℂ) ^ (k + N₁) / (z + (rogersFalseThetaFreq (k + N₁) : ℂ))) :=
      hdom.of_norm_bounded fun k => hterm k z hz
    have hall := (summable_nat_add_iff
      (f := fun n : ℕ => (-1 : ℂ) ^ n / (z + (rogersFalseThetaFreq n : ℂ))) N₁).1 hts
    have hsplit := (hall.sum_add_tsum_nat_add N₁).symm
    have hm_lt : m ∈ Finset.range N₁ := Finset.mem_range.mpr (by dsimp only [N₁]; omega)
    have her := (Finset.add_sum_erase (Finset.range N₁)
      (fun n => (-1 : ℂ) ^ n / (z + (rogersFalseThetaFreq n : ℂ))) hm_lt).symm
    dsimp only [Pi.add_apply, rogersFalseThetaBorel, mid, tail]; rw [hsplit, her]; ring
  expType_plus := by
    let d : ℂ := Complex.exp (I * ((Real.pi + Real.pi / 6 : ℝ) : ℂ))
    have hd : ‖d‖ = 1 := norm_exp_I_realF _
    have hdim : |d.im| = 1 / 2 := by
      dsimp only [d]; rw [mul_comm I, Complex.exp_ofReal_mul_I_im,
        show Real.pi + Real.pi / 6 = Real.pi / 6 + Real.pi by ring, Real.sin_add_pi,
        Real.sin_pi_div_six, abs_neg, abs_of_pos (by norm_num)]
    refine ⟨2 * ∑' n : ℕ, (rogersFalseThetaFreq n)⁻¹, 0,
      mul_nonneg (by norm_num) (tsum_nonneg fun n => inv_nonneg.mpr (rogersFalseThetaFreq_pos n).le), le_rfl,
      fun v _ => ?_⟩
    rw [Minor.pull, norm_mul, hd, one_mul, zero_mul, Real.exp_zero, mul_one, rogersFalseThetaBorel]
    have hdom := summable_inv_rogersFalseThetaFreq.mul_left 2
    have hterm : ∀ n : ℕ, ‖(-1 : ℂ) ^ n / (d * (v : ℂ) + (rogersFalseThetaFreq n : ℂ))‖ ≤
        2 * (rogersFalseThetaFreq n)⁻¹ := by
      intro n; rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
      have hge := rogers_norm_add_ray_ge n hd v; rw [hdim] at hge
      calc ‖d * (v : ℂ) + (rogersFalseThetaFreq n : ℂ)‖⁻¹
          ≤ (rogersFalseThetaFreq n * (1 / 2))⁻¹ := inv_anti₀ (by linarith [rogersFalseThetaFreq_pos n]) hge
        _ = 2 * (rogersFalseThetaFreq n)⁻¹ := by rw [mul_inv]; ring
    have hs := hdom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
    calc ‖∑' n, _‖ ≤ ∑' n, ‖(-1 : ℂ) ^ n / (d * (v : ℂ) + (rogersFalseThetaFreq n : ℂ))‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n, 2 * (rogersFalseThetaFreq n)⁻¹ := hs.tsum_le_tsum hterm hdom
      _ = 2 * ∑' n, (rogersFalseThetaFreq n)⁻¹ := tsum_mul_left
  expType_minus := by
    let d : ℂ := Complex.exp (I * ((Real.pi - Real.pi / 6 : ℝ) : ℂ))
    have hd : ‖d‖ = 1 := norm_exp_I_realF _
    have hdim : |d.im| = 1 / 2 := by
      dsimp only [d]; rw [mul_comm I, Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub,
        Real.sin_pi_div_six, abs_of_pos (by norm_num)]
    refine ⟨2 * ∑' n : ℕ, (rogersFalseThetaFreq n)⁻¹, 0,
      mul_nonneg (by norm_num) (tsum_nonneg fun n => inv_nonneg.mpr (rogersFalseThetaFreq_pos n).le), le_rfl,
      fun v _ => ?_⟩
    rw [Minor.pull, norm_mul, hd, one_mul, zero_mul, Real.exp_zero, mul_one, rogersFalseThetaBorel]
    have hdom := summable_inv_rogersFalseThetaFreq.mul_left 2
    have hterm : ∀ n : ℕ, ‖(-1 : ℂ) ^ n / (d * (v : ℂ) + (rogersFalseThetaFreq n : ℂ))‖ ≤
        2 * (rogersFalseThetaFreq n)⁻¹ := by
      intro n; rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div]
      have hge := rogers_norm_add_ray_ge n hd v; rw [hdim] at hge
      calc ‖d * (v : ℂ) + (rogersFalseThetaFreq n : ℂ)‖⁻¹
          ≤ (rogersFalseThetaFreq n * (1 / 2))⁻¹ := inv_anti₀ (by linarith [rogersFalseThetaFreq_pos n]) hge
        _ = 2 * (rogersFalseThetaFreq n)⁻¹ := by rw [mul_inv]; ring
    have hs := hdom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
    calc ‖∑' n, _‖ ≤ ∑' n, ‖(-1 : ℂ) ^ n / (d * (v : ℂ) + (rogersFalseThetaFreq n : ℂ))‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n, 2 * (rogersFalseThetaFreq n)⁻¹ := hs.tsum_le_tsum hterm hdom
      _ = 2 * ∑' n, (rogersFalseThetaFreq n)⁻¹ := tsum_mul_left

private lemma stieltjes_exp_eq_laplace_inv {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(a : ℂ) * (t : ℂ)) / ((u : ℂ) + (t : ℂ)) =
      ∫ ξ in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (ξ : ℂ)) / ((ξ : ℂ) + (a : ℂ)) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let F : ℝ × ℝ → ℂ := fun p =>
    Complex.exp (-(a : ℂ) * (p.1 : ℂ)) * Complex.exp (-(u : ℂ) * (p.2 : ℂ)) *
      Complex.exp (-(p.1 : ℂ) * (p.2 : ℂ))
  have hIntProd : Integrable F (μ.prod μ) := by
    have hdom : Integrable (fun p : ℝ × ℝ => Real.exp (-a * p.1) * Real.exp (-u * p.2)) (μ.prod μ) :=
      (integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0).mul_prod
        (integrableOn_exp_mul_Ioi (by linarith : -u < 0) 0)
    refine hdom.mono' (by fun_prop : Continuous F).aestronglyMeasurable ?_
    have hae : ∀ᵐ p : ℝ × ℝ ∂(μ.prod μ), 0 < p.1 ∧ 0 < p.2 := by
      rw [show μ.prod μ = (volume.prod volume).restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) from
        Measure.prod_restrict _ _]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    filter_upwards [hae] with ⟨t, ξ⟩ ⟨ht, hξ⟩
    dsimp only [F]
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, Complex.neg_im, neg_zero]
    have hle1 : Real.exp (-t * ξ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc Real.exp (-a * t) * Real.exp (-u * ξ) * Real.exp (-t * ξ)
        ≤ Real.exp (-a * t) * Real.exp (-u * ξ) * 1 :=
          mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ = Real.exp (-a * t) * Real.exp (-u * ξ) := mul_one _
  have hswap := MeasureTheory.integral_integral_swap (f := fun t ξ => F (t, ξ))
    (show Integrable (Function.uncurry (fun t ξ => F (t, ξ))) (μ.prod μ) from hIntProd)
  have hLHS : ∀ t ∈ Set.Ioi (0 : ℝ),
      (∫ ξ : ℝ, F (t, ξ) ∂μ) = Complex.exp (-(a : ℂ) * (t : ℂ)) / ((u : ℂ) + (t : ℂ)) := by
    intro t ht
    have ht_pos : 0 < t := ht
    have hrew : (fun ξ : ℝ => F (t, ξ)) =
        fun ξ : ℝ => Complex.exp (-(a : ℂ) * (t : ℂ)) * ((Real.exp (-(u + t) * ξ) : ℝ) : ℂ) := by
      funext ξ; dsimp only [F]; rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [hrew, integral_const_mul, integral_complex_ofReal,
      integral_exp_mul_Ioi (show -(u + t) < 0 by linarith) 0]
    simp only [mul_zero, Real.exp_zero, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_add]
    have hne : (u : ℂ) + (t : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_add]; exact Complex.ofReal_ne_zero.mpr (by linarith)
    field_simp [hne]
  have hRHS : ∀ ξ ∈ Set.Ioi (0 : ℝ),
      (∫ t : ℝ, F (t, ξ) ∂μ) = Complex.exp (-(u : ℂ) * (ξ : ℂ)) / ((ξ : ℂ) + (a : ℂ)) := by
    intro ξ hξ
    have hξ_pos : 0 < ξ := hξ
    have hrew : (fun t : ℝ => F (t, ξ)) =
        fun t : ℝ => Complex.exp (-(u : ℂ) * (ξ : ℂ)) * ((Real.exp (-(a + ξ) * t) : ℝ) : ℂ) := by
      funext t; dsimp only [F]; rw [Complex.ofReal_exp, mul_comm (Complex.exp (-(a : ℂ) * (t : ℂ))),
        mul_assoc, ← Complex.exp_add]
      congr 2; push_cast; ring
    rw [hrew, integral_const_mul, integral_complex_ofReal,
      integral_exp_mul_Ioi (show -(a + ξ) < 0 by linarith) 0]
    simp only [mul_zero, Real.exp_zero, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_add]
    have hne : (ξ : ℂ) + (a : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_add]; exact Complex.ofReal_ne_zero.mpr (by linarith)
    have hne' : (a : ℂ) + (ξ : ℂ) ≠ 0 := by rw [add_comm]; exact hne
    field_simp [hne, hne']; ring
  have h1 : (∫ t : ℝ, ∫ ξ : ℝ, F (t, ξ) ∂μ ∂μ) =
      ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-(a : ℂ) * (t : ℂ)) / ((u : ℂ) + (t : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioi hLHS
  have h2 : (∫ ξ : ℝ, ∫ t : ℝ, F (t, ξ) ∂μ ∂μ) =
      ∫ ξ in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (ξ : ℂ)) / ((ξ : ℂ) + (a : ℂ)) :=
    setIntegral_congr_fun measurableSet_Ioi hRHS
  rw [← h1, ← h2, hswap]

/-- **Exact Stieltjes–Laplace Identity for Rogers's False Theta** (`u > 0`):
`∫_0^∞ (∑_{n ≥ 0} (-1)^n e^{-(n + 1/2)² t}) / (u + t) dt = ∫_0^∞ e^{-u ξ} (∑_{n ≥ 0} (-1)^n / (ξ + (n + 1/2)²)) dξ`. -/
theorem rogersFalseThetaStieltjes_eq_laplace {u : ℝ} (hu : 0 < u) :
    rogersFalseThetaStieltjes u = laplaceTransform rogersFalseThetaBorel u := by
  unfold rogersFalseThetaStieltjes laplaceTransform rogersFalseTheta rogersFalseThetaBorel
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  -- Left side: swap ∫_t and ∑'_n
  have hL_fn : ∀ t ∈ Set.Ioi (0 : ℝ),
      (∑' n : ℕ, (-1 : ℂ) ^ n * Complex.exp (-(rogersFalseThetaFreq n : ℂ) * (t : ℂ))) / ((u : ℂ) + (t : ℂ)) =
        ∑' n : ℕ, (-1 : ℂ) ^ n * (Complex.exp (-(rogersFalseThetaFreq n : ℂ) * (t : ℂ)) / ((u : ℂ) + (t : ℂ))) := by
    intro t _; rw [← tsum_div_const]
    exact tsum_congr fun n => by ring
  have hL_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun t : ℝ => (-1 : ℂ) ^ n * (Complex.exp (-(rogersFalseThetaFreq n : ℂ) * (t : ℂ)) / ((u : ℂ) + (t : ℂ)))) μ :=
    fun n => ContinuousOn.aestronglyMeasurable
      (ContinuousOn.mul continuousOn_const
        ((by fun_prop : ContinuousOn (fun t : ℝ => Complex.exp (-(rogersFalseThetaFreq n : ℂ) * (t : ℂ))) (Set.Ioi 0)).div
          (by fun_prop : ContinuousOn (fun t : ℝ => (u : ℂ) + (t : ℂ)) (Set.Ioi 0)) fun t ht h0 => by
            rw [← Complex.ofReal_add] at h0
            linarith [Complex.ofReal_eq_zero.mp h0, Set.mem_Ioi.mp ht])) measurableSet_Ioi
  have hL_enorm : ∑' n : ℕ, ∫⁻ t : ℝ,
      ‖(-1 : ℂ) ^ n * (Complex.exp (-(rogersFalseThetaFreq n : ℂ) * (t : ℂ)) / ((u : ℂ) + (t : ℂ)))‖ₑ ∂μ ≠ ⊤ := by
    have hle : ∀ n : ℕ, ∫⁻ t : ℝ,
        ‖(-1 : ℂ) ^ n * (Complex.exp (-(rogersFalseThetaFreq n : ℂ) * (t : ℂ)) / ((u : ℂ) + (t : ℂ)))‖ₑ ∂μ ≤
        ENNReal.ofReal ((u⁻¹) * (rogersFalseThetaFreq n)⁻¹) := by
      intro n
      have hdom : IntegrableOn (fun t : ℝ => u⁻¹ * Real.exp (-rogersFalseThetaFreq n * t)) (Set.Ioi 0) volume :=
        (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (rogersFalseThetaFreq_pos n)) 0).const_mul u⁻¹
      have hint_eq : ∫ t in Set.Ioi (0 : ℝ), u⁻¹ * Real.exp (-rogersFalseThetaFreq n * t) =
          u⁻¹ * (rogersFalseThetaFreq n)⁻¹ := by
        rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr (rogersFalseThetaFreq_pos n)) 0]
        simp [div_eq_mul_inv]
      dsimp only [μ]
      rw [← hint_eq, ofReal_integral_eq_lintegral_ofReal hdom
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t _ => by positivity))]
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_))
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have ht_pos : 0 < t := ht
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div, Complex.norm_exp,
        show (-(rogersFalseThetaFreq n : ℂ) * (t : ℂ)).re = -rogersFalseThetaFreq n * t by simp [Complex.mul_re],
        ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ u + t),
        div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hu (by linarith)) (Real.exp_pos _).le
    have hsum_fin : ∑' n : ℕ, ENNReal.ofReal (u⁻¹ * (rogersFalseThetaFreq n)⁻¹) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (inv_nonneg.mpr hu.le)
        (inv_nonneg.mpr (rogersFalseThetaFreq_pos n).le)) (summable_inv_rogersFalseThetaFreq.mul_left u⁻¹)]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hsum_fin (tsum_le_tsum hle)
  have hL_swap : ∫ t in Set.Ioi (0 : ℝ),
      (∑' n : ℕ, (-1 : ℂ) ^ n * Complex.exp (-(rogersFalseThetaFreq n : ℂ) * (t : ℂ))) / ((u : ℂ) + (t : ℂ)) =
      ∑' n : ℕ, (-1 : ℂ) ^ n * ∫ t in Set.Ioi (0 : ℝ),
        Complex.exp (-(rogersFalseThetaFreq n : ℂ) * (t : ℂ)) / ((u : ℂ) + (t : ℂ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hL_fn, MeasureTheory.integral_tsum hL_meas hL_enorm]
    exact tsum_congr fun n => integral_const_mul _ _
  -- Right side: swap ∫_ξ and ∑'_n
  have hR_fn : ∀ ξ ∈ Set.Ioi (0 : ℝ),
      Complex.exp (-(u : ℂ) * (ξ : ℂ)) * (∑' n : ℕ, (-1 : ℂ) ^ n / ((ξ : ℂ) + (rogersFalseThetaFreq n : ℂ))) =
        ∑' n : ℕ, (-1 : ℂ) ^ n * (Complex.exp (-(u : ℂ) * (ξ : ℂ)) / ((ξ : ℂ) + (rogersFalseThetaFreq n : ℂ))) := by
    intro ξ _; rw [← tsum_mul_left]
    exact tsum_congr fun n => by ring
  have hR_meas : ∀ n : ℕ, AEStronglyMeasurable
      (fun ξ : ℝ => (-1 : ℂ) ^ n * (Complex.exp (-(u : ℂ) * (ξ : ℂ)) / ((ξ : ℂ) + (rogersFalseThetaFreq n : ℂ)))) μ :=
    fun n => ContinuousOn.aestronglyMeasurable
      (ContinuousOn.mul continuousOn_const
        ((by fun_prop : ContinuousOn (fun ξ : ℝ => Complex.exp (-(u : ℂ) * (ξ : ℂ))) (Set.Ioi 0)).div
          (by fun_prop : ContinuousOn (fun ξ : ℝ => (ξ : ℂ) + (rogersFalseThetaFreq n : ℂ)) (Set.Ioi 0)) fun ξ hξ h0 => by
            rw [← Complex.ofReal_add] at h0
            linarith [Complex.ofReal_eq_zero.mp h0, Set.mem_Ioi.mp hξ, rogersFalseThetaFreq_pos n])) measurableSet_Ioi
  have hR_enorm : ∑' n : ℕ, ∫⁻ ξ : ℝ,
      ‖(-1 : ℂ) ^ n * (Complex.exp (-(u : ℂ) * (ξ : ℂ)) / ((ξ : ℂ) + (rogersFalseThetaFreq n : ℂ)))‖ₑ ∂μ ≠ ⊤ := by
    have hle : ∀ n : ℕ, ∫⁻ ξ : ℝ,
        ‖(-1 : ℂ) ^ n * (Complex.exp (-(u : ℂ) * (ξ : ℂ)) / ((ξ : ℂ) + (rogersFalseThetaFreq n : ℂ)))‖ₑ ∂μ ≤
        ENNReal.ofReal ((rogersFalseThetaFreq n)⁻¹ * u⁻¹) := by
      intro n
      have hdom : IntegrableOn (fun ξ : ℝ => (rogersFalseThetaFreq n)⁻¹ * Real.exp (-u * ξ)) (Set.Ioi 0) volume :=
        (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hu) 0).const_mul (rogersFalseThetaFreq n)⁻¹
      have hint_eq : ∫ ξ in Set.Ioi (0 : ℝ), (rogersFalseThetaFreq n)⁻¹ * Real.exp (-u * ξ) =
          (rogersFalseThetaFreq n)⁻¹ * u⁻¹ := by
        rw [integral_const_mul, integral_exp_mul_Ioi (neg_lt_zero.mpr hu) 0]
        simp [div_eq_mul_inv]
      dsimp only [μ]
      rw [← hint_eq, ofReal_integral_eq_lintegral_ofReal hdom
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun ξ _ =>
          mul_nonneg (inv_nonneg.mpr (rogersFalseThetaFreq_pos n).le) (Real.exp_pos _).le))]
      refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun ξ hξ => ?_))
      rw [← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      have hξ_pos : 0 < ξ := hξ
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_div, Complex.norm_exp,
        show (-(u : ℂ) * (ξ : ℂ)).re = -u * ξ by simp [Complex.mul_re],
        ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_of_nonneg (by linarith [rogersFalseThetaFreq_pos n]),
        div_eq_mul_inv, mul_comm]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ (rogersFalseThetaFreq_pos n) (by linarith)) (Real.exp_pos _).le
    have hsum_fin : ∑' n : ℕ, ENNReal.ofReal ((rogersFalseThetaFreq n)⁻¹ * u⁻¹) ≠ ⊤ := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (inv_nonneg.mpr (rogersFalseThetaFreq_pos n).le)
        (inv_nonneg.mpr hu.le)) (summable_inv_rogersFalseThetaFreq.mul_right u⁻¹)]
      exact ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top hsum_fin (tsum_le_tsum hle)
  have hR_swap : ∫ ξ in Set.Ioi (0 : ℝ),
      Complex.exp (-(u : ℂ) * (ξ : ℂ)) * (∑' n : ℕ, (-1 : ℂ) ^ n / ((ξ : ℂ) + (rogersFalseThetaFreq n : ℂ))) =
      ∑' n : ℕ, (-1 : ℂ) ^ n * ∫ ξ in Set.Ioi (0 : ℝ),
        Complex.exp (-(u : ℂ) * (ξ : ℂ)) / ((ξ : ℂ) + (rogersFalseThetaFreq n : ℂ)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hR_fn, MeasureTheory.integral_tsum hR_meas hR_enorm]
    exact tsum_congr fun n => integral_const_mul _ _
  rw [hL_swap, hR_swap]
  exact tsum_congr fun n => by rw [stieltjes_exp_eq_laplace_inv (rogersFalseThetaFreq_pos n) hu]

/-- **Theorem 3 (Literal Rogers False Theta Stieltjes Integral D-Transcendence over `ℂ(u)`)**:
The exact Stieltjes transform `∫_0^∞ (∑_{n ≥ 0} (-1)^n e^{-(n + 1/2)² t}) / (u + t) dt` of Rogers's
false theta function satisfies NO nonzero rational-coefficient differential equation over `ℂ(u)`. -/
theorem rogersFalseThetaStieltjes_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val rogersFalseThetaStieltjes u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 := by
  have hEqOn : Set.EqOn rogersFalseThetaStieltjes (laplaceTransform rogersFalseThetaBorel) (Set.Ioi 0) :=
    fun _ hu => rogersFalseThetaStieltjes_eq_laplace hu
  have hderiv_eq : ∀ j : ℕ, ∀ u : ℝ, 0 < u →
      iteratedDeriv j rogersFalseThetaStieltjes u = iteratedDeriv j (laplaceTransform rogersFalseThetaBorel) u := by
    intro j u hu
    exact Filter.EventuallyEq.iteratedDeriv_eq j
      (Filter.eventually_of_mem (Ioi_mem_nhds hu) fun t ht => hEqOn ht)
  have hP' : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (laplaceTransform rogersFalseThetaBorel) u)
        (evalRatU P (u : ℂ)) = 0 := by
    filter_upwards [hP, eventually_gt_atTop (0 : ℝ)] with u hu hpos
    have hfun : (fun j : Fin (r + 1) => iteratedDeriv j.val rogersFalseThetaStieltjes u) =
        fun j : Fin (r + 1) => iteratedDeriv j.val (laplaceTransform rogersFalseThetaBorel) u :=
      funext fun j => hderiv_eq j.val u hpos
    rwa [← hfun]
  have hana0 : AnalyticAt ℂ rogersFalseThetaBorel 0 :=
    rogers_borel_analyticAt fun n h0 => by
      rw [zero_add] at h0; exact (rogersFalseThetaFreq_pos n).ne' (Complex.ofReal_eq_zero.mp h0)
  have hcont : ContinuousOn (fun ξ : ℝ => rogersFalseThetaBorel (ξ : ℂ)) (Set.Ici 0) := by
    intro ξ hξ
    have hana := rogers_borel_analyticAt (w := (ξ : ℂ)) fun n h0 => by
      rw [← Complex.ofReal_add] at h0
      linarith [Complex.ofReal_eq_zero.mp h0, Set.mem_Ici.mp hξ, rogersFalseThetaFreq_pos n]
    exact hana.continuousAt.comp Complex.continuous_ofReal.continuousAt |>.continuousWithinAt
  have hbd : ∀ ξ : ℝ, 0 ≤ ξ → ‖rogersFalseThetaBorel (ξ : ℂ)‖ ≤ ∑' n : ℕ, (rogersFalseThetaFreq n)⁻¹ := by
    intro ξ hξ; unfold rogersFalseThetaBorel
    have hterm : ∀ n : ℕ, ‖(-1 : ℂ) ^ n / ((ξ : ℂ) + (rogersFalseThetaFreq n : ℂ))‖ ≤ (rogersFalseThetaFreq n)⁻¹ := by
      intro n
      rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, one_div, ← Complex.ofReal_add,
        Complex.norm_real, Real.norm_of_nonneg (by linarith [rogersFalseThetaFreq_pos n])]
      exact inv_anti₀ (rogersFalseThetaFreq_pos n) (by linarith)
    have hs := summable_inv_rogersFalseThetaFreq.of_nonneg_of_le (fun _ => norm_nonneg _) hterm
    exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hterm summable_inv_rogersFalseThetaFreq)
  exact laplaceTransform_no_rat_ade rogersFalseTheta_borelData hana0 hcont hbd P hP'

/-! #### 2E. Witness 4 — Positive-Ray (`θ₀ = 0`) Rogers False-Theta Borel Kernel `1 / cos(√z)` -/

/-- Entire function `cosSqrt z = coshSqrt (-z) = ∑ (-1)^n z^n / (2n)!`, satisfying `cosSqrt (w^2) = cos w`. -/
@[expose] def cosSqrt (z : ℂ) : ℂ := coshSqrt (-z)

/-- Exact positive-ray (`θ₀ = 0`) Rogers false-theta Borel kernel `1 / cos(√z) = (cosSqrt z)⁻¹`,
whose simple poles lie along `(0, ∞)` at `+π² (k + 1/2)²`. -/
@[expose] def rogersCosBorel (z : ℂ) : ℂ := (cosSqrt z)⁻¹

theorem cosSqrt_sq (w : ℂ) : cosSqrt (w ^ 2) = Complex.cos w := by
  unfold cosSqrt
  have hsq : -(w ^ 2) = (w * I) ^ 2 := by rw [mul_pow, Complex.I_sq]; ring
  rw [hsq, coshSqrt_sq, Complex.cosh_mul_I]

private lemma mordellCosh_zero_iffF (z : ℂ) :
    coshSqrt z = 0 ↔ ∃ k : ℕ, z = -(mordellCoshFreq k : ℂ) := by
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := exists_sq_eq z
    rw [coshSqrt_sq, Complex.cosh] at hz
    have hsum : Complex.exp w + Complex.exp (-w) = 0 := by
      have := congrArg (· * 2) hz; simpa using this
    have hexp2 : Complex.exp (2 * w) = Complex.exp (I * (Real.pi : ℂ)) := by
      rw [exp_I_piF, show 2 * w = w + w by ring, Complex.exp_add]
      have hprod : Complex.exp w * Complex.exp (-w) = 1 := by rw [← Complex.exp_add]; simp
      linear_combination Complex.exp w * hsum - hprod
    obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp2
    have hw : w = I * (Real.pi * ((j : ℂ) + 1 / 2)) := by linear_combination hj / 2
    have hsq : w ^ 2 = -((Real.pi * ((j : ℝ) + 1 / 2)) ^ 2 : ℝ) := by
      rw [hw]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    by_cases hj0 : 0 ≤ j
    · refine ⟨j.toNat, ?_⟩
      rw [hsq, mordellCoshFreq, show ((j.toNat : ℕ) : ℝ) = (j : ℝ) by exact_mod_cast Int.toNat_of_nonneg hj0]
    · push Not at hj0
      refine ⟨(-j - 1).toNat, ?_⟩
      rw [hsq, mordellCoshFreq,
        show (((-j - 1).toNat : ℕ) : ℝ) = -(j : ℝ) - 1 by exact_mod_cast Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -j - 1)]
      congr 1; exact_mod_cast (show (Real.pi * ((j : ℝ) + 1 / 2)) ^ 2 = (Real.pi * (-(j : ℝ) - 1 + 1 / 2)) ^ 2 by ring)
  · rintro ⟨k, rfl⟩
    let r : ℝ := Real.pi * ((k : ℝ) + 1 / 2)
    have hsq : (I * (r : ℂ)) ^ 2 = -(mordellCoshFreq k : ℂ) := by
      rw [mordellCoshFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [← hsq, coshSqrt_sq, show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.cosh_mul_I,
      ← Complex.ofReal_cos, Complex.ofReal_eq_zero]
    exact Real.cos_eq_zero_iff.mpr ⟨(k : ℤ), by dsimp only [r]; push_cast; ring⟩

private lemma mordellCosh_deriv_ne_zeroF (k : ℕ) :
    deriv coshSqrt (-(mordellCoshFreq k : ℂ)) ≠ 0 := by
  let r : ℝ := Real.pi * ((k : ℝ) + 1 / 2)
  have hsq : (I * (r : ℂ)) ^ 2 = -(mordellCoshFreq k : ℂ) := by
    rw [mordellCoshFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hd := deriv_coshSqrt_sq (I * (r : ℂ)); rw [hsq] at hd
  intro h0; rw [h0, mul_zero] at hd
  rw [show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.sinh_mul_I, ← Complex.ofReal_sin] at hd
  have hsin0 : Real.sin r = 0 := Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp hd.symm).resolve_right Complex.I_ne_zero)
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hsin0
  have hint : 2 * m = 2 * (k : ℤ) + 1 := by
    have : ((2 * m : ℤ) : ℝ) = ((2 * (k : ℤ) + 1 : ℤ) : ℝ) := by
      push_cast; dsimp only [r] at hm; nlinarith [Real.pi_pos]
    exact_mod_cast this
  omega

/-- Concrete `HigherOrderBorelData` witness for the positive-ray Rogers false-theta Borel kernel
`1 / cos(√z)` along `θ₀ = 0` with simple poles at `+π² (k + 1/2)²`. -/
def rogersCosBorel_borelData :
    HigherOrderBorelData rogersCosBorel 0 mordellCoshFreq (fun _ => 1)
      (fun k s => if s = 1 then -(deriv coshSqrt (-(mordellCoshFreq k : ℂ)))⁻¹ else 0) where
  α₀ := 5 * Real.pi / 12
  θ := Real.pi / 3
  ε := 1 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by unfold mordellCoshFreq; positivity
  ω_mono := fun a b hab => by
    unfold mordellCoshFreq
    have hlt : (a : ℝ) < b := by exact_mod_cast hab
    have h1 := mul_lt_mul_of_pos_left (show (a : ℝ) + 1 / 2 < (b : ℝ) + 1 / 2 by linarith) Real.pi_pos
    have hpos : 0 < Real.pi * ((a : ℝ) + 1 / 2) := by positivity
    nlinarith
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun k => by simpa using neg_ne_zero.mpr (inv_ne_zero (mordellCosh_deriv_ne_zeroF k))
  analyticOn := by
    intro z hz
    simp only [rotatedPuncturedWedge, puncturedWedge, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
      one_mul, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
    have hne : cosSqrt z ≠ 0 := by
      unfold cosSqrt; intro h0
      obtain ⟨k, hk⟩ := (mordellCosh_zero_iffF (-z)).mp h0
      exact hz.2 ⟨k, by linear_combination hk⟩
    exact (AnalyticAt.comp (f := fun ζ : ℂ => -ζ) (g := coshSqrt)
      (coshSqrt_analyticAt (-z)) analyticAt_id.neg).inv hne
  pole_principalPart := fun k => by
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, Finset.Icc_self,
      Finset.sum_singleton, ↓reduceIte, pow_one]
    have hzero : cosSqrt (mordellCoshFreq k : ℂ) = 0 := (mordellCosh_zero_iffF _).mpr ⟨k, rfl⟩
    have hD_an : AnalyticAt ℂ cosSqrt (mordellCoshFreq k : ℂ) :=
      AnalyticAt.comp (f := fun ζ : ℂ => -ζ) (g := coshSqrt) (coshSqrt_analyticAt _) analyticAt_id.neg
    have hD_deriv : deriv cosSqrt (mordellCoshFreq k : ℂ) = -deriv coshSqrt (-(mordellCoshFreq k : ℂ)) := by
      have h1 : HasDerivAt cosSqrt (deriv coshSqrt (-(mordellCoshFreq k : ℂ)) * (-1)) (mordellCoshFreq k : ℂ) :=
        (coshSqrt_differentiable _).hasDerivAt.comp (mordellCoshFreq k : ℂ) (hasDerivAt_neg _)
      rw [h1.deriv]; ring
    have hD_ne : deriv cosSqrt (mordellCoshFreq k : ℂ) ≠ 0 := by
      rw [hD_deriv]; exact neg_ne_zero.mpr (mordellCosh_deriv_ne_zeroF k)
    have hlim := simple_pole_tendsto_of_analyticF (N := fun _ => (1 : ℂ)) analyticAt_const hD_an hzero hD_ne
    rw [hD_deriv] at hlim
    simpa [rogersCosBorel, one_div, div_neg] using hlim
  expType_plus := by
    have hfun : rogersCosBorel = fun z => (1 : ℂ) / cosSqrt z := funext fun z => by simp [rogersCosBorel, one_div]
    rw [hfun]
    refine expType_div_of_flank_boundF (R₀ := 16) (by norm_num) (norm_exp_I_realF _)
      ((coshSqrt_differentiable.continuous.comp continuous_neg).comp (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 1) (B := 0) (by norm_num) (by norm_num) (fun _ _ => by simp)
    · obtain ⟨k, hk⟩ := (mordellCosh_zero_iffF _).mp h0
      have hk' : Complex.exp (I * ((Real.pi + 1 * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ) = -(mordellCoshFreq k : ℂ) := by
        have hexp : -Complex.exp (I * ((0 + Real.pi / 3 : ℝ) : ℂ)) =
            Complex.exp (I * ((Real.pi + 1 * (Real.pi / 3) : ℝ) : ℂ)) := by
          rw [show (Real.pi + 1 * (Real.pi / 3) : ℝ) = Real.pi + Real.pi / 3 by ring,
            show (0 + Real.pi / 3 : ℝ) = Real.pi / 3 by ring,
            Complex.ofReal_add, mul_add, Complex.exp_add, exp_I_piF]; ring
        rw [← hexp]; linear_combination hk
      exact flank_ray_im_ne_zero 1 (Or.inl rfl) hv (pos := mordellCoshFreq k)
        (by unfold mordellCoshFreq; positivity) hk'
    · obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_rayF 1 (Or.inl rfl) (by linarith)
      have hexp : -(Complex.exp (I * ((0 + Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ)) = w ^ 2 := by
        rw [hw_sq, show (Real.pi + 1 * (Real.pi / 3) : ℝ) = Real.pi + Real.pi / 3 by ring,
          show (0 + Real.pi / 3 : ℝ) = Real.pi / 3 by ring,
          Complex.ofReal_add, mul_add, Complex.exp_add, exp_I_piF]; ring
      dsimp only [cosSqrt]; rw [hexp, coshSqrt_sq]
      have hge2 : 2 ≤ w.re := by
        have h4 : (4 : ℝ) ≤ Real.sqrt v := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
          exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
        linarith
      linarith [real_sinh_two_gt_twoF, real_sinh_monoF hge2, sinh_re_le_norm_coshF w]
  expType_minus := by
    have hfun : rogersCosBorel = fun z => (1 : ℂ) / cosSqrt z := funext fun z => by simp [rogersCosBorel, one_div]
    rw [hfun]
    refine expType_div_of_flank_boundF (R₀ := 16) (by norm_num) (norm_exp_I_realF _)
      ((coshSqrt_differentiable.continuous.comp continuous_neg).comp (continuous_const.mul Complex.continuous_ofReal))
      (fun v hv h0 => ?_) (fun v hv => ?_) (A := 1) (B := 0) (by norm_num) (by norm_num) (fun _ _ => by simp)
    · obtain ⟨k, hk⟩ := (mordellCosh_zero_iffF _).mp h0
      have hk' : Complex.exp (I * ((Real.pi + -1 * (Real.pi / 3) : ℝ) : ℂ)) * (v : ℂ) = -(mordellCoshFreq k : ℂ) := by
        have hexp : -Complex.exp (I * ((0 - Real.pi / 3 : ℝ) : ℂ)) =
            Complex.exp (I * ((Real.pi + -1 * (Real.pi / 3) : ℝ) : ℂ)) := by
          rw [show (Real.pi + -1 * (Real.pi / 3) : ℝ) = Real.pi + (-(Real.pi / 3)) by ring,
            show (0 - Real.pi / 3 : ℝ) = -(Real.pi / 3) by ring,
            Complex.ofReal_add, mul_add, Complex.exp_add, exp_I_piF]; ring
        rw [← hexp]; linear_combination hk
      exact flank_ray_im_ne_zero (-1) (Or.inr rfl) hv (pos := mordellCoshFreq k)
        (by unfold mordellCoshFreq; positivity) hk'
    · obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_rayF (-1) (Or.inr rfl) (by linarith)
      have hexp : -(Complex.exp (I * ((0 - Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ)) = w ^ 2 := by
        rw [hw_sq, show (Real.pi + -1 * (Real.pi / 3) : ℝ) = Real.pi + (-(Real.pi / 3)) by ring,
          show (0 - Real.pi / 3 : ℝ) = -(Real.pi / 3) by ring,
          Complex.ofReal_add, mul_add, Complex.exp_add, exp_I_piF]; ring
      dsimp only [cosSqrt]; rw [hexp, coshSqrt_sq]
      have hge2 : 2 ≤ w.re := by
        have h4 : (4 : ℝ) ≤ Real.sqrt v := by
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
          exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
        linarith
      linarith [real_sinh_two_gt_twoF, real_sinh_monoF hge2, sinh_re_le_norm_coshF w]

/-- **Theorem 4 (Positive-Ray Rogers False-Theta Borel Series D-Transcendence over `ℂ(u)`)**:
The formal Laplace series of `1 / cos(√ξ)` satisfies NO nonzero rational-coefficient ADE over `ℂ(u)`. -/
theorem rogersCosBorel_formal_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries rogersCosBorel) P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_rat_ade rogersCosBorel_borelData P hP

/-! ### 3. Flagship 5-Function Joint Differential Independence over `ℂ(u)` -/

/-- The 5-tuple of mock & false theta Borel kernels with pairwise disjoint pole lattices along `θ₀ = π`:
- `0`: Classical Zwegers–Mordell `1 / cosh(√z)` (denom `2`),
- `1`: Ramanujan 3rd-order mock theta `ω(q)` `(2 cosh(√z) - 1)⁻¹` (denom `3`, odd),
- `2`: Ramanujan 3rd-order mock theta `f(q)` `2 cosh(√z/2) / (2 cosh(√z) + 1)` (denom `3`, even),
- `3`: Weight-`3/2` false theta `∑ n q^{n²}` kernel `√z / sinh(√z)` (denom `1`),
- `4`: Kontsevich / `χ₁₂` false theta kernel `sinhSqrt z / (2 coshSqrt (4 z) - 1)` (denom `6`). -/
@[expose] def fiveMockFalseBorel : Fin 5 → ℂ → ℂ
  | 0 => mordellCoshBorel
  | 1 => mockThetaOmegaBorel
  | 2 => mockThetaFBorel
  | 3 => falseThetaSinhBorel
  | 4 => kontsevichFalseBorel

/-- The 5 pairwise disjoint pole-frequency lattices along `θ₀ = π`. -/
@[expose] def fiveMockFalseFreq : Fin 5 → ℕ → ℝ
  | 0 => mordellCoshFreq
  | 1 => mockThetaOmegaFreq
  | 2 => mockThetaFFreq
  | 3 => falseThetaSinhFreq
  | 4 => kontsevichFalseFreq

/-- Exact simple-pole residues for the 5-tuple of mock & false theta Borel kernels. -/
@[expose] def fiveMockFalseRes : Fin 5 → ℕ → ℂ
  | 0 => fun k => (deriv coshSqrt (-(mordellCoshFreq k : ℂ)))⁻¹
  | 1 => fun k => (deriv (fun z => 2 * coshSqrt z - 1) (-(mockThetaOmegaFreq k : ℂ)))⁻¹
  | 2 => fun m => (2 * coshSqrt (-(mockThetaFFreq m : ℂ) / 4)) /
      deriv (fun z => 2 * coshSqrt z + 1) (-(mockThetaFFreq m : ℂ))
  | 3 => fun k => (deriv sinhSqrt (-(falseThetaSinhFreq k : ℂ)))⁻¹
  | 4 => fun k => sinhSqrt (-(kontsevichFalseFreq k : ℂ)) /
      deriv (fun z => 2 * coshSqrt (4 * z) - 1) (-(kontsevichFalseFreq k : ℂ))

/-- The 5 concrete Mordell integrals proved jointly differentially independent over `ℂ(u)`. -/
@[expose] def fiveMockFalseMordell : Fin 5 → ℝ → ℂ
  | 0 => mordellCoshIntegral
  | 1 => mockThetaOmegaMordell
  | 2 => mockThetaFMordell
  | 3 => falseThetaSinhMordell
  | 4 => kontsevichFalseMordell

private lemma fiveMockFalseFreq_eq_six_scaled (i : Fin 5) (k : ℕ) :
    ∃ N : ℕ, 0 < N ∧ fiveMockFalseFreq i k = (Real.pi * (N : ℝ) / 6) ^ 2 ∧
      match i with
      | 0 => N % 6 = 3
      | 1 => N % 6 = 2 ∨ N % 6 = 4
      | 2 => N % 6 = 4 ∨ N % 6 = 2
      | 3 => N % 6 = 0
      | 4 => N % 6 = 1 ∨ N % 6 = 5 := by
  fin_cases i
  · refine ⟨3 * (2 * k + 1), by omega, ?_, by omega⟩
    dsimp [fiveMockFalseFreq, mordellCoshFreq]; push_cast; ring
  · refine ⟨2 * coprimeSixSeq k, by have := coprimeSixSeq_posF k; omega, ?_, ?_⟩
    · dsimp [fiveMockFalseFreq, mockThetaOmegaFreq]; push_cast; ring
    · rcases coprimeSixSeq_mod_six k with h1 | h5 <;> omega
  · refine ⟨4 * coprimeThreeSeq k, by unfold coprimeThreeSeq; split_ifs <;> omega, ?_, ?_⟩
    · dsimp [fiveMockFalseFreq, mockThetaFFreq]; push_cast; ring
    · unfold coprimeThreeSeq; split_ifs <;> omega
  · refine ⟨6 * (k + 1), by omega, ?_, by omega⟩
    dsimp [fiveMockFalseFreq, falseThetaSinhFreq]; push_cast; ring
  · refine ⟨coprimeSixSeq k, coprimeSixSeq_posF k, rfl, coprimeSixSeq_mod_six k⟩

private lemma fiveMockFalseFreq_disjoint :
    ∀ i₁ i₂ : Fin 5, i₁ ≠ i₂ → ∀ m₁ m₂ : ℕ, fiveMockFalseFreq i₁ m₁ ≠ fiveMockFalseFreq i₂ m₂ := by
  have h12 : ∀ a b : ℕ, (Real.pi * (a : ℝ) / 6) ^ 2 = (Real.pi * (b : ℝ) / 6) ^ 2 → a = b := by
    intro a b hab
    have h1 : Real.pi * (a : ℝ) / 6 = Real.pi * (b : ℝ) / 6 := by
      have ha : 0 ≤ Real.pi * (a : ℝ) / 6 := by positivity
      have hb : 0 ≤ Real.pi * (b : ℝ) / 6 := by positivity
      nlinarith
    have h2 : (a : ℝ) = (b : ℝ) := by nlinarith [Real.pi_pos]
    exact_mod_cast h2
  intro i₁ i₂ hne m₁ m₂ heq
  -- Note indices 1 and 2 are distinguished by mod 4 (1 has 2*(odd) ≡ 2 mod 4, 2 has 4*(coprime3) ≡ 0 mod 4)!
  fin_cases i₁ <;> fin_cases i₂
  all_goals first
    | exact absurd rfl hne
    | (
      -- Express both frequencies as (π * N / 6)^2 and derive an arithmetic contradiction
      have h_omega : False := by
        dsimp [fiveMockFalseFreq, mordellCoshFreq, mockThetaOmegaFreq, mockThetaFFreq,
          falseThetaSinhFreq, kontsevichFalseFreq] at heq
        have hnat : ∀ (a b : ℕ),
            (Real.pi * (a : ℝ) / 6) ^ 2 = (Real.pi * (b : ℝ) / 6) ^ 2 → a = b := h12
        first
        | (have h := hnat (3 * (2 * m₁ + 1)) (2 * coprimeSixSeq m₂) (by push_cast; linarith); omega)
        | (have h := hnat (3 * (2 * m₁ + 1)) (4 * coprimeThreeSeq m₂) (by push_cast; linarith); omega)
        | (have h := hnat (3 * (2 * m₁ + 1)) (6 * (m₂ + 1)) (by push_cast; linarith); omega)
        | (have h := hnat (3 * (2 * m₁ + 1)) (coprimeSixSeq m₂) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₂ with h1 | h5 <;> omega)
        | (have h := hnat (2 * coprimeSixSeq m₁) (3 * (2 * m₂ + 1)) (by push_cast; linarith); omega)
        | (have h := hnat (2 * coprimeSixSeq m₁) (4 * coprimeThreeSeq m₂) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₁ with h1 | h5 <;> omega)
        | (have h := hnat (2 * coprimeSixSeq m₁) (6 * (m₂ + 1)) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₁ with h1 | h5 <;> omega)
        | (have h := hnat (2 * coprimeSixSeq m₁) (coprimeSixSeq m₂) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₂ with h1 | h5 <;> omega)
        | (have h := hnat (4 * coprimeThreeSeq m₁) (3 * (2 * m₂ + 1)) (by push_cast; linarith); omega)
        | (have h := hnat (4 * coprimeThreeSeq m₁) (2 * coprimeSixSeq m₂) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₂ with h1 | h5 <;> omega)
        | (have h := hnat (4 * coprimeThreeSeq m₁) (6 * (m₂ + 1)) (by push_cast; linarith)
           unfold coprimeThreeSeq at h; split_ifs at h <;> omega)
        | (have h := hnat (4 * coprimeThreeSeq m₁) (coprimeSixSeq m₂) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₂ with h1 | h5 <;> omega)
        | (have h := hnat (6 * (m₁ + 1)) (3 * (2 * m₂ + 1)) (by push_cast; linarith); omega)
        | (have h := hnat (6 * (m₁ + 1)) (2 * coprimeSixSeq m₂) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₂ with h1 | h5 <;> omega)
        | (have h := hnat (6 * (m₁ + 1)) (4 * coprimeThreeSeq m₂) (by push_cast; linarith)
           unfold coprimeThreeSeq at h; split_ifs at h <;> omega)
        | (have h := hnat (6 * (m₁ + 1)) (coprimeSixSeq m₂) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₂ with h1 | h5 <;> omega)
        | (have h := hnat (coprimeSixSeq m₁) (3 * (2 * m₂ + 1)) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₁ with h1 | h5 <;> omega)
        | (have h := hnat (coprimeSixSeq m₁) (2 * coprimeSixSeq m₂) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₁ with h1 | h5 <;> omega)
        | (have h := hnat (coprimeSixSeq m₁) (4 * coprimeThreeSeq m₂) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₁ with h1 | h5 <;> omega)
        | (have h := hnat (coprimeSixSeq m₁) (6 * (m₂ + 1)) (by push_cast; linarith)
           rcases coprimeSixSeq_mod_six m₁ with h1 | h5 <;> omega)
      exact h_omega)

private lemma coprimeThreeSeq_monoF : StrictMono coprimeThreeSeq := fun a b hab => by
  unfold coprimeThreeSeq; split_ifs <;> omega

private lemma coprimeThreeSeq_posF (m : ℕ) : 0 < coprimeThreeSeq m := by
  unfold coprimeThreeSeq; split_ifs <;> omega

private lemma two_coshSqrt_add_one_eq_zero_iffF (z : ℂ) :
    2 * coshSqrt z + 1 = 0 ↔ ∃ m : ℕ, z = -(mockThetaFFreq m : ℂ) := by
  have hex3 : ∀ k : ℤ, k % 3 = 1 ∨ k % 3 = 2 → ∃ m : ℕ, (coprimeThreeSeq m : ℤ) = |k| := by
    intro k hk
    have hnat : k.natAbs % 3 = 1 ∨ k.natAbs % 3 = 2 := by omega
    rcases hnat with h1 | h2
    · refine ⟨2 * (k.natAbs / 3), ?_⟩
      unfold coprimeThreeSeq
      rw [show 2 * (k.natAbs / 3) / 2 = k.natAbs / 3 by omega,
          show 2 * (k.natAbs / 3) % 2 = 0 by omega, ite_eq_left_iff.mpr (fun h => absurd rfl h),
          show 3 * (k.natAbs / 3) + 1 = k.natAbs by omega, Int.natCast_natAbs]
    · refine ⟨2 * (k.natAbs / 3) + 1, ?_⟩
      unfold coprimeThreeSeq
      rw [show (2 * (k.natAbs / 3) + 1) / 2 = k.natAbs / 3 by omega,
          show (2 * (k.natAbs / 3) + 1) % 2 = 1 by omega, ite_eq_right_iff.mpr (fun h => by omega),
          show 3 * (k.natAbs / 3) + 2 = k.natAbs by omega, Int.natCast_natAbs]
  constructor
  · intro hz
    obtain ⟨w, rfl⟩ := exists_sq_eq z
    rw [coshSqrt_sq, Complex.cosh] at hz
    have hsum : Complex.exp w + Complex.exp (-w) = -1 := by linear_combination hz
    have hprod : Complex.exp w * Complex.exp (-w) = 1 := by rw [← Complex.exp_add]; simp
    have hquad : Complex.exp w ^ 2 + Complex.exp w + 1 = 0 := by
      linear_combination Complex.exp w * hsum - hprod
    let ζ : ℂ := Complex.exp (I * ((2 * Real.pi / 3 : ℝ) : ℂ))
    have hζ_sum : ζ + ζ⁻¹ = -1 := by
      dsimp only [ζ]; rw [← Complex.exp_neg]
      have h1 : Complex.exp (I * ((2 * Real.pi / 3 : ℝ) : ℂ)) + Complex.exp (-(I * ((2 * Real.pi / 3 : ℝ) : ℂ))) =
          2 * Complex.cos ((2 * Real.pi / 3 : ℝ) : ℂ) := by
        rw [Complex.cos, show I * ((2 * Real.pi / 3 : ℝ) : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) * I by ring, ← neg_mul]; ring
      rw [h1, ← Complex.ofReal_cos, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three]; push_cast; ring
    have hfac : (Complex.exp w - ζ) * (Complex.exp w - ζ⁻¹) = 0 := by
      have hζ_ne : ζ ≠ 0 := Complex.exp_ne_zero _
      linear_combination hquad - Complex.exp w * hζ_sum + mul_inv_cancel₀ hζ_ne
    rcases mul_eq_zero.mp hfac with hL | hR
    · obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp (sub_eq_zero.mp hL)
      let k : ℤ := 3 * j + 1
      have hw : w = I * ((2 * Real.pi * (k : ℝ) / 3 : ℝ) : ℂ) := by dsimp only [k]; rw [hj]; push_cast; ring
      obtain ⟨m, hm⟩ := hex3 k (Or.inl (by omega))
      refine ⟨m, ?_⟩; rw [hw, mockThetaFFreq]
      have hsq_k : ((coprimeThreeSeq m : ℝ)) ^ 2 = (k : ℝ) ^ 2 := by
        have h1 : (coprimeThreeSeq m : ℝ) = |(k : ℝ)| := by exact_mod_cast hm
        rw [h1, sq_abs]
      have hsq_kC : (coprimeThreeSeq m : ℂ) ^ 2 = (k : ℂ) ^ 2 := by exact_mod_cast hsq_k
      have hLHS : (I * ((2 * Real.pi * (k : ℝ) / 3 : ℝ) : ℂ)) ^ 2 = -(2 * (Real.pi : ℂ) * (k : ℂ) / 3) ^ 2 := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [hLHS]; push_cast; linear_combination -(4 * (Real.pi : ℂ) ^ 2 / 9) * hsq_kC.symm
    · have hexp : Complex.exp w = Complex.exp (-(I * ((2 * Real.pi / 3 : ℝ) : ℂ))) := by
        rw [Complex.exp_neg]; exact sub_eq_zero.mp hR
      obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
      let k : ℤ := 3 * j - 1
      have hw : w = I * ((2 * Real.pi * (k : ℝ) / 3 : ℝ) : ℂ) := by dsimp only [k]; rw [hj]; push_cast; ring
      obtain ⟨m, hm⟩ := hex3 k (Or.inr (by omega))
      refine ⟨m, ?_⟩; rw [hw, mockThetaFFreq]
      have hsq_k : ((coprimeThreeSeq m : ℝ)) ^ 2 = (k : ℝ) ^ 2 := by
        have h1 : (coprimeThreeSeq m : ℝ) = |(k : ℝ)| := by exact_mod_cast hm
        rw [h1, sq_abs]
      have hsq_kC : (coprimeThreeSeq m : ℂ) ^ 2 = (k : ℂ) ^ 2 := by exact_mod_cast hsq_k
      have hLHS : (I * ((2 * Real.pi * (k : ℝ) / 3 : ℝ) : ℂ)) ^ 2 = -(2 * (Real.pi : ℂ) * (k : ℂ) / 3) ^ 2 := by
        push_cast; ring_nf; rw [Complex.I_sq]; ring
      rw [hLHS]; push_cast; linear_combination -(4 * (Real.pi : ℂ) ^ 2 / 9) * hsq_kC.symm
  · rintro ⟨m, rfl⟩
    let r : ℝ := 2 * Real.pi * (coprimeThreeSeq m : ℝ) / 3
    have hsq : (I * (r : ℂ)) ^ 2 = -(mockThetaFFreq m : ℂ) := by
      rw [mockThetaFFreq]; dsimp only [r]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    rw [← hsq, coshSqrt_sq, show I * (r : ℂ) = (r : ℂ) * I by ring, Complex.cosh_mul_I, ← Complex.ofReal_cos]
    have hcos : Real.cos r = -(1 / 2) := by
      dsimp only [r, coprimeThreeSeq]; split_ifs
      · rw [show 2 * Real.pi * ((3 * (m / 2) + 1 : ℕ) : ℝ) / 3 =
            (Real.pi - Real.pi / 3) + ((m / 2 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring,
          Real.cos_add_nat_mul_two_pi, Real.cos_pi_sub, Real.cos_pi_div_three]
      · rw [show 2 * Real.pi * ((3 * (m / 2) + 2 : ℕ) : ℝ) / 3 =
            -(Real.pi - Real.pi / 3) + ((m / 2 + 1 : ℕ) : ℝ) * (2 * Real.pi) by push_cast; ring,
          Real.cos_add_nat_mul_two_pi, Real.cos_neg, Real.cos_pi_sub, Real.cos_pi_div_three]
    rw [hcos]; push_cast; ring

/-- Concrete `JointSimplePoleFamily` witness uniting the 5 mock & false theta Borel kernels
(`mordellCoshBorel`, `mockThetaOmegaBorel`, `mockThetaFBorel`, `falseThetaSinhBorel`,
`kontsevichFalseBorel`) along `θ₀ = π` with shared wedge `(5π/12, π/3, 1/2)`. -/
def fiveMockFalseFamily :
    JointSimplePoleFamily 5 fiveMockFalseBorel Real.pi fiveMockFalseFreq fiveMockFalseRes where
  α₀ := 5 * Real.pi / 12
  θ := Real.pi / 3
  ε := 1 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := fun i => by
    fin_cases i
    · unfold fiveMockFalseFreq mordellCoshFreq; positivity
    · unfold fiveMockFalseFreq mockThetaOmegaFreq; have := coprimeSixSeq_posF 0; positivity
    · unfold fiveMockFalseFreq mockThetaFFreq; have := coprimeThreeSeq_posF 0; positivity
    · exact falseThetaSinh_borelData.ω_pos
    · exact kontsevichFalse_borelData.ω_pos
  ω_mono := fun i => by
    fin_cases i
    · exact mordellCosh_borelData.ω_mono
    · exact mockThetaOmega_borelData.ω_mono
    · exact mockThetaF_borelData.ω_mono
    · exact falseThetaSinh_borelData.ω_mono
    · exact kontsevichFalse_borelData.ω_mono
  ω_unbounded := fun i B => by
    have h_quad : ∀ c : ℝ, 0 < c → ∃ m : ℕ, B < (c * ((m : ℝ) + 1)) ^ 2 := by
      intro c hc
      let M : ℕ := Nat.ceil ((max 1 B) / c)
      refine ⟨M, ?_⟩
      have hM : max 1 B ≤ c * (M : ℝ) := by
        have hceil := (div_le_iff₀ hc).mp (Nat.le_ceil ((max 1 B) / c))
        linarith
      have h1 : 1 < c * ((M : ℝ) + 1) := by linarith [le_max_left (1 : ℝ) B]
      have hB : B < c * ((M : ℝ) + 1) := by linarith [le_max_right (1 : ℝ) B]
      nlinarith
    fin_cases i
    · obtain ⟨m, hm⟩ := h_quad (Real.pi / 2) (by positivity)
      refine ⟨m, hm.trans_le ?_⟩
      unfold fiveMockFalseFreq mordellCoshFreq
      have h1 : Real.pi / 2 * ((m : ℝ) + 1) ≤ Real.pi * ((m : ℝ) + 1 / 2) := by
        nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) m]
      nlinarith [show 0 ≤ Real.pi / 2 * ((m : ℝ) + 1) by positivity]
    · obtain ⟨m, hm⟩ := h_quad (Real.pi / 3) (by positivity)
      refine ⟨m, hm.trans_le ?_⟩
      unfold fiveMockFalseFreq mockThetaOmegaFreq
      have hle : m + 1 ≤ coprimeSixSeq m := by unfold coprimeSixSeq; split_ifs <;> omega
      have hleR : ((m : ℝ) + 1) ≤ (coprimeSixSeq m : ℝ) := by exact_mod_cast hle
      have h1 : Real.pi / 3 * ((m : ℝ) + 1) ≤ Real.pi * (coprimeSixSeq m : ℝ) / 3 := by nlinarith [Real.pi_pos]
      nlinarith [show 0 ≤ Real.pi / 3 * ((m : ℝ) + 1) by positivity]
    · obtain ⟨m, hm⟩ := h_quad (2 * Real.pi / 3) (by positivity)
      refine ⟨m, hm.trans_le ?_⟩
      unfold fiveMockFalseFreq mockThetaFFreq
      have hle : m + 1 ≤ coprimeThreeSeq m := by unfold coprimeThreeSeq; split_ifs <;> omega
      have hleR : ((m : ℝ) + 1) ≤ (coprimeThreeSeq m : ℝ) := by exact_mod_cast hle
      have h1 : 2 * Real.pi / 3 * ((m : ℝ) + 1) ≤ 2 * Real.pi * (coprimeThreeSeq m : ℝ) / 3 := by nlinarith [Real.pi_pos]
      nlinarith [show 0 ≤ 2 * Real.pi / 3 * ((m : ℝ) + 1) by positivity]
    · obtain ⟨m, hm⟩ := h_quad Real.pi Real.pi_pos
      exact ⟨m, hm⟩
    · obtain ⟨m, hm⟩ := h_quad (Real.pi / 6) (by positivity)
      refine ⟨m, hm.trans_le ?_⟩
      unfold fiveMockFalseFreq kontsevichFalseFreq
      have hle : m + 1 ≤ coprimeSixSeq m := by unfold coprimeSixSeq; split_ifs <;> omega
      have hleR : ((m : ℝ) + 1) ≤ (coprimeSixSeq m : ℝ) := by exact_mod_cast hle
      have h1 : Real.pi / 6 * ((m : ℝ) + 1) ≤ Real.pi * (coprimeSixSeq m : ℝ) / 6 := by nlinarith [Real.pi_pos]
      nlinarith [show 0 ≤ Real.pi / 6 * ((m : ℝ) + 1) by positivity]
  ω_disjoint := fiveMockFalseFreq_disjoint
  res_ne_zero := fun i m => by
    fin_cases i
    · simpa [fiveMockFalseRes] using mordellCosh_borelData.pp_lead_ne_zero m
    · simpa [fiveMockFalseRes] using mockThetaOmega_borelData.pp_lead_ne_zero m
    · simpa [fiveMockFalseRes] using mockThetaF_borelData.pp_lead_ne_zero m
    · simpa [fiveMockFalseRes] using falseThetaSinh_borelData.pp_lead_ne_zero m
    · simpa [fiveMockFalseRes] using kontsevichFalse_borelData.pp_lead_ne_zero m
  analyticOn := fun i => by
    fin_cases i
    · intro z hz
      simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
      have hz' := hz.2; rw [exp_neg_I_piF] at hz'
      exact (coshSqrt_analyticAt z).inv fun h0 => by
        obtain ⟨k, hk⟩ := (mordellCosh_zero_iffF z).mp h0
        exact hz' ⟨k, by dsimp only [fiveMockFalseFreq]; rw [hk]; ring⟩
    · intro z hz
      simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
      have hz' := hz.2; rw [exp_neg_I_piF] at hz'
      exact ((analyticAt_const.mul (coshSqrt_analyticAt z)).sub analyticAt_const).inv fun h0 => by
        obtain ⟨k, hk⟩ := (two_coshSqrt_sub_one_eq_zero_iffF z).mp h0
        exact hz' ⟨k, by dsimp only [fiveMockFalseFreq]; rw [hk]; ring⟩
    · intro z hz
      simp only [rotatedPuncturedWedge, puncturedWedge, Set.mem_ofPred_eq, Set.mem_sdiff] at hz
      have hz' := hz.2; rw [exp_neg_I_piF] at hz'
      have hnum : AnalyticAt ℂ (fun ζ => 2 * coshSqrt (ζ / 4)) z :=
        analyticAt_const.mul (AnalyticAt.comp (f := fun ζ : ℂ => ζ / 4) (g := coshSqrt)
          (coshSqrt_analyticAt (z / 4)) (analyticAt_id.div analyticAt_const (by norm_num)))
      have hden : AnalyticAt ℂ (fun ζ => 2 * coshSqrt ζ + 1) z :=
        (analyticAt_const.mul (coshSqrt_analyticAt z)).add analyticAt_const
      exact hnum.div hden fun h0 => by
        obtain ⟨m, hm⟩ := (two_coshSqrt_add_one_eq_zero_iffF z).mp h0
        exact hz' ⟨m, by dsimp only [fiveMockFalseFreq]; rw [hm]; ring⟩
    · exact falseThetaSinh_borelData.analyticOn
    · exact kontsevichFalse_borelData.analyticOn
  pole_res := fun i m => by
    fin_cases i
    · simpa [fiveMockFalseBorel, fiveMockFalseFreq, fiveMockFalseRes, Finset.Icc_self] using
        mordellCosh_borelData.pole_principalPart m
    · simpa [fiveMockFalseBorel, fiveMockFalseFreq, fiveMockFalseRes, Finset.Icc_self] using
        mockThetaOmega_borelData.pole_principalPart m
    · simpa [fiveMockFalseBorel, fiveMockFalseFreq, fiveMockFalseRes, Finset.Icc_self] using
        mockThetaF_borelData.pole_principalPart m
    · simpa [fiveMockFalseBorel, fiveMockFalseFreq, fiveMockFalseRes, Finset.Icc_self] using
        falseThetaSinh_borelData.pole_principalPart m
    · simpa [fiveMockFalseBorel, fiveMockFalseFreq, fiveMockFalseRes, Finset.Icc_self] using
        kontsevichFalse_borelData.pole_principalPart m
  expType_plus := fun i => by
    fin_cases i
    · dsimp only [fiveMockFalseBorel]
      rw [show mordellCoshBorel = fun z => (1 : ℂ) / coshSqrt z from
        funext fun z => by simp [mordellCoshBorel, one_div] ]
      refine expType_div_of_flank_boundF (R₀ := 16) (by norm_num) (norm_exp_I_realF _)
        (coshSqrt_differentiable.continuous.comp (continuous_const.mul Complex.continuous_ofReal))
        (fun v hv h0 => by
          obtain ⟨k, hk⟩ := (mordellCosh_zero_iffF _).mp h0
          exact flank_ray_im_ne_zero 1 (Or.inl rfl) hv (pos := mordellCoshFreq k)
            (by unfold mordellCoshFreq; positivity) (by simpa using hk))
        (fun v hv => by
          obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_rayF 1 (Or.inl rfl) (by linarith)
          rw [show Complex.exp (I * ((Real.pi + Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by simpa using hw_sq.symm,
            coshSqrt_sq]
          have hge2 : 2 ≤ w.re := by
            have h4 : (4 : ℝ) ≤ Real.sqrt v := by
              rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
              exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
            linarith
          linarith [real_sinh_two_gt_twoF, real_sinh_monoF hge2, sinh_re_le_norm_coshF w])
        (A := 1) (B := 0) (by norm_num) (by norm_num) (fun _ _ => by simp)
    · dsimp only [fiveMockFalseBorel]
      rw [show mockThetaOmegaBorel = fun z => (1 : ℂ) / (2 * coshSqrt z - 1) from
        funext fun z => by simp [mockThetaOmegaBorel, one_div] ]
      refine expType_div_of_flank_boundF (R₀ := 16) (by norm_num) (norm_exp_I_realF _)
        (((continuous_const.mul coshSqrt_differentiable.continuous).sub continuous_const).comp
          (continuous_const.mul Complex.continuous_ofReal))
        (fun v hv h0 => by
          obtain ⟨k, hk⟩ := (two_coshSqrt_sub_one_eq_zero_iffF _).mp h0
          exact flank_ray_im_ne_zero 1 (Or.inl rfl) hv (pos := mockThetaOmegaFreq k)
            (by unfold mockThetaOmegaFreq; have := coprimeSixSeq_posF k; positivity) (by simpa using hk))
        (fun v hv => by
          obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_rayF 1 (Or.inl rfl) (by linarith)
          rw [show Complex.exp (I * ((Real.pi + Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by simpa using hw_sq.symm,
            coshSqrt_sq]
          have hge2 : 2 ≤ w.re := by
            have h4 : (4 : ℝ) ≤ Real.sqrt v := by
              rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
              exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
            linarith
          have htri := norm_add_le (2 * Complex.cosh w - 1) (1 : ℂ)
          rw [sub_add_cancel, norm_mul, Complex.norm_ofNat, norm_one] at htri
          linarith [real_sinh_two_gt_twoF, real_sinh_monoF hge2, sinh_re_le_norm_coshF w])
        (A := 1) (B := 0) (by norm_num) (by norm_num) (fun _ _ => by simp)
    · dsimp only [fiveMockFalseBorel, mockThetaFBorel]
      refine expType_div_of_flank_boundF (R₀ := 16) (by norm_num) (norm_exp_I_realF _)
        (((continuous_const.mul coshSqrt_differentiable.continuous).add continuous_const).comp
          (continuous_const.mul Complex.continuous_ofReal))
        (fun v hv h0 => by
          obtain ⟨m, hm⟩ := (two_coshSqrt_add_one_eq_zero_iffF _).mp h0
          exact flank_ray_im_ne_zero 1 (Or.inl rfl) hv (pos := mockThetaFFreq m)
            (by unfold mockThetaFFreq; have := coprimeThreeSeq_posF m; positivity) (by simpa using hm))
        (fun v hv => by
          obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_rayF 1 (Or.inl rfl) (by linarith)
          rw [show Complex.exp (I * ((Real.pi + Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by simpa using hw_sq.symm,
            coshSqrt_sq]
          have hge2 : 2 ≤ w.re := by
            have h4 : (4 : ℝ) ≤ Real.sqrt v := by
              rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
              exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
            linarith
          have htri := norm_sub_le (2 * Complex.cosh w + 1) (1 : ℂ)
          rw [add_sub_cancel_right, norm_mul, Complex.norm_ofNat, norm_one] at htri
          linarith [real_sinh_two_gt_twoF, real_sinh_monoF hge2, sinh_re_le_norm_coshF w])
        (A := 2 * Real.exp 1) (B := 1) (by positivity) (by norm_num) (fun v hv => by
          obtain ⟨w, hw_sq, _, hw_norm⟩ := exists_sqrt_on_flank_rayF 1 (Or.inl rfl) hv
          have hsq4 : (w / 2) ^ 2 = Complex.exp (I * ((Real.pi + Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) / 4 := by
            rw [div_pow, show (2 : ℂ) ^ 2 = 4 by norm_num, hw_sq]; simp
          rw [← hsq4, coshSqrt_sq, norm_mul, Complex.norm_ofNat, Complex.cosh, norm_div, Complex.norm_ofNat]
          have h1 : ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ ≤ 2 * Real.exp (‖w‖ / 2) := by
            calc ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖
                ≤ ‖Complex.exp (w / 2)‖ + ‖Complex.exp (-(w / 2))‖ := norm_add_le _ _
              _ = Real.exp (w / 2).re + Real.exp (-(w / 2)).re := by rw [Complex.norm_exp, Complex.norm_exp]
              _ ≤ Real.exp ‖w / 2‖ + Real.exp ‖-(w / 2)‖ :=
                  add_le_add (Real.exp_le_exp.mpr (Complex.re_le_norm _)) (Real.exp_le_exp.mpr (Complex.re_le_norm _))
              _ = 2 * Real.exp (‖w‖ / 2) := by rw [norm_neg, norm_div, Complex.norm_ofNat]; ring
          have hsq_le : Real.sqrt v / 2 ≤ 1 + v := by nlinarith [sq_nonneg (Real.sqrt v - 1), Real.sq_sqrt hv]
          calc 2 * (‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ / 2)
              = ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ := by ring
            _ ≤ 2 * Real.exp (Real.sqrt v / 2) := hw_norm ▸ h1
            _ ≤ 2 * Real.exp (1 + v) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsq_le) (by norm_num)
            _ = 2 * Real.exp 1 * Real.exp (1 * v) := by rw [Real.exp_add, one_mul]; ring)
    · exact falseThetaSinh_borelData.expType_plus
    · exact kontsevichFalse_borelData.expType_plus
  expType_minus := fun i => by
    fin_cases i
    · dsimp only [fiveMockFalseBorel]
      rw [show mordellCoshBorel = fun z => (1 : ℂ) / coshSqrt z from
        funext fun z => by simp [mordellCoshBorel, one_div] ]
      refine expType_div_of_flank_boundF (R₀ := 16) (by norm_num) (norm_exp_I_realF _)
        (coshSqrt_differentiable.continuous.comp (continuous_const.mul Complex.continuous_ofReal))
        (fun v hv h0 => by
          obtain ⟨k, hk⟩ := (mordellCosh_zero_iffF _).mp h0
          exact flank_ray_im_ne_zero (-1) (Or.inr rfl) hv (pos := mordellCoshFreq k)
            (by unfold mordellCoshFreq; positivity)
            (by rw [show Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring]; exact hk))
        (fun v hv => by
          obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_rayF (-1) (Or.inr rfl) (by linarith)
          rw [show Complex.exp (I * ((Real.pi - Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by
            rw [show Real.pi - Real.pi / 3 = Real.pi + -1 * (Real.pi / 3) by ring]; exact hw_sq.symm, coshSqrt_sq]
          have hge2 : 2 ≤ w.re := by
            have h4 : (4 : ℝ) ≤ Real.sqrt v := by
              rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
              exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
            linarith
          linarith [real_sinh_two_gt_twoF, real_sinh_monoF hge2, sinh_re_le_norm_coshF w])
        (A := 1) (B := 0) (by norm_num) (by norm_num) (fun _ _ => by simp)
    · dsimp only [fiveMockFalseBorel]
      rw [show mockThetaOmegaBorel = fun z => (1 : ℂ) / (2 * coshSqrt z - 1) from
        funext fun z => by simp [mockThetaOmegaBorel, one_div] ]
      refine expType_div_of_flank_boundF (R₀ := 16) (by norm_num) (norm_exp_I_realF _)
        (((continuous_const.mul coshSqrt_differentiable.continuous).sub continuous_const).comp
          (continuous_const.mul Complex.continuous_ofReal))
        (fun v hv h0 => by
          obtain ⟨k, hk⟩ := (two_coshSqrt_sub_one_eq_zero_iffF _).mp h0
          exact flank_ray_im_ne_zero (-1) (Or.inr rfl) hv (pos := mockThetaOmegaFreq k)
            (by unfold mockThetaOmegaFreq; have := coprimeSixSeq_posF k; positivity)
            (by rw [show Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring]; exact hk))
        (fun v hv => by
          obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_rayF (-1) (Or.inr rfl) (by linarith)
          rw [show Complex.exp (I * ((Real.pi - Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by
            rw [show Real.pi - Real.pi / 3 = Real.pi + -1 * (Real.pi / 3) by ring]; exact hw_sq.symm, coshSqrt_sq]
          have hge2 : 2 ≤ w.re := by
            have h4 : (4 : ℝ) ≤ Real.sqrt v := by
              rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
              exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
            linarith
          have htri := norm_add_le (2 * Complex.cosh w - 1) (1 : ℂ)
          rw [sub_add_cancel, norm_mul, Complex.norm_ofNat, norm_one] at htri
          linarith [real_sinh_two_gt_twoF, real_sinh_monoF hge2, sinh_re_le_norm_coshF w])
        (A := 1) (B := 0) (by norm_num) (by norm_num) (fun _ _ => by simp)
    · dsimp only [fiveMockFalseBorel, mockThetaFBorel]
      refine expType_div_of_flank_boundF (R₀ := 16) (by norm_num) (norm_exp_I_realF _)
        (((continuous_const.mul coshSqrt_differentiable.continuous).add continuous_const).comp
          (continuous_const.mul Complex.continuous_ofReal))
        (fun v hv h0 => by
          obtain ⟨m, hm⟩ := (two_coshSqrt_add_one_eq_zero_iffF _).mp h0
          exact flank_ray_im_ne_zero (-1) (Or.inr rfl) hv (pos := mockThetaFFreq m)
            (by unfold mockThetaFFreq; have := coprimeThreeSeq_posF m; positivity)
            (by rw [show Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring]; exact hm))
        (fun v hv => by
          obtain ⟨w, hw_sq, hw_re, _⟩ := exists_sqrt_on_flank_rayF (-1) (Or.inr rfl) (by linarith)
          rw [show Complex.exp (I * ((Real.pi - Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) = w ^ 2 by
            rw [show Real.pi - Real.pi / 3 = Real.pi + -1 * (Real.pi / 3) by ring]; exact hw_sq.symm, coshSqrt_sq]
          have hge2 : 2 ≤ w.re := by
            have h4 : (4 : ℝ) ≤ Real.sqrt v := by
              rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
              exact Real.sqrt_le_sqrt (by linarith : (4 : ℝ) ^ 2 ≤ v)
            linarith
          have htri := norm_sub_le (2 * Complex.cosh w + 1) (1 : ℂ)
          rw [add_sub_cancel_right, norm_mul, Complex.norm_ofNat, norm_one] at htri
          linarith [real_sinh_two_gt_twoF, real_sinh_monoF hge2, sinh_re_le_norm_coshF w])
        (A := 2 * Real.exp 1) (B := 1) (by positivity) (by norm_num) (fun v hv => by
          obtain ⟨w, hw_sq, _, hw_norm⟩ := exists_sqrt_on_flank_rayF (-1) (Or.inr rfl) hv
          have hsq4 : (w / 2) ^ 2 = Complex.exp (I * ((Real.pi - Real.pi / 3 : ℝ) : ℂ)) * (v : ℂ) / 4 := by
            rw [div_pow, show (2 : ℂ) ^ 2 = 4 by norm_num, hw_sq,
              show Real.pi + -1 * (Real.pi / 3) = Real.pi - Real.pi / 3 by ring]
          rw [← hsq4, coshSqrt_sq, norm_mul, Complex.norm_ofNat, Complex.cosh, norm_div, Complex.norm_ofNat]
          have h1 : ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ ≤ 2 * Real.exp (‖w‖ / 2) := by
            calc ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖
                ≤ ‖Complex.exp (w / 2)‖ + ‖Complex.exp (-(w / 2))‖ := norm_add_le _ _
              _ = Real.exp (w / 2).re + Real.exp (-(w / 2)).re := by rw [Complex.norm_exp, Complex.norm_exp]
              _ ≤ Real.exp ‖w / 2‖ + Real.exp ‖-(w / 2)‖ :=
                  add_le_add (Real.exp_le_exp.mpr (Complex.re_le_norm _)) (Real.exp_le_exp.mpr (Complex.re_le_norm _))
              _ = 2 * Real.exp (‖w‖ / 2) := by rw [norm_neg, norm_div, Complex.norm_ofNat]; ring
          have hsq_le : Real.sqrt v / 2 ≤ 1 + v := by nlinarith [sq_nonneg (Real.sqrt v - 1), Real.sq_sqrt hv]
          calc 2 * (‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ / 2)
              = ‖Complex.exp (w / 2) + Complex.exp (-(w / 2))‖ := by ring
            _ ≤ 2 * Real.exp (Real.sqrt v / 2) := hw_norm ▸ h1
            _ ≤ 2 * Real.exp (1 + v) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hsq_le) (by norm_num)
            _ = 2 * Real.exp 1 * Real.exp (1 * v) := by rw [Real.exp_add, one_mul]; ring)
    · exact falseThetaSinh_borelData.expType_minus
    · exact kontsevichFalse_borelData.expType_minus

/-- **Flagship Theorem 5 (5-Tuple Joint Differential Independence of Mock & False Theta Mordell Integrals over `ℂ(u)`)**:
The 5 concrete Mordell integrals
`(mordellCoshIntegral, mockThetaOmegaMordell, mockThetaFMordell, falseThetaSinhMordell, kontsevichFalseMordell)`
satisfy NO nonzero joint rational-coefficient algebraic differential equation over `ℂ(u)`. -/
theorem five_mock_false_mordell_joint_no_rat_ade {r : ℕ}
    (P : MvPolynomial (Fin 5 × Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun ij : Fin 5 × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fiveMockFalseMordell ij.1) u)
        (jointEvalRatU P (u : ℂ)) = 0) : P = 0 := by
  have heq : ∀ i : Fin 5, fiveMockFalseMordell i = mordellIntegral (fiveMockFalseBorel i) := fun i => by
    fin_cases i
    · exact funext mordellCoshIntegral_eq
    · exact funext mockThetaOmegaMordell_eq
    · exact funext mockThetaFMordell_eq
    · exact funext falseThetaSinhMordell_eq
    · exact funext kontsevichFalseMordell_eq
  have hP' : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun ij : Fin 5 × Fin (r + 1) =>
        iteratedDeriv ij.2.val (mordellIntegral (fiveMockFalseBorel ij.1)) u)
        (jointEvalRatU P (u : ℂ)) = 0 := by
    simpa only [heq] using hP
  have hana0 : ∀ i : Fin 5, AnalyticAt ℂ (fiveMockFalseBorel i) 0 := fun i => by
    refine fiveMockFalseFamily.analyticOn i 0 ?_
    simp only [rotatedPuncturedWedge, puncturedWedge, mul_zero, Set.mem_ofPred_eq, Set.mem_sdiff]
    refine ⟨Or.inl (by simp [Metric.mem_ball, fiveMockFalseFamily.hε_pos]), ?_⟩
    rintro ⟨m, hm⟩
    have hpos : 0 < fiveMockFalseFreq i m :=
      lt_of_lt_of_le (fiveMockFalseFamily.ω_pos i) ((fiveMockFalseFamily.ω_mono i).monotone (Nat.zero_le m))
    exact hpos.ne' (Complex.ofReal_eq_zero.mp hm)
  have hcont : ∀ i : Fin 5, ContinuousOn (fun ξ : ℝ => fiveMockFalseBorel i (ξ : ℂ)) (Set.Ici 0) := fun i => by
    fin_cases i
    · intro ξ hξ
      have hne : coshSqrt (ξ : ℂ) ≠ 0 := by
        rw [show (ξ : ℂ) = ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 by rw [← Complex.ofReal_pow, Real.sq_sqrt hξ],
          coshSqrt_sq, ← Complex.ofReal_cosh]
        exact Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
      exact ((coshSqrt_analyticAt (ξ : ℂ)).inv hne).continuousAt.comp
        Complex.continuous_ofReal.continuousAt |>.continuousWithinAt
    · intro ξ hξ
      have hne : 2 * coshSqrt (ξ : ℂ) - 1 ≠ 0 := by
        rw [show (ξ : ℂ) = ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 by rw [← Complex.ofReal_pow, Real.sq_sqrt hξ],
          coshSqrt_sq, ← Complex.ofReal_cosh,
          show (2 : ℂ) * (Real.cosh (Real.sqrt ξ) : ℂ) - 1 = ((2 * Real.cosh (Real.sqrt ξ) - 1 : ℝ) : ℂ) by push_cast; rfl]
        exact Complex.ofReal_ne_zero.mpr (by linarith [real_one_le_coshF (Real.sqrt ξ)])
      exact (((analyticAt_const.mul (coshSqrt_analyticAt (ξ : ℂ))).sub analyticAt_const).inv hne).continuousAt.comp
        Complex.continuous_ofReal.continuousAt |>.continuousWithinAt
    · intro ξ hξ
      have hne : 2 * coshSqrt (ξ : ℂ) + 1 ≠ 0 := by
        rw [show (ξ : ℂ) = ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 by rw [← Complex.ofReal_pow, Real.sq_sqrt hξ],
          coshSqrt_sq, ← Complex.ofReal_cosh,
          show (2 : ℂ) * (Real.cosh (Real.sqrt ξ) : ℂ) + 1 = ((2 * Real.cosh (Real.sqrt ξ) + 1 : ℝ) : ℂ) by push_cast; rfl]
        exact Complex.ofReal_ne_zero.mpr (by linarith [Real.cosh_pos (Real.sqrt ξ)])
      have hnum : AnalyticAt ℂ (fun ζ => 2 * coshSqrt (ζ / 4)) (ξ : ℂ) :=
        analyticAt_const.mul (AnalyticAt.comp (f := fun ζ : ℂ => ζ / 4) (g := coshSqrt)
          (coshSqrt_analyticAt _) (analyticAt_id.div analyticAt_const (by norm_num)))
      have hden : AnalyticAt ℂ (fun ζ => 2 * coshSqrt ζ + 1) (ξ : ℂ) :=
        (analyticAt_const.mul (coshSqrt_analyticAt (ξ : ℂ))).add analyticAt_const
      exact (hnum.div hden hne).continuousAt.comp Complex.continuous_ofReal.continuousAt |>.continuousWithinAt
    · exact falseThetaSinhBorel_cont
    · exact kontsevichFalseBorel_cont
  have hbd : ∀ i : Fin 5, ∀ ξ : ℝ, 0 ≤ ξ → ‖fiveMockFalseBorel i (ξ : ℂ)‖ ≤ 1 := fun i ξ hξ => by
    fin_cases i
    · dsimp only [fiveMockFalseBorel, mordellCoshBorel]
      rw [show (ξ : ℂ) = ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 by rw [← Complex.ofReal_pow, Real.sq_sqrt hξ],
        coshSqrt_sq, ← Complex.ofReal_cosh, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (Real.cosh_pos _).le]
      exact inv_le_one_of_one_le₀ (real_one_le_coshF _)
    · dsimp only [fiveMockFalseBorel, mockThetaOmegaBorel]
      rw [show (ξ : ℂ) = ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 by rw [← Complex.ofReal_pow, Real.sq_sqrt hξ],
        coshSqrt_sq, ← Complex.ofReal_cosh,
        show (2 : ℂ) * (Real.cosh (Real.sqrt ξ) : ℂ) - 1 = ((2 * Real.cosh (Real.sqrt ξ) - 1 : ℝ) : ℂ) by push_cast; rfl,
        norm_inv, Complex.norm_real, Real.norm_of_nonneg (by linarith [real_one_le_coshF (Real.sqrt ξ)])]
      exact inv_le_one_of_one_le₀ (by linarith [real_one_le_coshF (Real.sqrt ξ)])
    · dsimp only [fiveMockFalseBorel, mockThetaFBorel]
      rw [show (ξ : ℂ) / 4 = ((Real.sqrt ξ / 2 : ℝ) : ℂ) ^ 2 by
          rw [← Complex.ofReal_pow, div_pow, Real.sq_sqrt hξ]; push_cast; norm_num,
        show (ξ : ℂ) = ((Real.sqrt ξ : ℝ) : ℂ) ^ 2 by rw [← Complex.ofReal_pow, Real.sq_sqrt hξ],
        coshSqrt_sq, coshSqrt_sq, ← Complex.ofReal_cosh, ← Complex.ofReal_cosh,
        show (2 : ℂ) * (Real.cosh (Real.sqrt ξ / 2) : ℂ) = ((2 * Real.cosh (Real.sqrt ξ / 2) : ℝ) : ℂ) by push_cast; rfl,
        show (2 : ℂ) * (Real.cosh (Real.sqrt ξ) : ℂ) + 1 = ((2 * Real.cosh (Real.sqrt ξ) + 1 : ℝ) : ℂ) by push_cast; rfl,
        norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by linarith [Real.cosh_pos (Real.sqrt ξ)]),
        div_le_one (by linarith [Real.cosh_pos (Real.sqrt ξ)])]
      linarith [real_cosh_mono_nonnegF (by positivity : 0 ≤ Real.sqrt ξ / 2)
        (by linarith [Real.sqrt_nonneg ξ] : Real.sqrt ξ / 2 ≤ Real.sqrt ξ)]
    · exact falseThetaSinhBorel_real_bound ξ hξ
    · exact kontsevichFalseBorel_real_bound ξ hξ
  exact joint_mordellIntegral_no_rat_ade fiveMockFalseFamily hana0 hcont hbd P hP'

/-! ### 4. Explicit True-Theta / Modular, Borel-Kernel, & Quadrant-III D-Algebraic Controls -/

/-- **Control A (Ramanujan ODEs → Chazy Order-3 Autonomous ODE)**:
In ANY commutative `ℂ`-algebra `R` with derivation `D : Derivation ℂ R R`, any triple
`(E2, E4, E6)` satisfying Ramanujan's modular ODEs satisfies Chazy's exact order-3 autonomous ODE
`2 D³ E₂ - 2 E₂ D² E₂ + 3 (D E₂)² = 0`. -/
theorem ramanujan_chazy_ode {R : Type*} [CommRing R] [Algebra ℂ R]
    (D : Derivation ℂ R R) {E2 E4 E6 : R}
    (h2 : (12 : R) * D E2 = E2 ^ 2 - E4)
    (h4 : (3 : R) * D E4 = E2 * E4 - E6)
    (h6 : (2 : R) * D E6 = E2 * E6 - E4 ^ 2) :
    (2 : R) * D (D (D E2)) - 2 * E2 * D (D E2) + 3 * (D E2) ^ 2 = 0 := by
  have hmulC : ∀ (c : ℂ) (x : R), D (algebraMap ℂ R c * x) = algebraMap ℂ R c * D x := fun c x => by
    rw [Derivation.leibniz, D.map_algebraMap, smul_zero, add_zero, smul_eq_mul]
  have h12 : ∀ x : R, D ((12 : R) * x) = 12 * D x := fun x => by
    simpa only [map_ofNat] using hmulC 12 x
  have h3 : ∀ x : R, D ((3 : R) * x) = 3 * D x := fun x => by
    simpa only [map_ofNat] using hmulC 3 x
  have h2c : ∀ x : R, D ((2 : R) * x) = 2 * D x := fun x => by
    simpa only [map_ofNat] using hmulC 2 x
  have hd2 : (12 : R) * D (D E2) = 2 * E2 * D E2 - D E4 := by
    have h := congrArg D h2
    rw [h12, map_sub, Derivation.leibniz_pow] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  have hd3 : (12 : R) * D (D (D E2)) = 2 * (D E2) ^ 2 + 2 * E2 * D (D E2) - D (D E4) := by
    have h := congrArg D hd2
    rw [h12, map_sub, mul_assoc (2 : R), h2c, Derivation.leibniz] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  have hd4 : (3 : R) * D (D E4) = D E2 * E4 + E2 * D E4 - D E6 := by
    have h := congrArg D h4
    rw [h3, map_sub, Derivation.leibniz] at h
    simp only [smul_eq_mul] at h
    linear_combination h
  have hmul : (36 : R) * ((2 : R) * D (D (D E2)) - 2 * E2 * D (D E2) + 3 * (D E2) ^ 2) = 0 := by
    linear_combination 6 * hd3 - 2 * hd4 + h6 + E2 * h4 - 5 * E2 * hd2 - E4 * h2 + 10 * D E2 * h2
  have hinv : (algebraMap ℂ R (36 : ℂ)⁻¹) * ((36 : R) *
      ((2 : R) * D (D (D E2)) - 2 * E2 * D (D E2) + 3 * (D E2) ^ 2)) = 0 := by
    rw [hmul, mul_zero]
  rw [← mul_assoc, ← map_ofNat (algebraMap ℂ R) 36, ← map_mul,
    inv_mul_cancel₀ (by norm_num : (36 : ℂ) ≠ 0), map_one, one_mul] at hinv
  exact hinv

/-- **Control B (True Gaussian Mordell Integral D-Algebraicity)**:
Contrasting the 5 D-transcendental mock/false theta Mordell integrals, the true Gaussian Mordell
integral `G(u) = ∫_0^∞ e^{-u x²} x e^{-x²} dx` equals `(2 (u + 1))⁻¹` for all `u > 0` and
satisfies the nonzero autonomous order-1 ODE `Y₁ + 2 Y₀² = 0` over `ℂ`. -/
@[expose] def trueGaussianMordell (u : ℝ) : ℂ :=
  ∫ x in Set.Ioi (0 : ℝ), Complex.exp (-(u : ℂ) * (x : ℂ) ^ 2) * (x : ℂ) * Complex.exp (-(x : ℂ) ^ 2)

theorem trueGaussianMordell_eq {u : ℝ} (hu : 0 < u) :
    trueGaussianMordell u = (2 * ((u : ℂ) + 1))⁻¹ := by
  have hcov := mordellIntegral_eq_half_laplace (fun z : ℂ => Complex.exp (-z)) u
  have h1 : trueGaussianMordell u = mordellIntegral (fun z : ℂ => Complex.exp (-z)) u := rfl
  rw [h1, hcov, laplaceTransform]
  have hrew : (fun ξ : ℝ => Complex.exp (-(u : ℂ) * (ξ : ℂ)) * Complex.exp (-(ξ : ℂ))) =
      fun ξ : ℝ => ((Real.exp (-(u + 1) * ξ) : ℝ) : ℂ) := by
    funext ξ; rw [← Complex.exp_add, Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [hrew, integral_complex_ofReal, integral_exp_mul_Ioi (show -(u + 1) < 0 by linarith) 0]
  simp only [mul_zero, Real.exp_zero, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_add]
  have hne : (u : ℂ) + 1 ≠ 0 := by
    rw [show (u : ℂ) + 1 = ((u + 1 : ℝ) : ℂ) by push_cast; rfl]
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  field_simp [hne]

theorem trueGaussianMordell_is_d_algebraic :
    ∃ (r : ℕ) (P : MvPolynomial (Fin (r + 1)) ℂ), P ≠ 0 ∧
      ∀ᶠ u : ℝ in Filter.atTop, MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val trueGaussianMordell u) P = 0 := by
  refine ⟨1, MvPolynomial.X 1 + 2 * MvPolynomial.X 0 ^ 2, ?_, ?_⟩
  · intro h0
    have hev := congrArg (MvPolynomial.eval (fun j : Fin 2 => if j = 1 then (1 : ℂ) else 0)) h0
    simp at hev
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    simp only [map_add, map_mul, map_ofNat, map_pow, MvPolynomial.eval_X, Fin.val_one, Fin.val_zero,
      iteratedDeriv_zero, iteratedDeriv_one]
    have hev : trueGaussianMordell =ᶠ[𝓝 u] fun t : ℝ => (2 * ((t : ℂ) + 1))⁻¹ :=
      Filter.eventually_of_mem (Ioi_mem_nhds hu) fun t ht => trueGaussianMordell_eq ht
    have hne : 2 * ((u : ℂ) + 1) ≠ 0 := by
      rw [show 2 * ((u : ℂ) + 1) = ((2 * (u + 1) : ℝ) : ℂ) by push_cast; rfl]
      exact Complex.ofReal_ne_zero.mpr (by linarith)
    have hd : HasDerivAt (fun t : ℝ => (2 * ((t : ℂ) + 1))⁻¹) (-(2 : ℂ) / (2 * ((u : ℂ) + 1)) ^ 2) u := by
      have h1 : HasDerivAt (fun t : ℝ => 2 * ((t : ℂ) + 1)) 2 u := by
        simpa using (((hasDerivAt_id u).ofReal_comp.add_const (1 : ℂ)).const_mul (2 : ℂ))
      exact h1.inv hne
    rw [hev.deriv_eq, hd.deriv, trueGaussianMordell_eq hu]
    field_simp [hne]; ring

/-- **Control C (Borel-Kernel D-Algebraicity vs. Laplace-Transform D-Transcendence)**:
The Zwegers–Mordell Borel kernel `φ(ξ) = 1 / cosh(√ξ) = mordellCoshBorel ξ` ITSELF satisfies the
explicit nonzero order-1 polynomial ODE `4 ξ (φ')² - φ² + φ⁴ = 0` for all `ξ > 0` (D-algebraic!),
even though its Laplace/Mordell transform `mordellCoshIntegral` is D-transcendental over `ℂ(u)`. -/
theorem sechSqrt_kernel_is_d_algebraic :
    ∃ (r : ℕ) (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)), P ≠ 0 ∧
      ∀ ξ : ℝ, 0 < ξ → MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => mordellCoshBorel (t : ℂ)) ξ)
        (evalU P (ξ : ℂ)) = 0 := by
  let P : MvPolynomial (Fin 2) (Polynomial ℂ) :=
    MvPolynomial.C (Polynomial.C 4 * Polynomial.X) * MvPolynomial.X 1 ^ 2 -
      MvPolynomial.X 0 ^ 2 + MvPolynomial.X 0 ^ 4
  refine ⟨1, P, ?_, fun ξ hξ => ?_⟩
  · intro h0
    have hev := congrArg (fun Q : MvPolynomial (Fin 2) (Polynomial ℂ) =>
      Polynomial.eval (1 : ℂ) (MvPolynomial.eval (fun j : Fin 2 => if j = 1 then (1 : Polynomial ℂ) else 0) Q)) h0
    dsimp only [P] at hev
    simp at hev
  · dsimp only [P, evalU]
    simp only [map_add, map_sub, map_mul, map_pow, MvPolynomial.map_C, MvPolynomial.map_X,
      Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.val_one, Fin.val_zero,
      iteratedDeriv_zero, iteratedDeriv_one]
    have hev : (fun t : ℝ => mordellCoshBorel (t : ℂ)) =ᶠ[𝓝 ξ]
        fun t : ℝ => ((Real.cosh (Real.sqrt t))⁻¹ : ℂ) := by
      filter_upwards [Ioi_mem_nhds hξ] with t ht
      unfold mordellCoshBorel
      rw [show (t : ℂ) = ((Real.sqrt t : ℝ) : ℂ) ^ 2 by rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt ht)],
        coshSqrt_sq, ← Complex.ofReal_cosh]
    have hsr_pos : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr hξ
    have hcosh_ne : Real.cosh (Real.sqrt ξ) ≠ 0 := (Real.cosh_pos _).ne'
    have hd_sqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt ξ)) ξ := by
      have hsq_deriv : HasDerivAt (fun s : ℝ => s ^ 2) (2 * Real.sqrt ξ) (Real.sqrt ξ) := by
        simpa [pow_one] using hasDerivAt_pow 2 (Real.sqrt ξ)
      have hne2 : (2 * Real.sqrt ξ : ℝ) ≠ 0 := by positivity
      have hleft : ∀ᶠ t : ℝ in 𝓝 ξ, (Real.sqrt t) ^ 2 = t :=
        Filter.eventually_of_mem (Ioi_mem_nhds hξ) fun t ht => Real.sq_sqrt (le_of_lt ht)
      have hinv := hsq_deriv.of_local_left_inverse Real.continuous_sqrt.continuousAt hne2 hleft
      simpa [one_div] using hinv
    have hd_real : HasDerivAt (fun t : ℝ => (Real.cosh (Real.sqrt t))⁻¹)
        (-(Real.sinh (Real.sqrt ξ) / (2 * Real.sqrt ξ)) / (Real.cosh (Real.sqrt ξ)) ^ 2) ξ := by
      have h1 : HasDerivAt (fun t : ℝ => Real.cosh (Real.sqrt t))
          (Real.sinh (Real.sqrt ξ) * (1 / (2 * Real.sqrt ξ))) ξ :=
        (hasDerivAt_real_cosh (Real.sqrt ξ)).comp ξ hd_sqrt
      have h2 := h1.inv hcosh_ne
      convert h2 using 1; ring
    have hd_cplx : HasDerivAt (fun t : ℝ => ((Real.cosh (Real.sqrt t))⁻¹ : ℂ))
        (((-(Real.sinh (Real.sqrt ξ) / (2 * Real.sqrt ξ)) / (Real.cosh (Real.sqrt ξ)) ^ 2 : ℝ) : ℂ)) ξ := by
      simpa using hd_real.ofReal_comp
    have hval : mordellCoshBorel (ξ : ℂ) = ((Real.cosh (Real.sqrt ξ))⁻¹ : ℂ) := hev.self_of_nhds
    rw [hev.deriv_eq, hd_cplx.deriv, hval]
    have hsq : Real.sqrt ξ ^ 2 = ξ := Real.sq_sqrt hξ.le
    have hhyp : Real.cosh (Real.sqrt ξ) ^ 2 - Real.sinh (Real.sqrt ξ) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
    norm_cast
    field_simp [hcosh_ne, hsr_pos.ne']
    nlinarith [hsq, hhyp]

/-- **Control D (Quadrant-III Witness: Exact 1st-Order Linear `q`-Difference Equation for Rogers's False Theta)**:
The bivariate Rogers false theta `Ψ(x, q) = ∑_{n ≥ 0} (-1)^n x^n q^{n(n+1)/2}` satisfies the exact
1st-order linear `q`-difference equation `Ψ(x, q) = 1 - x q Ψ(q x, q)` for every `x ∈ ℂ` and
`‖q‖ < 1`, placing Rogers's false theta in Quadrant III (`D-transcendental` × `$q$-holonomic`). -/
@[expose] def rogersFalseThetaBiv (x q : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * x ^ n * q ^ (n * (n + 1) / 2)

private lemma rogersFalseThetaBiv_summable (x : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ => (-1 : ℂ) ^ n * x ^ n * q ^ (n * (n + 1) / 2)) := by
  by_cases hq0 : q = 0
  · subst hq0
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have hn0 : n ≠ 0 := by simpa using hn
    have hpos : 0 < n * (n + 1) / 2 := by
      have : 2 ≤ n * (n + 1) := by cases n with | zero => contradiction | succ k => nlinarith
      omega
    simp [zero_pow hpos.ne']
  · have hq_pos : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖x‖ * ‖q‖ ^ (N / 2) ≤ 1 / 2 := by
      have htend : Tendsto (fun m : ℕ => ‖x‖ * ‖q‖ ^ m) atTop (𝓝 (‖x‖ * 0)) :=
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq).const_mul ‖x‖
      rw [mul_zero] at htend
      obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp htend (1 / 2) (by norm_num)
      refine ⟨2 * M, ?_⟩
      have h1 := hM M le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1
      rw [show 2 * M / 2 = M by omega]; exact h1.le
    refine (summable_nat_add_iff N).1 ?_
    have hgeom : Summable (fun k : ℕ => ((1 / 2 : ℝ) ^ k) * (1 / 2) ^ N) :=
      (summable_geometric_two).mul_right _
    refine hgeom.of_norm_bounded fun k => ?_
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow, norm_pow]
    have hdiv : (N / 2) * (k + N) ≤ (k + N) * (k + N + 1) / 2 := by
      have h1 : 2 * ((N / 2) * (k + N)) ≤ (k + N) * (k + N + 1) := by
        have : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
        nlinarith
      exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr (by linarith)
    have hqpow : ‖q‖ ^ ((k + N) * (k + N + 1) / 2) ≤ (‖q‖ ^ (N / 2)) ^ (k + N) := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one (norm_nonneg q) hq.le hdiv
    calc ‖x‖ ^ (k + N) * ‖q‖ ^ ((k + N) * (k + N + 1) / 2)
        ≤ ‖x‖ ^ (k + N) * (‖q‖ ^ (N / 2)) ^ (k + N) :=
          mul_le_mul_of_nonneg_left hqpow (pow_nonneg (norm_nonneg x) _)
      _ = (‖x‖ * ‖q‖ ^ (N / 2)) ^ (k + N) := (mul_pow _ _ _).symm
      _ ≤ (1 / 2 : ℝ) ^ (k + N) := pow_le_pow_left₀ (by positivity) hN _
      _ = (1 / 2 : ℝ) ^ k * (1 / 2) ^ N := pow_add _ _ _

theorem rogers_false_theta_qdiff_control (x : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    rogersFalseThetaBiv x q = 1 - x * q * rogersFalseThetaBiv (q * x) q := by
  unfold rogersFalseThetaBiv
  rw [(rogersFalseThetaBiv_summable x hq).tsum_eq_zero_add]
  simp only [pow_zero, mul_one, zero_mul, Nat.zero_div]
  rw [← tsum_mul_left, sub_eq_add_neg, ← tsum_neg]
  congr 1
  refine tsum_congr fun n => ?_
  have htri : (n + 1) * (n + 1 + 1) / 2 = n * (n + 1) / 2 + (n + 1) := by
    have h2 : 2 ∣ n * (n + 1) := Nat.even_mul_succ_self n |>.two_dvd
    obtain ⟨m, hm⟩ := h2
    have h3 : (n + 1) * (n + 1 + 1) = 2 * (m + (n + 1)) := by linarith
    rw [h3, hm, Nat.mul_div_cancel_left _ (by norm_num), Nat.mul_div_cancel_left _ (by norm_num)]
  rw [htri, pow_add q, pow_succ (-1 : ℂ), pow_succ x, pow_succ q, mul_pow]
  ring

end
end PakPrimes.FalseThetaDichotomy
