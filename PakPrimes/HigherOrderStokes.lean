module

public import PakPrimes.GeneralTheorem2
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.Divisors

/-! # General Sectorial Higher-Order-Pole Non-Autonomous Stokes–Vandermonde Criterion

This module formalizes the **General Sectorial Higher-Order-Pole Non-Autonomous
Stokes–Vandermonde Criterion** (Wave 2 / Theorem PY-1 end-to-end in Lean 4):

1. **Specifications (`rotatedBorelWedge`, `rotatedPuncturedWedge`, `HigherOrderBorelData`,
   `formalEvalPoly`, `formalEvalRat`)**:
   - Arbitrary rotated ray `θ₀ : ℝ` with poles at `exp (I * θ₀) * ω m` (`0 < ω 0 < ω 1 < ...`).
   - Arbitrary finite pole orders `ord : ℕ → ℕ` (`1 ≤ ord m`) with principal part coefficients
     `pp m s` (`1 ≤ s ≤ ord m`) and nonzero leading coefficient `pp m (ord m) ≠ 0`.
   - Non-autonomous polynomial differential equations over `ℂ[u]` (`Polynomial ℂ`) and `ℂ(u)`
     (`RatFunc ℂ`) evaluated inside `LaurentSeries ℂ` (`ℂ((1/u))`).
2. **Rotation Reduction & Polynomial Coefficient Clearing (`scaleSubst`, `rotPoly`, `revPoly`)**:
   Reduces arbitrary rotation `θ₀ : ℝ` to `θ₀ = 0` via `φ_rot z := φ (exp (I * θ₀) * z)` and
   simultaneous rescaling of `u` and `Y_j`.
3. **Commuting Higher-Order Operators & Non-Degenerate Top-`u`-Degree Extraction (`L_op`,
   `D_freq_higher`, `D_freq_top_of_L_op_eq_zero`)**:
   Avoids `P_trap` (`u`-degree mixing in `Y`-constant terms) by choosing minimal `Y`-total-degree
   `Pmin`, eliminating all `r + 1` poles via `L_op` before extracting the top `u`-degree
   `Y`-dependent component `P_top`, then applying complex Vandermonde descent.
4. **Higher-Order Triangle Residue Formula & Non-Autonomous Stokes Bridge**:
   Proves `triIntegral_mul_inv_sub_pow` for arbitrary order `s ≥ 1` via iterated `dslope` + FTC,
   establishes the exact polynomial-amplitude Stokes jump expansion, and connects to `PolyBorelExpr`.
5. **Tier-1 Non-Vacuity Instantiations**:
   Constructs `HigherOrderBorelData` directly on:
   - the double-pole trigamma Borel series `∑_{n ≥ 1} 1 / (n - ξ)^2` (and rotated versions),
   - the Lambert divisor double-pole Borel series `∑_{n ≥ 1} d(n) / (n - ξ)^2`, and
   - general Dirichlet-pole series `∑_{n ≥ 1} c(n) / (e^{iθ₀} n - ξ)^p` for `p ≥ 2`.
-/

set_option maxHeartbeats 1200000

public section
namespace PakPrimes.HigherOrderStokes

open Complex Real Filter MeasureTheory Set MvPolynomial Matrix
open PakPrimes.BorelStokesVandermonde
open PakPrimes.GeneralTheorem2
open scoped Topology Interval

noncomputable section

/-! ### 1. Public Specifications -/

/-- Open rotated Borel wedge `e^{i θ₀} • borelWedge α₀ ε`. -/
@[expose] def rotatedBorelWedge (θ₀ α₀ ε : ℝ) : Set ℂ :=
  {z : ℂ | Complex.exp (-I * (θ₀ : ℂ)) * z ∈ borelWedge α₀ ε}

/-- Open rotated punctured wedge `e^{i θ₀} • puncturedWedge α₀ ε ω`, avoiding `e^{i θ₀} ω m`. -/
@[expose] def rotatedPuncturedWedge (θ₀ α₀ ε : ℝ) (ω : ℕ → ℝ) : Set ℂ :=
  {z : ℂ | Complex.exp (-I * (θ₀ : ℂ)) * z ∈ puncturedWedge α₀ ε ω}

/-- Complex-analytic hypotheses for a Borel transform `φ` along a rotated ray `e^{i θ₀}`
with poles at `e^{i θ₀} ω m` of arbitrary finite orders `ord m ≥ 1`, principal part coefficients
`pp m s` (`1 ≤ s ≤ ord m`) with `pp m (ord m) ≠ 0`, and exponential type along two flanking rays
`e^{i (θ₀ ± θ)}`. -/
structure HigherOrderBorelData
    (φ : ℂ → ℂ) (θ₀ : ℝ) (ω : ℕ → ℝ) (ord : ℕ → ℕ) (pp : ℕ → ℕ → ℂ) where
  α₀ : ℝ
  θ : ℝ
  ε : ℝ
  hθ_pos : 0 < θ
  hθ_lt : θ < α₀
  hα₀_lt : α₀ < Real.pi / 2
  hε_pos : 0 < ε
  ω_pos : 0 < ω 0
  ω_mono : StrictMono ω
  ord_pos : ∀ m : ℕ, 1 ≤ ord m
  pp_lead_ne_zero : ∀ m : ℕ, pp m (ord m) ≠ 0
  analyticOn : AnalyticOnNhd ℂ φ (rotatedPuncturedWedge θ₀ α₀ ε ω)
  pole_principalPart : ∀ m : ℕ, ∃ L : ℂ,
    Filter.Tendsto
      (fun z : ℂ => φ z - ∑ s ∈ Finset.Icc 1 (ord m),
        pp m s / (z - Complex.exp (I * (θ₀ : ℂ)) * (ω m : ℂ)) ^ s)
      (𝓝[≠] (Complex.exp (I * (θ₀ : ℂ)) * (ω m : ℂ))) (𝓝 L)
  expType_plus : ExpType (Minor.pull (Complex.exp (I * ((θ₀ + θ : ℝ) : ℂ))) φ)
  expType_minus : ExpType (Minor.pull (Complex.exp (I * ((θ₀ - θ : ℝ) : ℂ))) φ)

/-- Formal variable `u = w⁻¹` inside `LaurentSeries ℂ` (`w = 1/u`). -/
@[expose] def uLaurent : LaurentSeries ℂ :=
  HahnSeries.single (-1 : ℤ) (1 : ℂ)

/-- Embedding `ℂ[u] →+* ℂ((1/u))` sending `u ↦ w⁻¹ = uLaurent`. -/
@[expose] def polyToLaurent : Polynomial ℂ →+* LaurentSeries ℂ :=
  (Polynomial.aeval uLaurent : Polynomial ℂ →ₐ[ℂ] LaurentSeries ℂ).toRingHom

/-- Formal evaluation of a non-autonomous differential polynomial `P ∈ ℂ[u][Y_0, ..., Y_r]`
at `S ∈ ℂ[[1/u]]` inside `LaurentSeries ℂ`. -/
@[expose] def formalEvalPoly {r : ℕ} (S : PowerSeries ℂ)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) : LaurentSeries ℂ :=
  MvPolynomial.eval₂ polyToLaurent
    (fun j : Fin (r + 1) => ((d_u^[j.val] S : PowerSeries ℂ) : LaurentSeries ℂ)) P

/-- Evaluation of the `Polynomial ℂ` coefficients of `P` at `u : ℂ`. -/
@[expose] def evalU {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (u : ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  MvPolynomial.map (Polynomial.evalRingHom u) P

/-! ### 2. Coefficient Clearing (`revPoly`, `formalEvalW`), `RatFunc` Lift, and Rotation -/

private lemma uLaurent_pow (k : ℕ) :
    uLaurent ^ k = HahnSeries.single (-(k : ℤ)) (1 : ℂ) := by
  induction k with
  | zero => simp [uLaurent]
  | succ k ih =>
    rw [pow_succ, ih, uLaurent, HahnSeries.single_mul_single, one_mul]
    have hidx : -(k : ℤ) + (-1 : ℤ) = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hidx]

/-- Reversed polynomial `w^N p(1/w)` in `w = 1/u` for `p : Polynomial ℂ`. -/
private def revPoly (N : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k)

private lemma poly_finset_sum_coeff {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (m : ℕ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  simpa only [Polynomial.lcoeff_apply] using map_sum (Polynomial.lcoeff ℂ m) f s

private lemma revPoly_eval_inv {N : ℕ} (p : Polynomial ℂ) (hp : p.natDegree ≤ N)
    {u : ℂ} (hu : u ≠ 0) :
    (revPoly N p).eval u⁻¹ = u⁻¹ ^ N * p.eval u := by
  have hsum : p = ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k :=
    Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
  conv_rhs => rw [hsum]
  change Polynomial.evalRingHom u⁻¹ (revPoly N p) = u⁻¹ ^ N * Polynomial.evalRingHom u _
  simp only [revPoly, map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    map_pow, Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have heq : u⁻¹ ^ (N - k) = u⁻¹ ^ N * u ^ k := by
    calc u⁻¹ ^ (N - k) = u⁻¹ ^ (N - k) * (u⁻¹ ^ k * u ^ k) := by
          rw [← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]
      _ = (u⁻¹ ^ (N - k) * u⁻¹ ^ k) * u ^ k := by ring
      _ = u⁻¹ ^ N * u ^ k := by rw [← pow_add, Nat.sub_add_cancel hk_le]
  rw [heq]
  ring

private lemma single_mul_polyToLaurent {N : ℕ} (p : Polynomial ℂ) (hp : p.natDegree ≤ N) :
    HahnSeries.single (N : ℤ) (1 : ℂ) * polyToLaurent p =
      (((revPoly N p : Polynomial ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
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
  have hR : (((revPoly N p : Polynomial ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ∑ k ∈ Finset.range (N + 1),
        HahnSeries.C (p.coeff k) *
          ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ (N - k) := by
    unfold revPoly
    change HahnSeries.ofPowerSeries ℤ ℂ
      (Polynomial.coeToPowerSeries.ringHom
        (∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k))) = _
    simp only [map_sum, map_mul, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, HahnSeries.ofPowerSeries_C, Polynomial.coe_X]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [uLaurent_pow k]
  have hX : ((PowerSeries.X : PowerSeries ℂ) : LaurentSeries ℂ) ^ (N - k) =
      HahnSeries.single ((N - k : ℕ) : ℤ) (1 : ℂ) := by
    rw [← PowerSeries.coe_pow, HahnSeries.ofPowerSeries_X_pow]
  rw [hX, ← mul_assoc, mul_comm (HahnSeries.single (N : ℤ) 1) (HahnSeries.C (p.coeff k)),
    mul_assoc, HahnSeries.single_mul_single, one_mul]
  have hidx : (N : ℤ) + -(k : ℤ) = ((N - k : ℕ) : ℤ) := by omega
  rw [hidx, HahnSeries.C_apply, HahnSeries.single_mul_single]

private lemma polyToLaurent_injective : Function.Injective polyToLaurent := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  by_contra hp0
  have hsingle := single_mul_polyToLaurent p le_rfl
  rw [hp, mul_zero] at hsingle
  have hps : ((revPoly p.natDegree p : Polynomial ℂ) : PowerSeries ℂ) = 0 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ) (hsingle.symm.trans (map_zero _).symm)
  have hpoly : revPoly p.natDegree p = 0 := Polynomial.coe_inj.mp hps
  have hcoeff0 : (revPoly p.natDegree p).coeff 0 = 0 := by rw [hpoly]; simp
  rw [revPoly, poly_finset_sum_coeff] at hcoeff0
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

/-- Embedding `ℂ(u) →+* ℂ((1/u))` extending `polyToLaurent`. -/
@[expose] def ratToLaurent : RatFunc ℂ →+* LaurentSeries ℂ :=
  RatFunc.liftRingHom polyToLaurent fun p hp => by
    change polyToLaurent p ∈ nonZeroDivisors (LaurentSeries ℂ)
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp ⊢
    intro h0
    exact hp (polyToLaurent_injective (h0.trans (map_zero polyToLaurent).symm))

/-- Formal evaluation of a non-autonomous rational-coefficient differential polynomial
`P ∈ ℂ(u)[Y_0, ..., Y_r]` at `S ∈ ℂ[[1/u]]` inside `LaurentSeries ℂ`. -/
@[expose] def formalEvalRat {r : ℕ} (S : PowerSeries ℂ)
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) : LaurentSeries ℂ :=
  MvPolynomial.eval₂ ratToLaurent
    (fun j : Fin (r + 1) => ((d_u^[j.val] S : PowerSeries ℂ) : LaurentSeries ℂ)) P

private def maxUDeg {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) : ℕ :=
  P.support.sup fun α => (P.coeff α).natDegree

private lemma natDegree_le_maxUDeg {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (α : Fin (r + 1) →₀ ℕ) : (P.coeff α).natDegree ≤ maxUDeg P := by
  by_cases hα : α ∈ P.support
  · exact Finset.le_sup (f := fun α => (P.coeff α).natDegree) hα
  · rw [MvPolynomial.notMem_support_iff.mp hα, Polynomial.natDegree_zero]
    exact Nat.zero_le _

private def revMvPoly {r : ℕ} (N : ℕ) (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  ∑ α ∈ P.support, MvPolynomial.monomial α (revPoly N (P.coeff α))

private lemma revMvPoly_coeff {r : ℕ} (N : ℕ) (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (α : Fin (r + 1) →₀ ℕ) :
    (revMvPoly N P).coeff α = revPoly N (P.coeff α) := by
  unfold revMvPoly
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, Finset.sum_eq_zero]
    · simp [revPoly]
    · intro β hβ
      have hne : β ≠ α := fun h => hα (h ▸ hβ)
      simp [hne]

private lemma evalU_revMvPoly {r : ℕ} {N : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hN : ∀ α, (P.coeff α).natDegree ≤ N) {u : ℂ} (hu : u ≠ 0) :
    evalU (revMvPoly N P) u⁻¹ = (u⁻¹ ^ N) • evalU P u := by
  classical
  ext α
  simp only [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, revMvPoly_coeff,
    MvPolynomial.coeff_smul, smul_eq_mul]
  exact revPoly_eval_inv (P.coeff α) (hN α) hu

/-- Formal evaluation in `PowerSeries ℂ` for polynomials whose `Polynomial ℂ` coefficients
live in `w = 1/u`. -/
private def formalEvalW {r : ℕ} (S : PowerSeries ℂ)
    (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) : PowerSeries ℂ :=
  MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom (fun j : Fin (r + 1) => d_u^[j.val] S) Q

private lemma formalEvalW_eq_zero_iff_formalEvalPoly {r : ℕ} (S : PowerSeries ℂ)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) {N : ℕ}
    (hN : ∀ α, (P.coeff α).natDegree ≤ N) :
    formalEvalW S (revMvPoly N P) = 0 ↔ formalEvalPoly S P = 0 := by
  have hlink : HahnSeries.single (N : ℤ) (1 : ℂ) * formalEvalPoly S P =
      ((formalEvalW S (revMvPoly N P) : PowerSeries ℂ) : LaurentSeries ℂ) := by
    have hP_sum : P = ∑ α ∈ P.support, MvPolynomial.monomial α (P.coeff α) := MvPolynomial.as_sum P
    conv_lhs => rw [hP_sum]
    unfold formalEvalPoly formalEvalW revMvPoly
    rw [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_sum, Finset.mul_sum]
    simp_rw [MvPolynomial.eval₂_monomial]
    change ∑ α ∈ P.support, HahnSeries.single (N : ℤ) 1 *
        (polyToLaurent (P.coeff α) * α.prod fun i e =>
          ((d_u^[i.val] S : PowerSeries ℂ) : LaurentSeries ℂ) ^ e) =
      HahnSeries.ofPowerSeries ℤ ℂ
        (∑ α ∈ P.support, Polynomial.coeToPowerSeries.ringHom (revPoly N (P.coeff α)) *
          α.prod fun i e => (d_u^[i.val] S) ^ e)
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hpow_eq : (α.prod fun i e => ((d_u^[i.val] S : PowerSeries ℂ) : LaurentSeries ℂ) ^ e) =
        ((α.prod fun i e => (d_u^[i.val] S) ^ e : PowerSeries ℂ) : LaurentSeries ℂ) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [hpow_eq, ← mul_assoc, single_mul_polyToLaurent (P.coeff α) (hN α),
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

/-- Scaling substitution `w ↦ μ * w` on `PowerSeries ℂ`. -/
private def scaleSubstFun (μ : ℂ) (S : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => μ ^ n * PowerSeries.coeff n S

@[simp] private lemma scaleSubstFun_coeff (μ : ℂ) (S : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (scaleSubstFun μ S) = μ ^ n * PowerSeries.coeff n S :=
  PowerSeries.coeff_mk n _

private def scaleSubst (μ : ℂ) : PowerSeries ℂ →+* PowerSeries ℂ where
  toFun := scaleSubstFun μ
  map_one' := by
    ext n
    cases n with
    | zero => simp
    | succ n => simp
  map_mul' S T := by
    ext n
    simp only [scaleSubstFun_coeff, PowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hp, pow_add]
    ring
  map_zero' := by
    ext n
    simp
  map_add' S T := by
    ext n
    simp only [scaleSubstFun_coeff, map_add, mul_add]

@[simp] private lemma scaleSubst_coeff (μ : ℂ) (S : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (scaleSubst μ S) = μ ^ n * PowerSeries.coeff n S :=
  scaleSubstFun_coeff μ S n

private lemma scaleSubst_injective {μ : ℂ} (hμ : μ ≠ 0) : Function.Injective (scaleSubst μ) := by
  rw [injective_iff_map_eq_zero]
  intro S hS
  ext n
  have hn := congrArg (PowerSeries.coeff n) hS
  simp only [scaleSubst_coeff, map_zero] at hn
  exact (mul_eq_zero.mp hn).resolve_left (pow_ne_zero n hμ)

private lemma coeff_comp_C_mul_X (p : Polynomial ℂ) (μ : ℂ) (k : ℕ) :
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

private lemma scaleSubst_coe_poly (μ : ℂ) (p : Polynomial ℂ) :
    scaleSubst μ (p : PowerSeries ℂ) =
      ((p.comp (Polynomial.C μ * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) := by
  ext n
  rw [scaleSubst_coeff, Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_comp_C_mul_X]

private lemma scaleSubst_revPoly (μ : ℂ) (hμ : μ ≠ 0) {N : ℕ} (p : Polynomial ℂ) :
    scaleSubst μ ((revPoly N p : Polynomial ℂ) : PowerSeries ℂ) =
      PowerSeries.C (μ ^ N) * ((revPoly N (p.comp (Polynomial.C μ⁻¹ * Polynomial.X)) : Polynomial ℂ) : PowerSeries ℂ) := by
  rw [scaleSubst_coe_poly, ← Polynomial.coe_C, ← Polynomial.coe_mul, Polynomial.coe_inj]
  ext m
  rw [coeff_comp_C_mul_X, Polynomial.coeff_C_mul]
  simp only [revPoly, poly_finset_sum_coeff, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X_pow, coeff_comp_C_mul_X]
  split_ifs with hmk
  · subst hmk
    have hpow : μ ^ (N - k) = μ ^ N * μ⁻¹ ^ k := by
      rw [inv_pow, ← div_eq_mul_inv, eq_div_iff (pow_ne_zero k hμ), ← pow_add,
        Nat.sub_add_cancel hk_le]
    rw [hpow]
    ring
  · ring

private lemma d_u_scaleSubst {μ : ℂ} (hμ : μ ≠ 0) (S : PowerSeries ℂ) :
    d_u (scaleSubst μ S) = PowerSeries.C μ⁻¹ * scaleSubst μ (d_u S) := by
  ext n
  cases n with
  | zero =>
    change -(PowerSeries.coeff 0 (PowerSeries.X ^ 2 * PowerSeries.derivative (scaleSubst μ S))) =
      PowerSeries.coeff 0 (PowerSeries.C μ⁻¹ * scaleSubst μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
    rw [PowerSeries.coeff_C_mul, scaleSubst_coeff, map_neg, PowerSeries.coeff_X_pow_mul']
    simp [PowerSeries.coeff_X_pow_mul']
  | succ n =>
    cases n with
    | zero =>
      change -(PowerSeries.coeff 1 (PowerSeries.X ^ 2 * PowerSeries.derivative (scaleSubst μ S))) =
        PowerSeries.coeff 1 (PowerSeries.C μ⁻¹ * scaleSubst μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
      rw [PowerSeries.coeff_C_mul, scaleSubst_coeff, map_neg, PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_X_pow_mul']
      simp
    | succ m =>
      change -(PowerSeries.coeff (m + 2) (PowerSeries.X ^ 2 * PowerSeries.derivative (scaleSubst μ S))) =
        PowerSeries.coeff (m + 2) (PowerSeries.C μ⁻¹ * scaleSubst μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
      rw [PowerSeries.coeff_C_mul, scaleSubst_coeff, map_neg, PowerSeries.coeff_X_pow_mul',
        PowerSeries.coeff_X_pow_mul']
      split_ifs with hle2
      · simp only [Nat.add_sub_cancel, PowerSeries.coeff_derivative, scaleSubst_coeff]
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ']
        field_simp [hμ]
        ring
      · omega

private lemma iteratedDeriv_comp_const_mul_near_zero {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    (μ : ℂ) (k : ℕ) :
    ∀ᶠ z in 𝓝 (0 : ℂ),
      iteratedDeriv k (fun w => φ (μ * w)) z = μ ^ k * iteratedDeriv k φ (μ * z) := by
  induction k with
  | zero => exact Filter.Eventually.of_forall fun _ => by simp
  | succ k ih =>
    have hdk_anal : AnalyticAt ℂ (iteratedDeriv k φ) 0 := by
      clear ih
      induction k generalizing φ with
      | zero => simpa using hφ
      | succ m ihm =>
        rw [iteratedDeriv_succ']
        exact ihm hφ.deriv
    have hcont : ContinuousAt (fun z : ℂ => μ * z) 0 := continuousAt_const.mul continuousAt_id
    have hdk_diff : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (iteratedDeriv k φ) (μ * z) := by
      have this' := hdk_anal.eventually_analyticAt
      rw [show (0 : ℂ) = μ * 0 by ring] at this'
      exact (hcont.tendsto.eventually this').mono fun z hz => hz.differentiableAt
    filter_upwards [ih.eventually_nhds, hdk_diff] with z hzeq hzdiff
    have hderiv_eq : deriv (iteratedDeriv k (fun w => φ (μ * w))) z =
        deriv (fun w => μ ^ k * iteratedDeriv k φ (μ * w)) z :=
      Filter.EventuallyEq.deriv_eq hzeq
    rw [iteratedDeriv_succ, hderiv_eq]
    have hchain : HasDerivAt (fun w => μ ^ k * iteratedDeriv k φ (μ * w))
        (μ ^ k * (deriv (iteratedDeriv k φ) (μ * z) * μ)) z :=
      (hzdiff.hasDerivAt.comp z (((hasDerivAt_id z).const_mul μ).congr_deriv (mul_one μ))).const_mul (μ ^ k)
    rw [hchain.deriv, iteratedDeriv_succ]
    ring

private lemma iteratedDeriv_comp_const_mul_zero {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    (μ : ℂ) (k : ℕ) :
    iteratedDeriv k (fun z => φ (μ * z)) 0 = μ ^ k * iteratedDeriv k φ 0 := by
  simpa using (iteratedDeriv_comp_const_mul_near_zero hφ μ k).self_of_nhds

private lemma d_u_C_mul (c : ℂ) (S : PowerSeries ℂ) :
    d_u (PowerSeries.C c * S) = PowerSeries.C c * d_u S := by
  ext n
  cases n with
  | zero => simp [d_u]
  | succ n =>
    cases n with
    | zero => simp [d_u, PowerSeries.coeff_X_pow_mul']
    | succ m =>
      simp only [d_u, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
      split_ifs with h
      · simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul]
        ring
      · simp

private lemma d_u_iter_formalSeries_rot {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    {μ : ℂ} (hμ : μ ≠ 0) (j : ℕ) :
    d_u^[j] (formalSeries (fun z => φ (μ * z))) =
      PowerSeries.C (μ⁻¹ ^ (j + 1)) * scaleSubst μ (d_u^[j] (formalSeries φ)) := by
  have h0 : formalSeries (fun z => φ (μ * z)) =
      PowerSeries.C μ⁻¹ * scaleSubst μ (formalSeries φ) := by
    ext n
    cases n with
    | zero => simp [formalSeries]
    | succ k =>
      simp only [formalSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, scaleSubst_coeff]
      rw [iteratedDeriv_comp_const_mul_zero hφ μ k, pow_succ']
      field_simp [hμ]
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      d_u_C_mul, d_u_scaleSubst hμ, ← mul_assoc, ← map_mul, ← pow_succ]

/-- Rotation ring homomorphism on `MvPolynomial (Fin (r + 1)) (Polynomial ℂ)` corresponding
to `ξ ↦ μ * ξ`, `u ↦ μ⁻¹ * ũ`, `Y_j ↦ μ^{j+1} * Ỹ_j`. -/
private def rotPoly (r : ℕ) (μ : ℂ) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) →+* MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (Polynomial.compRingHom (Polynomial.C μ⁻¹ * Polynomial.X)))
    (fun j : Fin (r + 1) => MvPolynomial.C (Polynomial.C (μ ^ (j.val + 1))) * MvPolynomial.X j)

private lemma prod_support_pow_eq_univ {r : ℕ} (α : Fin (r + 1) →₀ ℕ) (f : Fin (r + 1) → ℂ) :
    (∏ j ∈ α.support, f j ^ α j) = ∏ j : Fin (r + 1), f j ^ α j := by
  refine Finset.prod_subset (Finset.subset_univ _) fun j _ hnot => ?_
  rw [Finsupp.notMem_support_iff.mp hnot, pow_zero]

private lemma rotPoly_coeff {r : ℕ} (μ : ℂ) (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (α : Fin (r + 1) →₀ ℕ) :
    (rotPoly r μ P).coeff α =
      Polynomial.C (∏ j ∈ α.support, (μ ^ (j.val + 1)) ^ α j) *
        (P.coeff α).comp (Polynomial.C μ⁻¹ * Polynomial.X) := by
  classical
  induction P using MvPolynomial.induction_on generalizing α with
  | C p =>
    simp only [rotPoly, MvPolynomial.eval₂Hom_C, RingHom.comp_apply, MvPolynomial.coeff_C,
      Polynomial.coe_compRingHom_apply]
    split_ifs with hα
    · subst hα; simp
    · simp
  | add A B hA hB =>
    rw [map_add, show (rotPoly r μ A + rotPoly r μ B).coeff α =
        (rotPoly r μ A).coeff α + (rotPoly r μ B).coeff α from rfl,
      hA, hB, show (A + B).coeff α = A.coeff α + B.coeff α from rfl,
      Polynomial.add_comp, mul_add]
  | mul_X A k hA =>
    rw [map_mul]
    have hrot_X : rotPoly r μ (MvPolynomial.X k) =
        MvPolynomial.C (Polynomial.C (μ ^ (k.val + 1))) * MvPolynomial.X k := by
      simp [rotPoly]
    rw [hrot_X, MvPolynomial.coeff_mul_X']
    have hcoeff_CX : ∀ (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (c : Polynomial ℂ),
        (Q * (MvPolynomial.C c * MvPolynomial.X k)).coeff α =
          if k ∈ α.support then c * Q.coeff (α - Finsupp.single k 1) else 0 := by
      intro Q c
      rw [← mul_assoc, mul_comm Q (MvPolynomial.C c), mul_assoc, MvPolynomial.coeff_C_mul,
        MvPolynomial.coeff_mul_X']
      split_ifs <;> simp
    rw [hcoeff_CX]
    split_ifs with hk
    · let α' : Fin (r + 1) →₀ ℕ := α - Finsupp.single k (1 : ℕ)
      rw [hA α']
      have hk1 : 1 ≤ α k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hk))
      have hprod_eq : ∏ j ∈ α.support, (μ ^ (j.val + 1)) ^ α j =
          μ ^ (k.val + 1) * ∏ j ∈ α'.support, (μ ^ (j.val + 1)) ^ α' j := by
        rw [prod_support_pow_eq_univ, prod_support_pow_eq_univ]
        rw [← Finset.mul_prod_erase Finset.univ (fun j : Fin (r + 1) => (μ ^ (j.val + 1)) ^ α j)
          (Finset.mem_univ k)]
        rw [← Finset.mul_prod_erase Finset.univ (fun j : Fin (r + 1) => (μ ^ (j.val + 1)) ^ α' j)
          (Finset.mem_univ k)]
        have hrest : ∏ j ∈ Finset.univ.erase k, (μ ^ (j.val + 1)) ^ α j =
            ∏ j ∈ Finset.univ.erase k, (μ ^ (j.val + 1)) ^ α' j := by
          refine Finset.prod_congr rfl fun j hj => ?_
          have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
          simp [α', Finsupp.tsub_apply, hjk.symm]
        rw [hrest]
        simp only [α', Finsupp.tsub_apply, Finsupp.single_apply, ↓reduceIte]
        rw [← mul_assoc, ← pow_succ']
        congr 2
        omega
      rw [hprod_eq, Polynomial.C_mul]
      ring
    · simp

private lemma rotPoly_eq_zero_iff {r : ℕ} {μ : ℂ} (hμ : μ ≠ 0)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    rotPoly r μ P = 0 ↔ P = 0 := by
  constructor
  · intro h0
    apply MvPolynomial.ext
    intro α
    have hα := congrArg (fun Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) => Q.coeff α) h0
    change (rotPoly r μ P).coeff α = 0 at hα
    rw [rotPoly_coeff] at hα
    have hprod_ne : Polynomial.C (∏ j ∈ α.support, (μ ^ (j.val + 1)) ^ α j) ≠ 0 :=
      Polynomial.C_ne_zero.mpr
        (Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (pow_ne_zero _ hμ))
    have hcomp : (P.coeff α).comp (Polynomial.C μ⁻¹ * Polynomial.X) = 0 :=
      (mul_eq_zero.mp hα).resolve_left hprod_ne
    have hcomp2 := congrArg (fun q : Polynomial ℂ => q.comp (Polynomial.C μ * Polynomial.X)) hcomp
    rw [Polynomial.comp_assoc, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp,
      ← mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hμ, Polynomial.C_1, one_mul,
      Polynomial.comp_X, Polynomial.zero_comp] at hcomp2
    change P.coeff α = 0
    exact hcomp2
  · rintro rfl; simp

private lemma maxUDeg_rotPoly_le {r : ℕ} (μ : ℂ)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    maxUDeg (rotPoly r μ P) ≤ maxUDeg P := by
  refine Finset.sup_le fun α _ => ?_
  rw [rotPoly_coeff]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine Polynomial.natDegree_comp_le.trans ?_
  have hdeg1 : (Polynomial.C μ⁻¹ * Polynomial.X).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le
  exact (Nat.mul_le_mul_left _ hdeg1).trans (by simp [natDegree_le_maxUDeg P α])

private lemma formalEvalPoly_rot_eq_zero {r : ℕ} {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    {μ : ℂ} (hμ : μ ≠ 0)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries φ) P = 0) :
    formalEvalPoly (formalSeries (fun z => φ (μ * z))) (rotPoly r μ P) = 0 := by
  let N := maxUDeg P
  have hNP : ∀ α, (P.coeff α).natDegree ≤ N := natDegree_le_maxUDeg P
  have hNrot : ∀ α, ((rotPoly r μ P).coeff α).natDegree ≤ N := fun α =>
    (natDegree_le_maxUDeg (rotPoly r μ P) α).trans (maxUDeg_rotPoly_le μ P)
  rw [← formalEvalW_eq_zero_iff_formalEvalPoly _ _ hNP] at hP
  rw [← formalEvalW_eq_zero_iff_formalEvalPoly _ _ hNrot]
  have hid : PowerSeries.C (μ ^ N) *
        formalEvalW (formalSeries (fun z => φ (μ * z))) (revMvPoly N (rotPoly r μ P)) =
      scaleSubst μ (formalEvalW (formalSeries φ) (revMvPoly N P)) := by
    have hext_sum : ∀ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
        formalEvalW (formalSeries (fun z => φ (μ * z))) (revMvPoly N Q) =
          ∑ α ∈ Q.support, ((revPoly N (Q.coeff α) : Polynomial ℂ) : PowerSeries ℂ) *
            ∏ j ∈ α.support, (d_u^[j.val] (formalSeries (fun z => φ (μ * z)))) ^ α j := by
      intro Q
      unfold formalEvalW revMvPoly
      rw [MvPolynomial.eval₂_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [MvPolynomial.eval₂_monomial]
      rfl
    have hext_sum' : formalEvalW (formalSeries φ) (revMvPoly N P) =
        ∑ α ∈ P.support, ((revPoly N (P.coeff α) : Polynomial ℂ) : PowerSeries ℂ) *
          ∏ j ∈ α.support, (d_u^[j.val] (formalSeries φ)) ^ α j := by
      unfold formalEvalW revMvPoly
      rw [MvPolynomial.eval₂_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [MvPolynomial.eval₂_monomial]
      rfl
    have hrot_term : ∀ α : Fin (r + 1) →₀ ℕ,
        PowerSeries.C (μ ^ N) *
          (((revPoly N ((rotPoly r μ P).coeff α) : Polynomial ℂ) : PowerSeries ℂ) *
            ∏ j ∈ α.support, (d_u^[j.val] (formalSeries (fun z => φ (μ * z)))) ^ α j) =
        scaleSubst μ
          (((revPoly N (P.coeff α) : Polynomial ℂ) : PowerSeries ℂ) *
            ∏ j ∈ α.support, (d_u^[j.val] (formalSeries φ)) ^ α j) := by
      intro α
      rw [rotPoly_coeff]
      have hrev_C : ∀ (c : ℂ) (q : Polynomial ℂ),
          revPoly N (Polynomial.C c * q) = Polynomial.C c * revPoly N q := by
        intro c q
        simp only [revPoly, Polynomial.coeff_C_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by rw [Polynomial.C_mul]; ring
      rw [hrev_C, Polynomial.coe_mul, Polynomial.coe_C]
      have hpow_rot : ∏ j ∈ α.support, (d_u^[j.val] (formalSeries (fun z => φ (μ * z)))) ^ α j =
          PowerSeries.C (∏ j ∈ α.support, (μ⁻¹ ^ (j.val + 1)) ^ α j) *
            scaleSubst μ (∏ j ∈ α.support, (d_u^[j.val] (formalSeries φ)) ^ α j) := by
        simp_rw [d_u_iter_formalSeries_rot hφ hμ, mul_pow, ← map_pow, Finset.prod_mul_distrib,
          ← map_prod]
      rw [hpow_rot, map_mul (scaleSubst μ)]
      have hC_cancel : (∏ j ∈ α.support, (μ ^ (j.val + 1)) ^ α j) *
          (∏ j ∈ α.support, (μ⁻¹ ^ (j.val + 1)) ^ α j) = 1 := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_eq_one fun j _ => ?_
        rw [← mul_pow, ← mul_pow, mul_inv_cancel₀ hμ, one_pow, one_pow]
      calc PowerSeries.C (μ ^ N) *
            ((PowerSeries.C (∏ j ∈ α.support, (μ ^ (j.val + 1)) ^ α j) *
                ((revPoly N ((P.coeff α).comp (Polynomial.C μ⁻¹ * Polynomial.X)) : Polynomial ℂ) : PowerSeries ℂ)) *
              (PowerSeries.C (∏ j ∈ α.support, (μ⁻¹ ^ (j.val + 1)) ^ α j) *
                scaleSubst μ (∏ j ∈ α.support, (d_u^[j.val] (formalSeries φ)) ^ α j)))
          = PowerSeries.C ((∏ j ∈ α.support, (μ ^ (j.val + 1)) ^ α j) *
              (∏ j ∈ α.support, (μ⁻¹ ^ (j.val + 1)) ^ α j)) *
              ((PowerSeries.C (μ ^ N) *
                ((revPoly N ((P.coeff α).comp (Polynomial.C μ⁻¹ * Polynomial.X)) : Polynomial ℂ) : PowerSeries ℂ)) *
                scaleSubst μ (∏ j ∈ α.support, (d_u^[j.val] (formalSeries φ)) ^ α j)) := by
            rw [map_mul]; ring
        _ = scaleSubst μ ((revPoly N (P.coeff α) : Polynomial ℂ) : PowerSeries ℂ) *
              scaleSubst μ (∏ j ∈ α.support, (d_u^[j.val] (formalSeries φ)) ^ α j) := by
            rw [hC_cancel, map_one, one_mul, scaleSubst_revPoly μ hμ (P.coeff α)]
    have hsupp_sub : (rotPoly r μ P).support ⊆ P.support := by
      intro α hα
      rw [MvPolynomial.mem_support_iff] at hα ⊢
      intro h0
      apply hα
      rw [rotPoly_coeff, h0, Polynomial.zero_comp, mul_zero]
    rw [hext_sum, hext_sum', map_sum, Finset.mul_sum]
    rw [Finset.sum_subset hsupp_sub]
    · exact Finset.sum_congr rfl fun α _ => hrot_term α
    · intro α _ hnot
      rw [MvPolynomial.notMem_support_iff.mp hnot]
      simp [revPoly]
  rw [hP, map_zero] at hid
  have hC_ne : PowerSeries.C (μ ^ N) ≠ 0 := by
    intro h0
    have h0' := congrArg (PowerSeries.coeff 0) h0
    simp [pow_ne_zero N hμ] at h0'
  exact (mul_eq_zero.mp hid).resolve_left hC_ne

/-! ### 3. Algebraic Core: Higher-Order Differential Operators and Top-`u` Extraction -/

/-- Higher-order constant-coefficient frequency operator
`D_ω^{(a)} P = ∑ j, C (choose j a * (-ω)^(j - a)) • ∂_j P`. -/
@[expose] def D_freq_higher (r a : ℕ) (ω : ℂ) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) →ₗ[Polynomial ℂ]
      MvPolynomial (Fin (r + 1)) (Polynomial ℂ) where
  toFun P := ∑ j : Fin (r + 1),
    (Polynomial.C ((Nat.choose j.val a : ℂ) * (-ω) ^ (j.val - a))) • MvPolynomial.pderiv j P
  map_add' P Q := by simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(MvPolynomial.pderiv j).map_smul, smul_comm]

/-- Polynomial jet coefficients `Q_j(u) = ∑_{a ≤ j} choose j a (-ω)^{j - a} Q^{(a)}(u)`. -/
@[expose] def Q_jet (Q : Polynomial ℂ) (ω : ℂ) (j : ℕ) : Polynomial ℂ :=
  ∑ a ∈ Finset.range (j + 1),
    Polynomial.C ((Nat.choose j a : ℂ) * (-ω) ^ (j - a)) * (Polynomial.derivative^[a] Q)

/-- Higher-order polynomial-in-`u` Stokes operator `L_{Q, ω} P = ∑ j, Q_jet Q ω j • ∂_j P`. -/
@[expose] def L_op (r : ℕ) (Q : Polynomial ℂ) (ω : ℂ) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) →ₗ[Polynomial ℂ]
      MvPolynomial (Fin (r + 1)) (Polynomial ℂ) where
  toFun P := ∑ j : Fin (r + 1), Q_jet Q ω j.val • MvPolynomial.pderiv j P
  map_add' P Q' := by simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(MvPolynomial.pderiv j).map_smul, smul_comm]

private lemma L_op_eq_sum_D_freq_higher (r : ℕ) (Q : Polynomial ℂ) (ω : ℂ)
    (m : ℕ) (hm : Q.natDegree < m) (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    L_op r Q ω P =
      ∑ a ∈ Finset.range m, (Polynomial.derivative^[a] Q) • D_freq_higher r a ω P := by
  have hvan : ∀ a, m ≤ a → Polynomial.derivative^[a] Q = 0 := fun a ha =>
    Polynomial.iterate_derivative_eq_zero (lt_of_lt_of_le hm ha)
  unfold L_op D_freq_higher Q_jet
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.sum_smul, Finset.smul_sum, smul_smul, mul_comm (Polynomial.derivative^[ _ ] Q)]
  let T (j : Fin (r + 1)) (a : ℕ) : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    (Polynomial.C ((Nat.choose j.val a : ℂ) * (-ω) ^ (j.val - a)) *
      Polynomial.derivative^[a] Q) • MvPolynomial.pderiv j P
  have hT_gt_j : ∀ j a, j.val < a → T j a = 0 := by
    intro j a hja
    simp [T, Nat.choose_eq_zero_of_lt hja]
  have hT_ge_m : ∀ j a, m ≤ a → T j a = 0 := by
    intro j a ham
    simp [T, hvan a ham]
  have hL : ∑ j : Fin (r + 1), ∑ a ∈ Finset.range (j.val + 1), T j a =
      ∑ j : Fin (r + 1), ∑ a ∈ Finset.range (max (r + 1) m), T j a := by
    refine Finset.sum_congr rfl fun j _ => ?_
    refine (Finset.sum_subset (Finset.range_mono (by omega)) fun a _ hnot => ?_)
    rw [Finset.mem_range, not_lt] at hnot
    exact hT_gt_j j a hnot
  have hR : ∑ a ∈ Finset.range m, ∑ j : Fin (r + 1), T j a =
      ∑ j : Fin (r + 1), ∑ a ∈ Finset.range (max (r + 1) m), T j a := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_subset (Finset.range_mono (le_max_right _ _)) fun a _ hnot => ?_
    rw [Finset.mem_range, not_lt] at hnot
    exact hT_ge_m j a hnot
  exact hL.trans hR.symm

private lemma degree_pderiv_poly_lt {ι : Type*} (i : ι) (P : MvPolynomial ι (Polynomial ℂ))
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

private lemma totalDegree_poly_sum_lt {ι σ : Type*} [DecidableEq ι] (s : Finset ι)
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

private lemma degree_L_op_lt {r : ℕ} (Q : Polynomial ℂ) (ω : ℂ)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (h : 0 < P.totalDegree) :
    (L_op r Q ω P).totalDegree < P.totalDegree := by
  unfold L_op
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine totalDegree_poly_sum_lt Finset.univ _ h fun j _ => ?_
  exact (MvPolynomial.totalDegree_smul_le _ _).trans_lt (degree_pderiv_poly_lt j P h)

private lemma all_partials_poly_zero {ι : Type*} (P : MvPolynomial ι (Polynomial ℂ))
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
    have hmul : (((m - Finsupp.single i (1 : ℕ)) i : Polynomial ℂ) + 1) ≠ 0 := by
      have : ((m - Finsupp.single i (1 : ℕ)) i + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero _
      exact_mod_cast this
    have hcm : P.coeff m = 0 := (mul_eq_zero.mp hp).resolve_right hmul
    simp [hcm, MvPolynomial.coeff_C, Ne.symm hm]

/-- General directional shift-invariance for arbitrary vector `v : Fin (r + 1) → ℂ`. -/
private def lineSliceGen {r : ℕ} (x v : Fin (r + 1) → ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval fun j => Polynomial.C (x j) + Polynomial.C (v j) * Polynomial.X

private lemma lineSliceGen_eval {r : ℕ} (x v : Fin (r + 1) → ℂ)
    (P : MvPolynomial (Fin (r + 1)) ℂ) (a : ℂ) :
    (lineSliceGen x v P).eval a = MvPolynomial.eval (fun j => x j + a * v j) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [lineSliceGen]
  | add A B hA hB =>
    simp only [map_add, Polynomial.eval_add] at hA hB ⊢
    rw [hA, hB]
  | mul_X A j hA =>
    simp only [lineSliceGen, map_mul, MvPolynomial.aeval_X] at hA ⊢
    simp [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
      hA, mul_comm a (v j)]

private lemma derivative_lineSliceGen {r : ℕ} (x v : Fin (r + 1) → ℂ)
    (P : MvPolynomial (Fin (r + 1)) ℂ) :
    Polynomial.derivative (lineSliceGen x v P) =
      ∑ j : Fin (r + 1), Polynomial.C (v j) * lineSliceGen x v (MvPolynomial.pderiv j P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [lineSliceGen]
  | add A B hA hB =>
    simp only [map_add, hA, hB, mul_add, Finset.sum_add_distrib]
  | mul_X A k hA =>
    simp only [map_mul, Polynomial.derivative_mul, hA]
    have hk : Polynomial.derivative (lineSliceGen x v (MvPolynomial.X k)) = Polynomial.C (v k) := by
      simp [lineSliceGen]
    rw [hk]
    simp only [MvPolynomial.pderiv_mul, map_add, MvPolynomial.pderiv_X, Pi.single_apply,
      mul_add, Finset.sum_add_distrib]
    have hsum1 : ∑ j : Fin (r + 1), Polynomial.C (v j) *
        lineSliceGen x v (MvPolynomial.pderiv j A * MvPolynomial.X k) =
        (∑ j : Fin (r + 1), Polynomial.C (v j) * lineSliceGen x v (MvPolynomial.pderiv j A)) *
          lineSliceGen x v (MvPolynomial.X k) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]; ring
    have hsum2 : ∑ j : Fin (r + 1), Polynomial.C (v j) *
        lineSliceGen x v (A * if k = j then 1 else 0) =
        lineSliceGen x v A * Polynomial.C (v k) := by
      trans ∑ j : Fin (r + 1), if k = j then Polynomial.C (v k) * lineSliceGen x v A else 0
      · refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs with hkj
        · subst hkj; simp
        · simp
      · simp [mul_comm]
    rw [hsum1, hsum2]

lemma shift_invariant_of_pderiv_sum_eq_zero {r : ℕ} (v : Fin (r + 1) → ℂ)
    (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∑ j : Fin (r + 1), v j • MvPolynomial.pderiv j P = 0)
    (x : Fin (r + 1) → ℂ) (a : ℂ) :
    MvPolynomial.eval (fun j => x j + a * v j) P = MvPolynomial.eval x P := by
  have hd : Polynomial.derivative (lineSliceGen x v P) = 0 := by
    rw [derivative_lineSliceGen]
    have h0 : lineSliceGen x v (∑ j : Fin (r + 1), v j • MvPolynomial.pderiv j P) = 0 := by
      rw [hP, map_zero]
    simp only [map_sum, Algebra.smul_def, MvPolynomial.algebraMap_eq] at h0
    simpa [lineSliceGen] using h0
  have hc := Polynomial.eq_C_of_derivative_eq_zero hd
  have he : (lineSliceGen x v P).eval a = (lineSliceGen x v P).eval 0 := by
    rw [hc, Polynomial.eval_C, Polynomial.eval_C]
  rw [lineSliceGen_eval, lineSliceGen_eval] at he
  simpa using he

private lemma evalU_pderiv {r : ℕ} (j : Fin (r + 1))
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (u : ℂ) :
    evalU (MvPolynomial.pderiv j P) u = MvPolynomial.pderiv j (evalU P u) := by
  unfold evalU
  exact (MvPolynomial.pderiv_map).symm

private lemma evalU_L_op {r : ℕ} (Q : Polynomial ℂ) (ω : ℂ)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (u : ℂ) :
    evalU (L_op r Q ω P) u =
      ∑ j : Fin (r + 1), (Q_jet Q ω j.val).eval u • MvPolynomial.pderiv j (evalU P u) := by
  unfold L_op evalU
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp only [map_sum, Algebra.smul_def, map_mul, MvPolynomial.map_C, Polynomial.coe_evalRingHom,
    MvPolynomial.pderiv_map, MvPolynomial.algebraMap_eq]

/-- Extract the coefficient polynomial in `MvPolynomial (Fin (r + 1)) ℂ` of `u^k` from
`P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)`. -/
private def coeffU {r : ℕ} (k : ℕ) (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  ∑ α ∈ P.support, MvPolynomial.monomial α ((P.coeff α).coeff k)

private lemma coeffU_coeff {r : ℕ} (k : ℕ) (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (α : Fin (r + 1) →₀ ℕ) :
    (coeffU k P).coeff α = (P.coeff α).coeff k := by
  classical
  unfold coeffU
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · rw [MvPolynomial.notMem_support_iff.mp hα, Finset.sum_eq_zero]
    · simp
    · intro β hβ
      have hne : β ≠ α := fun h => hα (h ▸ hβ)
      simp [hne]

private lemma coeffU_zero {r : ℕ} (k : ℕ) : coeffU (r := r) k 0 = 0 := by
  ext α; simp [coeffU_coeff]

private lemma coeffU_add {r : ℕ} (k : ℕ) (A B : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    coeffU k (A + B) = coeffU k A + coeffU k B := by
  ext α; simp [coeffU_coeff]

private lemma coeffU_sum {r : ℕ} {ι : Type*} (k : ℕ) (s : Finset ι)
    (f : ι → MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    coeffU k (∑ i ∈ s, f i) = ∑ i ∈ s, coeffU k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffU_zero]
  | @insert i s hi ih => rw [Finset.sum_insert hi, coeffU_add, ih, Finset.sum_insert hi]

private lemma coeffU_pderiv {r : ℕ} (k : ℕ) (j : Fin (r + 1))
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    coeffU k (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (coeffU k P) := by
  ext α
  simp only [coeffU_coeff, MvPolynomial.coeff_pderiv]
  have hcast : ((α j : Polynomial ℂ) + 1) = Polynomial.C ((α j : ℂ) + 1) := by simp
  rw [hcast, mul_comm, Polynomial.coeff_C_mul]
  ring

private lemma coeffU_C_smul {r : ℕ} (k : ℕ) (c : ℂ)
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    coeffU k (Polynomial.C c • P) = c • coeffU k P := by
  ext α
  simp [coeffU_coeff]

private lemma coeffU_mul_smul_top {r : ℕ} (p : Polynomial ℂ)
    (R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) {d_p d_R : ℕ}
    (hp : p.natDegree ≤ d_p) (hR : maxUDeg R ≤ d_R) :
    coeffU (d_R + d_p) (p • R) = p.coeff d_p • coeffU d_R R := by
  ext α
  simp only [coeffU_coeff, MvPolynomial.coeff_smul, smul_eq_mul]
  rw [Polynomial.coeff_mul]
  have hRα : (R.coeff α).natDegree ≤ d_R := (natDegree_le_maxUDeg R α).trans hR
  have hterm : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal (d_R + d_p),
      p.coeff x.1 * (R.coeff α).coeff x.2 =
        if x = (d_p, d_R) then p.coeff d_p * (R.coeff α).coeff d_R else 0 := by
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    split_ifs with hxd
    · rw [hxd]
    · by_cases h1 : d_p < x.1
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp h1), zero_mul]
      · have h2 : d_R < x.2 := by
          rcases x with ⟨x1, x2⟩
          dsimp only at hx h1 ⊢
          by_contra h2le
          exact hxd (Prod.ext (by omega) (by omega))
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hRα h2), mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp [Finset.HasAntidiagonal.mem_antidiagonal, add_comm]

private lemma maxUDeg_D_freq_higher_le (r a : ℕ) (ω : ℂ)
    (R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    maxUDeg (D_freq_higher r a ω R) ≤ maxUDeg R := by
  refine Finset.sup_le fun α _ => ?_
  unfold D_freq_higher
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [MvPolynomial.coeff_sum]
  refine (Polynomial.natDegree_sum_le _ _).trans (Finset.sup_le fun j _ => ?_)
  dsimp only [Function.comp_def]
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [MvPolynomial.coeff_pderiv]
  have hcast : ((α j : Polynomial ℂ) + 1) = Polynomial.C ((α j : ℂ) + 1) := by simp
  rw [hcast, mul_comm]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  exact natDegree_le_maxUDeg R (α + Finsupp.single j 1)

private lemma coeffU_D_freq_higher_zero (r : ℕ) (ω : ℂ) (k : ℕ)
    (R : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    coeffU k (D_freq_higher r 0 ω R) = D_freq r ω (coeffU k R) := by
  unfold D_freq_higher D_freq
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [coeffU_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero]
  rw [coeffU_C_smul, coeffU_pderiv]

private lemma D_freq_top_of_L_op_eq_zero {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP_deg : 0 < P.totalDegree)
    (ω : ℕ → ℝ) (hω_mono : StrictMono ω)
    (Q : ℕ → Polynomial ℂ) (m : ℕ → ℕ)
    (hm_pos : ∀ k, 1 ≤ m k)
    (hQ_deg : ∀ k, k < r + 1 → (Q k).natDegree = m k - 1)
    (hQ_lead : ∀ k, k < r + 1 → (Q k).leadingCoeff ≠ 0)
    (hL_zero : ∀ k, k < r + 1 → L_op r (Q k) (ω k : ℂ) P = 0) :
    False := by
  let P_Y := P - MvPolynomial.C (P.coeff 0)
  have hPY_ne : P_Y ≠ 0 := by
    intro h0
    have hPC : P = MvPolynomial.C (P.coeff 0) := sub_eq_zero.mp h0
    have hdeg0 : P.totalDegree = 0 := by rw [hPC]; simp
    omega
  have hPY_const : P_Y.coeff 0 = 0 := by simp [P_Y]
  have hL_PY : ∀ k, k < r + 1 → L_op r (Q k) (ω k : ℂ) P_Y = 0 := by
    intro k hk
    have hpderiv : ∀ j, MvPolynomial.pderiv j P_Y = MvPolynomial.pderiv j P := by
      intro j; simp [P_Y, map_sub]
    have heq : L_op r (Q k) (ω k : ℂ) P_Y = L_op r (Q k) (ω k : ℂ) P := by
      unfold L_op
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      refine Finset.sum_congr rfl fun j _ => by rw [hpderiv j]
    rw [heq, hL_zero k hk]
  let d_top := maxUDeg P_Y
  let P_top : MvPolynomial (Fin (r + 1)) ℂ := coeffU d_top P_Y
  have hPtop_ne : P_top ≠ 0 := by
    have hsupp : P_Y.support.Nonempty := MvPolynomial.support_nonempty.mpr hPY_ne
    obtain ⟨α₀, hα₀_mem, hα₀_max⟩ := Finset.exists_mem_eq_sup P_Y.support hsupp
      (fun α => (P_Y.coeff α).natDegree)
    have hd_eq : (P_Y.coeff α₀).natDegree = d_top := hα₀_max.symm
    have hcoeff_ne : P_Y.coeff α₀ ≠ 0 := MvPolynomial.mem_support_iff.mp hα₀_mem
    have hlead_ne : (P_Y.coeff α₀).coeff d_top ≠ 0 := by
      rw [← hd_eq]
      exact Polynomial.leadingCoeff_ne_zero.mpr hcoeff_ne
    intro h0
    have := congrArg (fun R : MvPolynomial (Fin (r + 1)) ℂ => R.coeff α₀) h0
    simp only [P_top, coeffU_coeff, AddMonoidAlgebra.coeff_zero] at this
    exact hlead_ne this
  have hPtop_const : P_top.coeff 0 = 0 := by
    simp [P_top, coeffU_coeff, hPY_const]
  have hD_top : ∀ k, k < r + 1 → D_freq r (ω k : ℂ) P_top = 0 := by
    intro k hk
    have hmk : 1 ≤ m k := hm_pos k
    have hQk_deg : (Q k).natDegree < m k := by rw [hQ_deg k hk]; omega
    have hL_exp := L_op_eq_sum_D_freq_higher r (Q k) (ω k : ℂ) (m k) hQk_deg P_Y
    rw [hL_PY k hk] at hL_exp
    have hc_zero := congrArg (coeffU (d_top + (m k - 1))) hL_exp.symm
    rw [coeffU_zero, coeffU_sum] at hc_zero
    have hsum_terms : ∑ a ∈ Finset.range (m k),
        coeffU (d_top + (m k - 1)) ((Polynomial.derivative^[a] (Q k)) • D_freq_higher r a (ω k : ℂ) P_Y) =
        ((Q k).coeff (m k - 1)) • D_freq r (ω k : ℂ) P_top := by
      have h0_mem : 0 ∈ Finset.range (m k) := Finset.mem_range.mpr hmk
      rw [← Finset.add_sum_erase (Finset.range (m k)) _ h0_mem]
      have hterm0 : coeffU (d_top + (m k - 1))
          ((Polynomial.derivative^[0] (Q k)) • D_freq_higher r 0 (ω k : ℂ) P_Y) =
          ((Q k).coeff (m k - 1)) • D_freq r (ω k : ℂ) P_top := by
        rw [Function.iterate_zero_apply, coeffU_mul_smul_top (Q k) _ (le_of_eq (hQ_deg k hk))
          (maxUDeg_D_freq_higher_le r 0 _ P_Y), coeffU_D_freq_higher_zero]
      have hrest : ∑ a ∈ (Finset.range (m k)).erase 0,
          coeffU (d_top + (m k - 1)) ((Polynomial.derivative^[a] (Q k)) • D_freq_higher r a (ω k : ℂ) P_Y) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        have ha_pos : 1 ≤ a := Nat.pos_of_ne_zero (Finset.mem_erase.mp ha).1
        have hderiv_deg : (Polynomial.derivative^[a] (Q k)).natDegree ≤ m k - 1 := by
          refine (Polynomial.natDegree_iterate_derivative (Q k) a).trans ?_
          rw [hQ_deg k hk]
          omega
        have hderiv_lt : (Polynomial.derivative^[a] (Q k)).natDegree < m k - 1 ∨ m k - 1 = 0 := by
          by_cases hm1 : m k - 1 = 0
          · exact Or.inr hm1
          · left
            refine lt_of_le_of_lt (Polynomial.natDegree_iterate_derivative (Q k) a) ?_
            rw [hQ_deg k hk]
            omega
        have hcoeff_lt : (Polynomial.derivative^[a] (Q k)).coeff (m k - 1) = 0 := by
          rcases hderiv_lt with hlt | hm1
          · exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
          · have hq0 : (Q k).natDegree < a := by rw [hQ_deg k hk, hm1]; omega
            rw [Polynomial.iterate_derivative_eq_zero hq0, Polynomial.coeff_zero]
        rw [coeffU_mul_smul_top _ _ hderiv_deg (maxUDeg_D_freq_higher_le r a _ P_Y),
          hcoeff_lt, zero_smul]
      rw [hterm0, hrest, add_zero]
    rw [hsum_terms] at hc_zero
    have hlead_ne' : (Q k).coeff (m k - 1) ≠ 0 := by
      have := hQ_lead k hk
      rwa [Polynomial.leadingCoeff, hQ_deg k hk] at this
    exact (smul_eq_zero.mp hc_zero).resolve_left hlead_ne'
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
  have hVC_mul : VC *ᵥ (fun j : Fin (r + 1) => MvPolynomial.pderiv j P_top) = 0 := by
    funext i
    simp only [VC, Matrix.mulVec, dotProduct, Matrix.map_apply, V, Matrix.vandermonde_apply,
      Pi.zero_apply]
    have hDi := hD_top i.val i.isLt
    rw [D_freq] at hDi
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at hDi
    simpa only [nodes, Algebra.smul_def, MvPolynomial.algebraMap_eq] using hDi
  have hpderiv_zero : ∀ j : Fin (r + 1), MvPolynomial.pderiv j P_top = 0 :=
    congrFun (Matrix.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hVC_det hVC_mul)
  have hPC := all_partials_zero P_top hpderiv_zero
  have hPC' : P_top.coeff 0 = 0 := hPtop_const
  exact hPtop_ne (hPC.trans (by rw [hPC', map_zero]))

/-! ### 4. Non-Autonomous Borel Algebra (`PolyBorelExpr`) for Unrotated Rays (`θ₀ = 0`) -/

private def ε₀H {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : ℝ :=
  min h.ε (ω 0 / 2)

private lemma ε₀H_pos {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : 0 < ε₀H h :=
  lt_min h.hε_pos (half_pos h.ω_pos)

private lemma ε₀H_le_ε {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : ε₀H h ≤ h.ε :=
  min_le_left _ _

private lemma ε₀H_lt_ω {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) (m : ℕ) :
    ε₀H h < ω m := by
  have h1 : ε₀H h ≤ ω 0 / 2 := min_le_right _ _
  have h2 : ω 0 / 2 < ω 0 := half_lt_self h.ω_pos
  have h3 : ω 0 ≤ ω m := h.ω_mono.monotone (Nat.zero_le m)
  linarith

private lemma tan_pos_of_memH {α : ℝ} (h1 : 0 < α) (h2 : α < Real.pi / 2) : 0 < Real.tan α :=
  Real.tan_pos_of_pos_of_lt_pi_div_two h1 h2

private lemma tan_lt_tanH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    Real.tan h.θ < Real.tan h.α₀ :=
  Real.strictMonoOn_tan
    ⟨by linarith [h.hθ_pos, Real.pi_pos], h.hθ_lt.trans h.hα₀_lt⟩
    ⟨by linarith [h.hθ_pos, h.hθ_lt, Real.pi_pos], h.hα₀_lt⟩
    h.hθ_lt

private lemma cos_pos_θH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    0 < Real.cos h.θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.hθ_pos, Real.pi_pos], h.hθ_lt.trans h.hα₀_lt⟩

private lemma sin_pos_θH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    0 < Real.sin h.θ :=
  Real.sin_pos_of_pos_of_lt_pi h.hθ_pos (h.hθ_lt.trans (h.hα₀_lt.trans (by linarith [Real.pi_pos])))

private def dPlusH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : ℂ :=
  Complex.exp (I * (h.θ : ℂ))

private def dMinusH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : ℂ :=
  Complex.exp (-I * (h.θ : ℂ))

private lemma dPlusH_eq {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    dPlusH h = (Real.cos h.θ : ℂ) + (Real.sin h.θ : ℂ) * I := by
  unfold dPlusH
  rw [mul_comm I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

private lemma dMinusH_eq {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    dMinusH h = (Real.cos h.θ : ℂ) - (Real.sin h.θ : ℂ) * I := by
  unfold dMinusH
  rw [show -I * (h.θ : ℂ) = ((-h.θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
  push_cast; ring

private lemma dPlusH_re {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (dPlusH h).re = Real.cos h.θ := by
  rw [dPlusH_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

private lemma dPlusH_im {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (dPlusH h).im = Real.sin h.θ := by
  rw [dPlusH_eq]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]

private lemma dMinusH_re {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (dMinusH h).re = Real.cos h.θ := by
  rw [dMinusH_eq]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

private lemma dMinusH_im {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (dMinusH h).im = -Real.sin h.θ := by
  rw [dMinusH_eq]
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_sub]

private lemma norm_dPlusH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : ‖dPlusH h‖ = 1 := by
  unfold dPlusH
  rw [mul_comm I]
  exact Complex.norm_exp_ofReal_mul_I h.θ

private lemma norm_dMinusH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : ‖dMinusH h‖ = 1 := by
  unfold dMinusH
  rw [show -I * (h.θ : ℂ) = ((-h.θ : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I (-h.θ)

private def wedgePlusH (α₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.im < Real.tan α₀ * z.re}

private def wedgeMinusH (α₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ z.im < 0 ∧ -Real.tan α₀ * z.re < z.im}

private lemma isOpen_wedgePlusH (α₀ ε : ℝ) : IsOpen (wedgePlusH α₀ ε) :=
  Metric.isOpen_ball.union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im (continuous_const.mul Complex.continuous_re))))

private lemma isOpen_wedgeMinusH (α₀ ε : ℝ) : IsOpen (wedgeMinusH α₀ ε) :=
  Metric.isOpen_ball.union
    ((isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_im continuous_const).inter
        (isOpen_lt (continuous_const.mul Complex.continuous_re) Complex.continuous_im)))

private lemma star_wedgePlusH (α₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ z ∈ wedgePlusH α₀ ε, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ wedgePlusH α₀ ε := by
  intro z hz t ht
  rcases hz with hz_ball | ⟨hre, him, htan⟩
  · left
    rw [Metric.mem_ball, dist_zero_right] at hz_ball ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz_ball
  · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · left; simpa [Metric.mem_ball, dist_zero_right] using hε
    · right
      refine ⟨?_, ?_, ?_⟩
      · simpa [Complex.mul_re] using mul_pos ht_pos hre
      · simpa [Complex.mul_im] using mul_pos ht_pos him
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.mul_im, add_zero]
        nlinarith [ht_pos, htan]

private lemma star_wedgeMinusH (α₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ z ∈ wedgeMinusH α₀ ε, ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * z ∈ wedgeMinusH α₀ ε := by
  intro z hz t ht
  rcases hz with hz_ball | ⟨hre, him, htan⟩
  · left
    rw [Metric.mem_ball, dist_zero_right] at hz_ball ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hz_ball
  · rcases eq_or_lt_of_le ht.1 with rfl | ht_pos
    · left; simpa [Metric.mem_ball, dist_zero_right] using hε
    · right
      refine ⟨?_, ?_, ?_⟩
      · simpa [Complex.mul_re] using mul_pos ht_pos hre
      · simpa [Complex.mul_im] using mul_neg_of_pos_of_neg ht_pos him
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
          Complex.mul_im, add_zero]
        nlinarith [ht_pos, htan]

private lemma wedgePlusH_domain (α₀ : ℝ) {ε : ℝ} (hε : 0 < ε) : Domain (wedgePlusH α₀ ε) :=
  ⟨isOpen_wedgePlusH α₀ ε, star_wedgePlusH α₀ hε⟩

private lemma wedgeMinusH_domain (α₀ : ℝ) {ε : ℝ} (hε : 0 < ε) : Domain (wedgeMinusH α₀ ε) :=
  ⟨isOpen_wedgeMinusH α₀ ε, star_wedgeMinusH α₀ hε⟩

private lemma isPreconnected_wedgePlusH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    IsPreconnected (wedgePlusH h.α₀ (ε₀H h)) := by
  let S₁ : Set ℂ := Metric.ball (0 : ℂ) (ε₀H h)
  let S₂ : Set ℂ := {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.im < Real.tan h.α₀ * z.re}
  have h1 : IsPreconnected S₁ := (convex_ball (0 : ℂ) (ε₀H h)).isPreconnected
  have h2 : IsPreconnected S₂ := by
    refine Convex.isPreconnected ?_
    intro x hx y hy a b ha hb hab
    simp only [S₂, Set.mem_ofPred_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
      add_zero] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    · refine ⟨add_pos_of_pos_of_nonneg (mul_pos ha_pos hx.1) (mul_nonneg hb hy.1.le),
        add_pos_of_pos_of_nonneg (mul_pos ha_pos hx.2.1) (mul_nonneg hb hy.2.1.le), ?_⟩
      have h1' : a * x.im < a * (Real.tan h.α₀ * x.re) := mul_lt_mul_of_pos_left hx.2.2 ha_pos
      have h2' : b * y.im ≤ b * (Real.tan h.α₀ * y.re) := mul_le_mul_of_nonneg_left hy.2.2.le hb
      linarith
  refine h1.union' ?_ h2
  refine ⟨((ε₀H h / 2 : ℝ) : ℂ) * dPlusH h, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos (ε₀H_pos h)), norm_dPlusH h, mul_one]
    linarith [ε₀H_pos h]
  · have hre : 0 < (((ε₀H h / 2 : ℝ) : ℂ) * dPlusH h).re := by
      simp [Complex.mul_re, dPlusH_re h]
      exact mul_pos (half_pos (ε₀H_pos h)) (cos_pos_θH h)
    have him : 0 < (((ε₀H h / 2 : ℝ) : ℂ) * dPlusH h).im := by
      simp [Complex.mul_im, dPlusH_im h]
      exact mul_pos (half_pos (ε₀H_pos h)) (sin_pos_θH h)
    have htan : (((ε₀H h / 2 : ℝ) : ℂ) * dPlusH h).im <
        Real.tan h.α₀ * (((ε₀H h / 2 : ℝ) : ℂ) * dPlusH h).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero, dPlusH_re h, dPlusH_im h]
      have hsin_eq : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
        rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θH h).ne']
      rw [hsin_eq]
      have hc0 : 0 < (ε₀H h / 2) * Real.cos h.θ := mul_pos (half_pos (ε₀H_pos h)) (cos_pos_θH h)
      calc (ε₀H h / 2) * (Real.tan h.θ * Real.cos h.θ)
          = Real.tan h.θ * ((ε₀H h / 2) * Real.cos h.θ) := by ring
        _ < Real.tan h.α₀ * ((ε₀H h / 2) * Real.cos h.θ) :=
            mul_lt_mul_of_pos_right (tan_lt_tanH h) hc0
    exact ⟨hre, him, htan⟩

private lemma isPreconnected_wedgeMinusH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    IsPreconnected (wedgeMinusH h.α₀ (ε₀H h)) := by
  let S₁ : Set ℂ := Metric.ball (0 : ℂ) (ε₀H h)
  let S₂ : Set ℂ := {z : ℂ | 0 < z.re ∧ z.im < 0 ∧ -Real.tan h.α₀ * z.re < z.im}
  have h1 : IsPreconnected S₁ := (convex_ball (0 : ℂ) (ε₀H h)).isPreconnected
  have h2 : IsPreconnected S₂ := by
    refine Convex.isPreconnected ?_
    intro x hx y hy a b ha hb hab
    simp only [S₂, Set.mem_ofPred_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.mul_im,
      add_zero] at hx hy ⊢
    rcases eq_or_lt_of_le ha with rfl | ha_pos
    · have hb1 : b = 1 := by linarith
      subst hb1; simpa using hy
    · refine ⟨add_pos_of_pos_of_nonneg (mul_pos ha_pos hx.1) (mul_nonneg hb hy.1.le), ?_, ?_⟩
      · exact add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg ha_pos hx.2.1)
          (mul_nonpos_of_nonneg_of_nonpos hb hy.2.1.le)
      · have h1' : a * (-Real.tan h.α₀ * x.re) < a * x.im := mul_lt_mul_of_pos_left hx.2.2 ha_pos
        have h2' : b * (-Real.tan h.α₀ * y.re) ≤ b * y.im := mul_le_mul_of_nonneg_left hy.2.2.le hb
        linarith
  refine h1.union' ?_ h2
  refine ⟨((ε₀H h / 2 : ℝ) : ℂ) * dMinusH h, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (half_pos (ε₀H_pos h)), norm_dMinusH h, mul_one]
    linarith [ε₀H_pos h]
  · have hre : 0 < (((ε₀H h / 2 : ℝ) : ℂ) * dMinusH h).re := by
      simp [Complex.mul_re, dMinusH_re h]
      exact mul_pos (half_pos (ε₀H_pos h)) (cos_pos_θH h)
    have him : (((ε₀H h / 2 : ℝ) : ℂ) * dMinusH h).im < 0 := by
      simp [Complex.mul_im, dMinusH_im h]
      exact mul_pos (half_pos (ε₀H_pos h)) (sin_pos_θH h)
    have htan : -Real.tan h.α₀ * (((ε₀H h / 2 : ℝ) : ℂ) * dMinusH h).re <
        (((ε₀H h / 2 : ℝ) : ℂ) * dMinusH h).im := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Complex.mul_im, add_zero, dMinusH_re h, dMinusH_im h]
      have hsin_eq : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
        rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θH h).ne']
      rw [hsin_eq]
      have hc0 : 0 < (ε₀H h / 2) * Real.cos h.θ := mul_pos (half_pos (ε₀H_pos h)) (cos_pos_θH h)
      calc -Real.tan h.α₀ * ((ε₀H h / 2) * Real.cos h.θ)
          < -Real.tan h.θ * ((ε₀H h / 2) * Real.cos h.θ) :=
            mul_lt_mul_of_pos_right (neg_lt_neg (tan_lt_tanH h)) hc0
        _ = (ε₀H h / 2) * -(Real.tan h.θ * Real.cos h.θ) := by ring
    exact ⟨hre, him, htan⟩

private lemma wedgePlusH_containsRay {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    ContainsRay (wedgePlusH h.α₀ (ε₀H h)) (dPlusH h) := by
  intro v hv
  rcases eq_or_lt_of_le hv with rfl | hv_pos
  · left; simpa [Metric.mem_ball, dist_zero_right] using ε₀H_pos h
  · right
    simp only [Set.mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.mul_im, dPlusH_re h, dPlusH_im h]
    rw [zero_add]
    refine ⟨mul_pos (cos_pos_θH h) hv_pos, mul_pos (sin_pos_θH h) hv_pos, ?_⟩
    have hsin_eq : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
      rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θH h).ne']
    rw [hsin_eq]
    have hvc : 0 < Real.cos h.θ * v := mul_pos (cos_pos_θH h) hv_pos
    calc Real.tan h.θ * Real.cos h.θ * v
        = Real.tan h.θ * (Real.cos h.θ * v) := by ring
      _ < Real.tan h.α₀ * (Real.cos h.θ * v) := mul_lt_mul_of_pos_right (tan_lt_tanH h) hvc

private lemma wedgeMinusH_containsRay {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    ContainsRay (wedgeMinusH h.α₀ (ε₀H h)) (dMinusH h) := by
  intro v hv
  rcases eq_or_lt_of_le hv with rfl | hv_pos
  · left; simpa [Metric.mem_ball, dist_zero_right] using ε₀H_pos h
  · right
    simp only [Set.mem_ofPred_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.mul_im, dMinusH_re h, dMinusH_im h]
    rw [zero_add]
    refine ⟨mul_pos (cos_pos_θH h) hv_pos, ?_, ?_⟩
    · nlinarith [hv_pos, sin_pos_θH h]
    · have hsin_eq : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
        rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θH h).ne']
      rw [hsin_eq]
      have hvc : 0 < Real.cos h.θ * v := mul_pos (cos_pos_θH h) hv_pos
      calc -Real.tan h.α₀ * (Real.cos h.θ * v)
          < -Real.tan h.θ * (Real.cos h.θ * v) :=
            mul_lt_mul_of_pos_right (neg_lt_neg (tan_lt_tanH h)) hvc
        _ = -(Real.tan h.θ * Real.cos h.θ) * v := by ring

private lemma rotatedPuncturedWedge_zero_eq (α₀ ε : ℝ) (ω : ℕ → ℝ) :
    rotatedPuncturedWedge 0 α₀ ε ω = puncturedWedge α₀ ε ω := by
  ext z
  simp [rotatedPuncturedWedge]

private lemma wedgePlusH_subset_punctured {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    wedgePlusH h.α₀ (ε₀H h) ⊆ rotatedPuncturedWedge 0 h.α₀ h.ε ω := by
  rw [rotatedPuncturedWedge_zero_eq]
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hz_ball | ⟨hre, him, htan⟩
    · left
      rw [Metric.mem_ball] at hz_ball ⊢
      exact hz_ball.trans_le (ε₀H_le_ε h)
    · right
      exact ⟨hre, by rw [abs_of_pos him]; exact htan⟩
  · rintro ⟨m, rfl⟩
    rcases hz with hz_ball | ⟨_, him, _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m)))] at hz_ball
      linarith [ε₀H_lt_ω h m]
    · simp at him

private lemma wedgeMinusH_subset_punctured {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    wedgeMinusH h.α₀ (ε₀H h) ⊆ rotatedPuncturedWedge 0 h.α₀ h.ε ω := by
  rw [rotatedPuncturedWedge_zero_eq]
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hz_ball | ⟨hre, him, htan⟩
    · left
      rw [Metric.mem_ball] at hz_ball ⊢
      exact hz_ball.trans_le (ε₀H_le_ε h)
    · right
      exact ⟨hre, by rw [abs_of_neg him]; linarith⟩
  · rintro ⟨m, rfl⟩
    rcases hz with hz_ball | ⟨_, him, _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m)))] at hz_ball
      linarith [ε₀H_lt_ω h m]
    · simp at him

private def aPhiH (φ : ℂ → ℂ) : Minor := ⟨0, φ⟩

private lemma aPhiH_toSeries (φ : ℂ → ℂ) : (aPhiH φ).toSeries = formalSeries φ := by
  ext n
  cases n <;> simp [aPhiH, Minor.toSeries, formalSeries]

private lemma aPhiH_good_plus {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (aPhiH φ).Good (wedgePlusH h.α₀ (ε₀H h)) (dPlusH h) := by
  refine ⟨h.analyticOn.mono (wedgePlusH_subset_punctured h), ?_⟩
  change ExpType (Minor.pull (dPlusH h) φ)
  simpa [dPlusH] using h.expType_plus

private lemma aPhiH_good_minus {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (aPhiH φ).Good (wedgeMinusH h.α₀ (ε₀H h)) (dMinusH h) := by
  refine ⟨h.analyticOn.mono (wedgeMinusH_subset_punctured h), ?_⟩
  change ExpType (Minor.pull (dMinusH h) φ)
  simpa [dMinusH, neg_mul] using h.expType_minus

private lemma analyticAt_eqOn_zero_of_iteratedDeriv_zeroH {U : Set ℂ} {f : ℂ → ℂ}
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

private def polyMinor (q : Polynomial ℂ) : Minor :=
  ⟨q.coeff 0, fun z : ℂ =>
    ∑ m ∈ Finset.range q.natDegree, (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m⟩

private lemma polyMinor_C (c : ℂ) : polyMinor (Polynomial.C c) = Minor.const c := by
  simp [polyMinor, Minor.const]

private lemma polyMinor_toSeries (q : Polynomial ℂ) :
    (polyMinor q).toSeries = (q : PowerSeries ℂ) := by
  ext n
  cases n with
  | zero => simp [polyMinor, Minor.toSeries]
  | succ k =>
    simp only [polyMinor, Minor.toSeries, PowerSeries.coeff_mk, Polynomial.coeff_coe]
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
      · subst hkm
        simp only [↓reduceIte]
        have hfac : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
        field_simp [hfac]
      · simp [hkm, Ne.symm hkm]
    rw [Finset.sum_congr rfl hterm]
    by_cases hk : k < q.natDegree
    · rw [Finset.sum_ite_eq']
      simp [Finset.mem_range.mpr hk]
    · have hnot : k ∉ Finset.range q.natDegree := by simpa [Finset.mem_range] using hk
      rw [Finset.sum_ite_eq', ite_eq_right_iff.mpr fun hmem => absurd hmem hnot]
      have hlt : q.natDegree < k + 1 := by omega
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt hlt).symm

private lemma polyMinor_good (q : Polynomial ℂ) (U : Set ℂ) (d : ℂ) :
    (polyMinor q).Good U d := by
  refine ⟨?_, ?_⟩
  · intro z _
    dsimp only [polyMinor]
    exact Finset.analyticAt_fun_sum _ fun m _ => by fun_prop
  · refine ⟨∑ m ∈ Finset.range q.natDegree, ‖d‖ ^ (m + 1) * ‖q.coeff (m + 1)‖, 1,
      Finset.sum_nonneg (fun _ _ => by positivity), zero_le_one, fun v hv => ?_⟩
    rw [Minor.pull]
    dsimp only [polyMinor]
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

private lemma polyMinor_value (q : Polynomial ℂ) {d p : ℂ} (hp : 0 < (p * d).re) :
    (polyMinor q).value d p = q.eval p⁻¹ := by
  have hpd0 : p * d ≠ 0 := fun h0 => by simp [h0] at hp
  have hp0 : p ≠ 0 := left_ne_zero_of_mul hpd0
  have hd0 : d ≠ 0 := right_ne_zero_of_mul hpd0
  unfold Minor.value polyMinor complexLaplace
  dsimp only
  have heq : (fun v : ℝ => damped (p * d)
      (Minor.pull d fun z => ∑ m ∈ Finset.range q.natDegree,
        (q.coeff (m + 1) / (m.factorial : ℂ)) * z ^ m) v) =
      fun v : ℝ => ∑ m ∈ Finset.range q.natDegree,
        (d ^ (m + 1) * (q.coeff (m + 1) / (m.factorial : ℂ))) *
          (Complex.exp (-(p * d) * (v : ℂ)) * (v : ℂ) ^ m) := by
    funext v
    simp only [damped, Minor.pull, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [mul_pow, pow_succ']
    ring
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
  simp only [pow_zero, mul_one]
  ring

private inductive PolyBorelExpr where
  | poly (q : Polynomial ℂ)
  | leaf
  | add (e f : PolyBorelExpr)
  | mul (e f : PolyBorelExpr)
  | jet (e : PolyBorelExpr)

namespace PolyBorelExpr

private def residual (a : Minor) : PolyBorelExpr → Minor
  | poly q => polyMinor q
  | leaf => a
  | add e f => (e.residual a).plus (f.residual a)
  | mul e f => (e.residual a).times (f.residual a)
  | jet e => (e.residual a).jet

private def eval (a : Minor) (d : ℂ) : PolyBorelExpr → ℂ → ℂ
  | poly q => fun p => q.eval p⁻¹
  | leaf => a.value d
  | add e f => fun p => e.eval a d p + f.eval a d p
  | mul e f => fun p => e.eval a d p * f.eval a d p
  | jet e => fun p => deriv (e.eval a d) p

private def ofBorelExpr : BorelExpr → PolyBorelExpr
  | .const c => poly (Polynomial.C c)
  | .leaf => leaf
  | .add e f => add (ofBorelExpr e) (ofBorelExpr f)
  | .mul e f => mul (ofBorelExpr e) (ofBorelExpr f)
  | .jet e => jet (ofBorelExpr e)

private lemma ofBorelExpr_residual (e : BorelExpr) (a : Minor) :
    (ofBorelExpr e).residual a = e.residual a := by
  induction e with
  | const c => simp [ofBorelExpr, residual, BorelExpr.residual, polyMinor_C]
  | leaf => rfl
  | add e f he hf => simp [ofBorelExpr, residual, BorelExpr.residual, he, hf]
  | mul e f he hf => simp [ofBorelExpr, residual, BorelExpr.residual, he, hf]
  | jet e he => simp [ofBorelExpr, residual, BorelExpr.residual, he]

private lemma ofBorelExpr_eval (e : BorelExpr) (a : Minor) (d : ℂ) :
    (ofBorelExpr e).eval a d = e.eval a d := by
  induction e with
  | const c => funext p; simp [ofBorelExpr, eval, BorelExpr.eval]
  | leaf => rfl
  | add e f he hf => funext p; simp [ofBorelExpr, eval, BorelExpr.eval, he, hf]
  | mul e f he hf => funext p; simp [ofBorelExpr, eval, BorelExpr.eval, he, hf]
  | jet e he => funext p; simp [ofBorelExpr, eval, BorelExpr.eval, he]

private lemma ofBorelExpr_jetIter (j : ℕ) :
    ofBorelExpr (Nat.iterate BorelExpr.jet j BorelExpr.leaf) =
      Nat.iterate jet j leaf := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ofBorelExpr, ih]

private lemma represents (e : PolyBorelExpr) {U : Set ℂ} {d : ℂ} (hU : Domain U)
    (ray : ContainsRay U d) {a : Minor} (ha : a.Good U d) :
    (e.residual a).Good U d ∧ e.eval a d =ᶠ[BorelStokesVandermonde.far d] (e.residual a).value d := by
  induction e with
  | poly q =>
    refine ⟨polyMinor_good q U d, ?_⟩
    filter_upwards [eventually_bound_far d 0] with p hp
    exact (polyMinor_value q hp).symm
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

private lemma exists_of_mvPolynomial {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    ∃ e : PolyBorelExpr,
      (∀ (U : Set ℂ) (d : ℂ) (a : Minor), Domain U → ContainsRay U d → a.Good U d →
        (e.residual a).toSeries = formalEvalW a.toSeries Q) ∧
      (∀ (U : Set ℂ) (d : ℂ) (a : Minor) (_hU : Domain U) (_ray : ContainsRay U d)
        (_ha : a.Good U d) (_hd : 0 < d.re),
        ∀ᶠ u : ℝ in atTop,
          e.eval a d (u : ℂ) =
            MvPolynomial.eval
              (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => a.value d (t : ℂ)) u)
              (evalU Q (u : ℂ)⁻¹)) := by
  induction Q using MvPolynomial.induction_on with
  | C q =>
    refine ⟨poly q, ?_, ?_⟩
    · intro U d a _ _ _
      simp [residual, polyMinor_toSeries, formalEvalW]
    · intro U d a _ _ _ _
      exact .of_forall fun u => by simp [eval, evalU]
  | add Q₁ Q₂ h₁ h₂ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    obtain ⟨e₂, hs₂, he₂⟩ := h₂
    refine ⟨add e₁ e₂, ?_, ?_⟩
    · intro U d a hU ray ha
      have hg₁ := (e₁.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      have hg₂ := (e₂.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      rw [residual, Minor.toSeries_plus hg₁ hg₂, hs₁ U d a hU ray ha, hs₂ U d a hU ray ha]
      simp [formalEvalW]
    · intro U d a hU ray ha hd
      filter_upwards [he₁ U d a hU ray ha hd, he₂ U d a hU ray ha hd] with u hu₁ hu₂
      simp [eval, evalU, hu₁, hu₂]
  | mul_X Q₁ j h₁ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    let ej : PolyBorelExpr := Nat.iterate jet j.val leaf
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
      simp [formalEvalW]
    · intro U d a hU ray ha hd
      have hjet_eq := (BorelExpr.jetIter_eval_eq_iteratedDeriv a hU ray ha hd j.val).1
      filter_upwards [he₁ U d a hU ray ha hd, hjet_eq] with u hu₁ huj
      have heval_eq : ej.eval a d (u : ℂ) =
          (Nat.iterate BorelExpr.jet j.val BorelExpr.leaf).eval a d (u : ℂ) := by
        dsimp only [ej]
        rw [← ofBorelExpr_jetIter, ofBorelExpr_eval]
      simp only [eval, evalU, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X] at hu₁ ⊢
      rw [heval_eq, hu₁, huj]

end PolyBorelExpr

private lemma formalEvalPoly_zero_implies_lateral_zero {φ ω ord pp}
    (h : HigherOrderBorelData φ 0 ω ord pp)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries φ) P = 0) :
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ)) u)
        (evalU P (u : ℂ)) = 0) ∧
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun t : ℝ => (aPhiH φ).value (dMinusH h) (t : ℂ)) u)
        (evalU P (u : ℂ)) = 0) := by
  let N := maxUDeg P
  let Q := revMvPoly N P
  have hNP : ∀ α, (P.coeff α).natDegree ≤ N := natDegree_le_maxUDeg P
  have hQ0 : formalEvalW (formalSeries φ) Q = 0 :=
    (formalEvalW_eq_zero_iff_formalEvalPoly (formalSeries φ) P hNP).mpr hP
  let Up := wedgePlusH h.α₀ (ε₀H h)
  let Um := wedgeMinusH h.α₀ (ε₀H h)
  have hUp_dom : Domain Up := wedgePlusH_domain h.α₀ (ε₀H_pos h)
  have hUm_dom : Domain Um := wedgeMinusH_domain h.α₀ (ε₀H_pos h)
  have hrayP : ContainsRay Up (dPlusH h) := wedgePlusH_containsRay h
  have hrayM : ContainsRay Um (dMinusH h) := wedgeMinusH_containsRay h
  have hgoodP : (aPhiH φ).Good Up (dPlusH h) := aPhiH_good_plus h
  have hgoodM : (aPhiH φ).Good Um (dMinusH h) := aPhiH_good_minus h
  have hreP : 0 < (dPlusH h).re := by rw [dPlusH_re h]; exact cos_pos_θH h
  have hreM : 0 < (dMinusH h).re := by rw [dMinusH_re h]; exact cos_pos_θH h
  obtain ⟨e, hs, he⟩ := PolyBorelExpr.exists_of_mvPolynomial Q
  have hres_series : (e.residual (aPhiH φ)).toSeries = 0 := by
    rw [hs Up (dPlusH h) (aPhiH φ) hUp_dom hrayP hgoodP, aPhiH_toSeries, hQ0]
  have hatom : (e.residual (aPhiH φ)).atom = 0 := by
    have := congrArg (PowerSeries.coeff 0) hres_series
    simpa [Minor.toSeries] using this
  have hderiv_zero : ∀ k : ℕ, iteratedDeriv k (e.residual (aPhiH φ)).density 0 = 0 := by
    intro k
    have := congrArg (PowerSeries.coeff (k + 1)) hres_series
    simpa [Minor.toSeries] using this
  have hplus_dens : EqOn (e.residual (aPhiH φ)).density 0 Up :=
    analyticAt_eqOn_zero_of_iteratedDeriv_zeroH (isPreconnected_wedgePlusH h)
      (by simpa using hrayP 0 le_rfl) (e.represents hUp_dom hrayP hgoodP).1.1 hderiv_zero
  have hminus_dens : EqOn (e.residual (aPhiH φ)).density 0 Um :=
    analyticAt_eqOn_zero_of_iteratedDeriv_zeroH (isPreconnected_wedgeMinusH h)
      (by simpa using hrayM 0 le_rfl) (e.represents hUm_dom hrayM hgoodM).1.1 hderiv_zero
  constructor
  · have hrep := (tendsto_coe_far hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
    filter_upwards [hrep, he Up (dPlusH h) (aPhiH φ) hUp_dom hrayP hgoodP hreP,
      eventually_gt_atTop (0 : ℝ)] with u hu_rep hu_ev hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hevalQ : MvPolynomial.eval (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ)) u)
        (evalU Q (u : ℂ)⁻¹) = 0 := by
      rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      simp [damped, Minor.pull, hplus_dens (hrayP v hv.le)]
    rw [show Q = revMvPoly N P from rfl, evalU_revMvPoly P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C] at hevalQ
    exact (mul_eq_zero.mp hevalQ).resolve_left (pow_ne_zero N (inv_ne_zero hu_ne))
  · have hrep := (tendsto_coe_far hreM).eventually (e.represents hUm_dom hrayM hgoodM).2
    filter_upwards [hrep, he Um (dMinusH h) (aPhiH φ) hUm_dom hrayM hgoodM hreM,
      eventually_gt_atTop (0 : ℝ)] with u hu_rep hu_ev hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hevalQ : MvPolynomial.eval (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun t : ℝ => (aPhiH φ).value (dMinusH h) (t : ℂ)) u)
        (evalU Q (u : ℂ)⁻¹) = 0 := by
      rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
      refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
      simp [damped, Minor.pull, hminus_dens (hrayM v hv.le)]
    rw [show Q = revMvPoly N P from rfl, evalU_revMvPoly P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C] at hevalQ
    exact (mul_eq_zero.mp hevalQ).resolve_left (pow_ne_zero N (inv_ne_zero hu_ne))

private lemma eval_lateral_flat_implies_formalEvalPoly_zero {φ ω ord pp}
    (h : HigherOrderBorelData φ 0 ω ord pp)
    {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) =>
        iteratedDeriv j.val (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ)) u)
        (evalU P (u : ℂ))‖ ≤ C * Real.exp (-δ₀ * u)) :
    formalEvalPoly (formalSeries φ) P = 0 := by
  let N := maxUDeg P
  let Q := revMvPoly N P
  have hNP : ∀ α, (P.coeff α).natDegree ≤ N := natDegree_le_maxUDeg P
  let Up := wedgePlusH h.α₀ (ε₀H h)
  have hUp_dom : Domain Up := wedgePlusH_domain h.α₀ (ε₀H_pos h)
  have hrayP : ContainsRay Up (dPlusH h) := wedgePlusH_containsRay h
  have hgoodP : (aPhiH φ).Good Up (dPlusH h) := aPhiH_good_plus h
  have hreP : 0 < (dPlusH h).re := by rw [dPlusH_re h]; exact cos_pos_θH h
  obtain ⟨C, hC⟩ := hP
  obtain ⟨e, hs, he⟩ := PolyBorelExpr.exists_of_mvPolynomial Q
  have hrep := (tendsto_coe_far hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
  have hflat : ∀ M : ℕ, ∃ C_M : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖(e.residual (aPhiH φ)).value (dPlusH h) (u : ℂ)‖ ≤ C_M / u ^ (M + 1) := by
    intro M
    refine ⟨max C 0 * (((M + 1).factorial : ℝ) / δ₀ ^ (M + 1)), ?_⟩
    filter_upwards [hC, hrep, he Up (dPlusH h) (aPhiH φ) hUp_dom hrayP hgoodP hreP,
      eventually_ge_atTop (1 : ℝ)] with u huC hurep huev hu1
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hinv_le1 : ‖(u : ℂ)⁻¹ ^ N‖ ≤ 1 := by
      rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
      exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu1)
    rw [← hurep, huev, show Q = revMvPoly N P from rfl, evalU_revMvPoly P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, norm_mul]
    have hexp : Real.exp (-δ₀ * u) ≤ ((M + 1).factorial : ℝ) / (δ₀ ^ (M + 1) * u ^ (M + 1)) := by
      have harg := Real.pow_div_factorial_le_exp (δ₀ * u) (by positivity) (M + 1)
      have hfac : 0 < ((M + 1).factorial : ℝ) := by positivity
      have hpow : 0 < (δ₀ * u) ^ (M + 1) := pow_pos (by positivity) (M + 1)
      calc Real.exp (-δ₀ * u) = (Real.exp (δ₀ * u))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
        _ ≤ ((δ₀ * u) ^ (M + 1) / ((M + 1).factorial : ℝ))⁻¹ :=
            inv_anti₀ (div_pos hpow hfac) harg
        _ = ((M + 1).factorial : ℝ) / (δ₀ ^ (M + 1) * u ^ (M + 1)) := by
            rw [inv_div, mul_pow]
    calc ‖(u : ℂ)⁻¹ ^ N‖ * ‖MvPolynomial.eval (fun j : Fin (r + 1) =>
            iteratedDeriv j.val (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ)) u)
            (evalU P (u : ℂ))‖
        ≤ 1 * (C * Real.exp (-δ₀ * u)) :=
          mul_le_mul hinv_le1 huC (norm_nonneg _) zero_le_one
      _ ≤ max C 0 * Real.exp (-δ₀ * u) := by
          rw [one_mul]
          exact mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le
      _ ≤ max C 0 * (((M + 1).factorial : ℝ) / (δ₀ ^ (M + 1) * u ^ (M + 1))) :=
          mul_le_mul_of_nonneg_left hexp (le_max_right C 0)
      _ = (max C 0 * (((M + 1).factorial : ℝ) / δ₀ ^ (M + 1))) / u ^ (M + 1) := by ring
  have hzero := Minor.toSeries_eq_zero_of_flat (e.residual (aPhiH φ)) hUp_dom hrayP
    (e.represents hUp_dom hrayP hgoodP).1 hreP hflat
  rw [hs Up (dPlusH h) (aPhiH φ) hUp_dom hrayP hgoodP, aPhiH_toSeries] at hzero
  exact (formalEvalW_eq_zero_iff_formalEvalPoly (formalSeries φ) P hNP).mp hzero

private lemma lateral_bounded_derivativesH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp)
    (j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ)) u‖ ≤ C := by
  let Up := wedgePlusH h.α₀ (ε₀H h)
  have hUp_dom : Domain Up := wedgePlusH_domain h.α₀ (ε₀H_pos h)
  have hrayP : ContainsRay Up (dPlusH h) := wedgePlusH_containsRay h
  have hgoodP : (aPhiH φ).Good Up (dPlusH h) := aPhiH_good_plus h
  have hreP : 0 < (dPlusH h).re := by rw [dPlusH_re h]; exact cos_pos_θH h
  let e := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have ha := (e.represents hUp_dom hrayP hgoodP).1
  obtain ⟨C₀, hC₀_nonneg, hC₀⟩ := Minor.value_asymptotic (e.residual (aPhiH φ)) hUp_dom hrayP ha hreP 0
  have hrep := (tendsto_coe_far hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
  have heq := (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiH φ) hUp_dom hrayP hgoodP hreP j).1
  refine ⟨‖(e.residual (aPhiH φ)).atom‖ + C₀, ?_⟩
  filter_upwards [hC₀, hrep, heq, eventually_ge_atTop (1 : ℝ)] with u hu0 hurep hueq hu1
  have heq' : iteratedDeriv j (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ)) u =
      (e.residual (aPhiH φ)).value (dPlusH h) (u : ℂ) := hueq.symm.trans hurep
  rw [heq']
  have hu0' : ‖(e.residual (aPhiH φ)).value (dPlusH h) (u : ℂ) - (e.residual (aPhiH φ)).atom‖ ≤ C₀ := by
    simpa using hu0.trans (div_le_self hC₀_nonneg (one_le_pow₀ hu1))
  calc ‖(e.residual (aPhiH φ)).value (dPlusH h) (u : ℂ)‖
      = ‖((e.residual (aPhiH φ)).value (dPlusH h) (u : ℂ) - (e.residual (aPhiH φ)).atom) +
          (e.residual (aPhiH φ)).atom‖ := by congr 1; ring
    _ ≤ ‖(e.residual (aPhiH φ)).value (dPlusH h) (u : ℂ) - (e.residual (aPhiH φ)).atom‖ +
          ‖(e.residual (aPhiH φ)).atom‖ := norm_add_le _ _
    _ ≤ ‖(e.residual (aPhiH φ)).atom‖ + C₀ := by linarith

private lemma lateral_eventually_differentiableH {φ ω ord pp}
    (h : HigherOrderBorelData φ 0 ω ord pp) (k : ℕ) :
    (∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ
      (iteratedDeriv k (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ))) u) ∧
    (∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ
      (iteratedDeriv k (fun t : ℝ => (aPhiH φ).value (dMinusH h) (t : ℂ))) u) :=
  ⟨(BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiH φ) (wedgePlusH_domain h.α₀ (ε₀H_pos h))
      (wedgePlusH_containsRay h) (aPhiH_good_plus h) (by rw [dPlusH_re h]; exact cos_pos_θH h) k).2,
   (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiH φ) (wedgeMinusH_domain h.α₀ (ε₀H_pos h))
      (wedgeMinusH_containsRay h) (aPhiH_good_minus h) (by rw [dMinusH_re h]; exact cos_pos_θH h) k).2⟩

/-! ### 5. Higher-Order Triangle Residue Formula and Stokes Jump Expansion -/

private def TriBdIntegrableH (F : ℂ → ℂ) (R m : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) volume 0 R ∧
  IntervalIntegrable (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) volume (-m * R) (m * R) ∧
  IntervalIntegrable (fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) volume 0 R

private lemma triIntegral_addH {F G : ℂ → ℂ} {R m : ℝ}
    (hF : TriBdIntegrableH F R m) (hG : TriBdIntegrableH G R m) :
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
    intervalIntegral.integral_add hF.2.2 hG.2.2]
  ring

private lemma triIntegral_const_mulH (c : ℂ) (F : ℂ → ℂ) (R m : ℝ) :
    triIntegral (fun z => c * F z) R m = c * triIntegral F R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (c * F ((x : ℂ) * (1 - I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) := by funext x; ring
  have h2 : (fun x : ℝ => (1 + I * (m : ℂ)) * (c * F ((x : ℂ) * (1 + I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) := by funext x; ring
  rw [h1, h2, intervalIntegral.integral_const_mul c, intervalIntegral.integral_const_mul c,
    intervalIntegral.integral_const_mul c]
  ring

private lemma triIntegral_sumH {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (R m : ℝ)
    (hF : ∀ i ∈ s, TriBdIntegrableH (F i) R m) :
    triIntegral (fun z => ∑ i ∈ s, F i z) R m = ∑ i ∈ s, triIntegral (F i) R m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [triIntegral]
  | @insert i s hi ih =>
    have hFi : TriBdIntegrableH (F i) R m := hF i (Finset.mem_insert_self i s)
    have hFs : ∀ j ∈ s, TriBdIntegrableH (F j) R m := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hsum_int : TriBdIntegrableH (fun z => ∑ j ∈ s, F j z) R m := by
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
    rw [hfn, triIntegral_addH hFi hsum_int, ih hFs, Finset.sum_insert hi]

private lemma triIntegral_congrH {F G : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 - I * (m : ℂ))) = G ((x : ℂ) * (1 - I * (m : ℂ))))
    (h2 : ∀ y ∈ Icc (-m * R) (m * R), F ((R : ℂ) + (y : ℂ) * I) = G ((R : ℂ) + (y : ℂ) * I))
    (h3 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 + I * (m : ℂ))) = G ((x : ℂ) * (1 + I * (m : ℂ)))) :
    triIntegral F R m = triIntegral G R m := by
  unfold triIntegral
  have hmR : -m * R ≤ m * R := by nlinarith
  have i1 : (∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hR] at hx; rw [h1 x hx]
  have i2 : (∫ y : ℝ in (-m * R)..(m * R), F ((R : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in (-m * R)..(m * R), G ((R : ℂ) + (y : ℂ) * I) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hmR] at hy; rw [h2 y hy]
  have i3 : (∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hR] at hx; rw [h3 x hx]
  rw [i1, i2, i3]

private lemma triBdIntegrable_of_continuousOnH {F : ℂ → ℂ} {R m : ℝ}
    (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 - I * (m : ℂ)))) (Icc 0 R))
    (h2 : ContinuousOn (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) (Icc (-m * R) (m * R)))
    (h3 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 + I * (m : ℂ)))) (Icc 0 R)) :
    TriBdIntegrableH F R m :=
  ⟨(continuousOn_const.mul h1).intervalIntegrable_of_Icc hR,
   h2.intervalIntegrable_of_Icc (by nlinarith),
   (continuousOn_const.mul h3).intervalIntegrable_of_Icc hR⟩

private lemma mem_closedTri_mul_one_addH {R m x t : ℝ} (_hR : 0 ≤ R) (_hm : 0 ≤ m)
    (hx : x ∈ Icc 0 R) (ht : t ∈ Icc (-m) m) :
    (x : ℂ) * (1 + I * (t : ℂ)) ∈ closedTri R m := by
  have hre : ((x : ℂ) * (1 + I * (t : ℂ))).re = x := by simp [Complex.mul_re]
  have him : ((x : ℂ) * (1 + I * (t : ℂ))).im = x * t := by simp [Complex.mul_im]
  refine ⟨by rw [hre]; exact hx.1, by rw [hre]; exact hx.2, ?_⟩
  rw [hre, him, abs_mul, abs_of_nonneg hx.1, mul_comm m x]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ht) hx.1

private lemma triBd_avoid_point {c R m : ℝ} (hc : 0 < c) (hR : c < R) (hm : 0 < m) :
    (∀ x : ℝ, (x : ℂ) * (1 - I * (m : ℂ)) ≠ (c : ℂ)) ∧
    (∀ x : ℝ, (x : ℂ) * (1 + I * (m : ℂ)) ≠ (c : ℂ)) ∧
    (∀ y : ℝ, (R : ℂ) + (y : ℂ) * I ≠ (c : ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x h0
    have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, zero_sub, add_zero] at him
    have hx0 : x = 0 := by
      have : x * (-m) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right (neg_ne_zero.mpr hm.ne')
    subst hx0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
    linarith
  · intro x h0
    have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add] at him
    have hx0 : x = 0 := by
      have : x * m = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hm.ne'
    subst hx0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
    linarith
  · intro y h0
    have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, Complex.ofReal_im] at hre
    linarith

private lemma triIntegral_inv_sub_pow_ge_two {c R m : ℝ} (hc : 0 < c) (hR : c < R) (hm : 0 < m)
    (k : ℕ) :
    triIntegral (fun z : ℂ => ((z - (c : ℂ))⁻¹) ^ (k + 2)) R m = 0 := by
  have h_av := triBd_avoid_point hc hR hm
  let G (z : ℂ) : ℂ := -(((k + 1 : ℕ) : ℂ))⁻¹ * ((z - (c : ℂ))⁻¹) ^ (k + 1)
  have hG_deriv : ∀ z : ℂ, z ≠ (c : ℂ) →
      HasDerivAt G (((z - (c : ℂ))⁻¹) ^ (k + 2)) z := by
    intro z hzc
    have hsub : z - (c : ℂ) ≠ 0 := sub_ne_zero.mpr hzc
    have hinv : HasDerivAt (fun w : ℂ => (w - (c : ℂ))⁻¹) (-1 / (z - (c : ℂ)) ^ 2) z :=
      ((hasDerivAt_id z).sub_const (c : ℂ)).inv hsub
    have hpow := (hinv.pow (k + 1)).const_mul (-(((k + 1 : ℕ) : ℂ))⁻¹)
    simp only [Nat.add_sub_cancel, div_eq_mul_inv] at hpow
    refine hpow.congr_deriv ?_
    have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [inv_pow]
    field_simp [hk1, hsub]
    rw [← pow_add]
    ring_nf
  have h1 : ∫ x : ℝ in (0 : ℝ)..R,
      (1 - I * (m : ℂ)) * ((((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2)) =
      G ((R : ℂ) * (1 - I * (m : ℂ))) - G 0 := by
    have hd : ∀ x ∈ uIcc (0 : ℝ) R,
        HasDerivAt (fun t : ℝ => G ((t : ℂ) * (1 - I * (m : ℂ))))
          ((1 - I * (m : ℂ)) * ((((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2))) x := by
      intro x _
      have ha : HasDerivAt (fun t : ℝ => (t : ℂ) * (1 - I * (m : ℂ))) (1 - I * (m : ℂ)) x :=
        ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const (1 - I * (m : ℂ))).congr_deriv (one_mul _)
      exact ((hG_deriv _ (h_av.1 x)).comp x ha).congr_deriv (mul_comm _ _)
    have hc_int : Continuous (fun x : ℝ =>
        (1 - I * (m : ℂ)) * ((((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2))) :=
      continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun x h0 =>
        h_av.1 x (sub_eq_zero.mp h0)).pow _)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc_int.intervalIntegrable 0 R)
    simpa only [Complex.ofReal_zero, zero_mul] using hftc
  have h2 : I * (∫ y : ℝ in (-m * R)..(m * R),
      ((((R : ℂ) + (y : ℂ) * I - (c : ℂ))⁻¹) ^ (k + 2))) =
      G ((R : ℂ) * (1 + I * (m : ℂ))) - G ((R : ℂ) * (1 - I * (m : ℂ))) := by
    have hd : ∀ y ∈ uIcc (-m * R) (m * R),
        HasDerivAt (fun s : ℝ => G ((R : ℂ) + (s : ℂ) * I))
          (I * ((((R : ℂ) + (y : ℂ) * I - (c : ℂ))⁻¹) ^ (k + 2))) y := by
      intro y _
      have ha : HasDerivAt (fun s : ℝ => (R : ℂ) + (s : ℂ) * I) I y :=
        (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).congr_deriv (one_mul I)).const_add (R : ℂ)
      exact ((hG_deriv _ (h_av.2.2 y)).comp y ha).congr_deriv (mul_comm _ _)
    have hc_int : Continuous (fun y : ℝ =>
        I * ((((R : ℂ) + (y : ℂ) * I - (c : ℂ))⁻¹) ^ (k + 2))) :=
      continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun y h0 =>
        h_av.2.2 y (sub_eq_zero.mp h0)).pow _)
    have h_p : (R : ℂ) + ((m * R : ℝ) : ℂ) * I = (R : ℂ) * (1 + I * (m : ℂ)) := by push_cast; ring
    have h_m : (R : ℂ) + ((-m * R : ℝ) : ℂ) * I = (R : ℂ) * (1 - I * (m : ℂ)) := by push_cast; ring
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc_int.intervalIntegrable (-m * R) (m * R)),
      h_p, h_m]
  have h3 : ∫ x : ℝ in (0 : ℝ)..R,
      (1 + I * (m : ℂ)) * ((((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2)) =
      G ((R : ℂ) * (1 + I * (m : ℂ))) - G 0 := by
    have hd : ∀ x ∈ uIcc (0 : ℝ) R,
        HasDerivAt (fun t : ℝ => G ((t : ℂ) * (1 + I * (m : ℂ))))
          ((1 + I * (m : ℂ)) * ((((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2))) x := by
      intro x _
      have ha : HasDerivAt (fun t : ℝ => (t : ℂ) * (1 + I * (m : ℂ))) (1 + I * (m : ℂ)) x :=
        ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const (1 + I * (m : ℂ))).congr_deriv (one_mul _)
      exact ((hG_deriv _ (h_av.2.1 x)).comp x ha).congr_deriv (mul_comm _ _)
    have hc_int : Continuous (fun x : ℝ =>
        (1 + I * (m : ℂ)) * ((((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2))) :=
      continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun x h0 =>
        h_av.2.1 x (sub_eq_zero.mp h0)).pow _)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc_int.intervalIntegrable 0 R)
    simpa only [Complex.ofReal_zero, zero_mul] using hftc
  unfold triIntegral
  rw [h1, h2, h3]
  ring

private lemma dslopeIter_analyticOn {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ)
    (c : ℂ) (k : ℕ) :
    AnalyticOnNhd ℂ ((Function.swap dslope c)^[k] F) univ := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hd : DifferentiableOn ℂ (dslope ((Function.swap dslope c)^[k] F) c) univ :=
      (Complex.differentiableOn_dslope (Filter.univ_mem : univ ∈ 𝓝 c)).mpr ih.differentiableOn
    exact hd.analyticOnNhd isOpen_univ

private lemma div_sub_pow_eq_dslopeIter (F : ℂ → ℂ) (c : ℂ) (k : ℕ) {z : ℂ} (hz : z ≠ c) :
    F z / (z - c) ^ (k + 1) =
      ((Function.swap dslope c)^[k + 1] F) z +
        ∑ p ∈ Finset.range (k + 1), ((Function.swap dslope c)^[p] F c) * (z - c)⁻¹ ^ (k + 1 - p) := by
  have hsub : z - c ≠ 0 := sub_ne_zero.mpr hz
  induction k with
  | zero =>
    rw [zero_add, pow_one, Function.iterate_one, Finset.range_one, Finset.sum_singleton,
      Function.iterate_zero_apply, Nat.sub_zero, pow_one]
    have hsl := sub_smul_dslope F c z
    rw [smul_eq_mul] at hsl
    dsimp only [Function.swap]
    rw [← sub_add_cancel (F z) (F c), ← hsl, add_div, mul_div_cancel_left₀ _ hsub, div_eq_mul_inv,
      add_comm]
  | succ k ih =>
    rw [pow_succ, ← div_div, ih, add_div, Finset.sum_div]
    have hsplit : ((Function.swap dslope c)^[k + 1] F) z / (z - c) =
        ((Function.swap dslope c)^[k + 2] F) z +
          ((Function.swap dslope c)^[k + 1] F c) * (z - c)⁻¹ := by
      have hsl := sub_smul_dslope ((Function.swap dslope c)^[k + 1] F) c z
      rw [Function.iterate_succ_apply' (Function.swap dslope c) (k + 1) F]
      change _ = dslope ((Function.swap dslope c)^[k + 1] F) c z + _
      rw [smul_eq_mul] at hsl
      rw [← sub_add_cancel (((Function.swap dslope c)^[k + 1] F) z) (((Function.swap dslope c)^[k + 1] F) c),
        ← hsl, add_div, mul_div_cancel_left₀ _ hsub, div_eq_mul_inv]
    rw [hsplit, add_assoc]
    congr 1
    rw [Finset.sum_range_succ (fun p => ((Function.swap dslope c)^[p] F c) * (z - c)⁻¹ ^ (k + 1 + 1 - p))
      (k + 1), add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp_le : p ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      rw [show k + 1 + 1 - p = (k + 1 - p) + 1 by omega, pow_succ, div_eq_mul_inv]
      ring
    · simp

private lemma iterated_dslope_apply_self {F : ℂ → ℂ} {c : ℂ} (hF : AnalyticAt ℂ F c) (k : ℕ) :
    ((Function.swap dslope c)^[k] F) c = iteratedDeriv k F c / (k.factorial : ℂ) := by
  have hf_ps := hF.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k
  rw [← hf_ps.coeff_zero 1, ← FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.coeff_iterate_fslope, zero_add,
    FormalMultilinearSeries.coeff_ofScalars]

private lemma triIntegral_mul_inv_sub_pow {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ)
    {c R m : ℝ} (hc : 0 < c) (hR : c < R) (hm : 0 < m) {s : ℕ} (hs : 1 ≤ s) :
    triIntegral (fun z : ℂ => F z / (z - (c : ℂ)) ^ s) R m =
      2 * (Real.pi : ℂ) * I * (iteratedDeriv (s - 1) F (c : ℂ) / ((s - 1).factorial : ℂ)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, s = k + 1 := ⟨s - 1, by omega⟩
  subst hk
  have h_av := triBd_avoid_point hc hR hm
  have hR_pos : 0 < R := lt_trans hc hR
  let G_rem : ℂ → ℂ := (Function.swap dslope (c : ℂ))^[k + 1] F
  have hG_an : AnalyticOnNhd ℂ G_rem univ := dslopeIter_analyticOn hF (c : ℂ) (k + 1)
  have htri_rem : triIntegral G_rem R m = 0 :=
    triIntegral_eq_zero_of_analyticOn hR_pos.le hm.le isOpen_univ (subset_univ _) hG_an
  have hG_int : TriBdIntegrableH G_rem R m :=
    triBdIntegrable_of_continuousOnH hR_pos.le hm.le
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
  let termP (p : ℕ) (z : ℂ) : ℂ :=
    ((Function.swap dslope (c : ℂ))^[p] F (c : ℂ)) * ((z - (c : ℂ))⁻¹) ^ (k + 1 - p)
  have htermP_int : ∀ p ∈ Finset.range (k + 1), TriBdIntegrableH (termP p) R m := by
    intro p _
    refine triBdIntegrable_of_continuousOnH hR_pos.le hm.le
      (Continuous.continuousOn (continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun x h0 =>
        h_av.1 x (sub_eq_zero.mp h0)).pow _)))
      (Continuous.continuousOn (continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun y h0 =>
        h_av.2.2 y (sub_eq_zero.mp h0)).pow _)))
      (Continuous.continuousOn (continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun x h0 =>
        h_av.2.1 x (sub_eq_zero.mp h0)).pow _)))
  have hsumP_int : TriBdIntegrableH (fun z => ∑ p ∈ Finset.range (k + 1), termP p z) R m := by
    refine ⟨?_, ?_, ?_⟩
    · have heq : (fun x : ℝ => (1 - I * (m : ℂ)) *
          ∑ p ∈ Finset.range (k + 1), termP p ((x : ℂ) * (1 - I * (m : ℂ)))) =
          ∑ p ∈ Finset.range (k + 1), fun x : ℝ =>
            (1 - I * (m : ℂ)) * termP p ((x : ℂ) * (1 - I * (m : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun p hp => (htermP_int p hp).1
    · have heq : (fun y : ℝ => ∑ p ∈ Finset.range (k + 1), termP p ((R : ℂ) + (y : ℂ) * I)) =
          ∑ p ∈ Finset.range (k + 1), fun y : ℝ => termP p ((R : ℂ) + (y : ℂ) * I) := by
        funext y; rw [Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun p hp => (htermP_int p hp).2.1
    · have heq : (fun x : ℝ => (1 + I * (m : ℂ)) *
          ∑ p ∈ Finset.range (k + 1), termP p ((x : ℂ) * (1 + I * (m : ℂ)))) =
          ∑ p ∈ Finset.range (k + 1), fun x : ℝ =>
            (1 + I * (m : ℂ)) * termP p ((x : ℂ) * (1 + I * (m : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun p hp => (htermP_int p hp).2.2
  have hcongr := triIntegral_congrH
    (F := fun z : ℂ => F z / (z - (c : ℂ)) ^ (k + 1))
    (G := fun z : ℂ => G_rem z + ∑ p ∈ Finset.range (k + 1), termP p z)
    hR_pos.le hm.le
    (fun x _ => div_sub_pow_eq_dslopeIter F (c : ℂ) k (h_av.1 x))
    (fun y _ => div_sub_pow_eq_dslopeIter F (c : ℂ) k (h_av.2.2 y))
    (fun x _ => div_sub_pow_eq_dslopeIter F (c : ℂ) k (h_av.2.1 x))
  rw [hcongr, triIntegral_addH hG_int hsumP_int, htri_rem, zero_add,
    triIntegral_sumH _ _ R m htermP_int]
  have hterm_val : ∀ p ∈ Finset.range (k + 1),
      triIntegral (termP p) R m =
        if p = k then 2 * (Real.pi : ℂ) * I * (iteratedDeriv k F (c : ℂ) / (k.factorial : ℂ)) else 0 := by
    intro p hp
    have hp_le : p ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    dsimp only [termP]
    rw [triIntegral_const_mulH]
    by_cases hpk : p = k
    · subst hpk
      rw [ite_eq_left_iff.mpr fun hne => absurd rfl hne, show p + 1 - p = 1 by omega]
      simp only [pow_one]
      rw [triIntegral_inv_sub hc hR hm, iterated_dslope_apply_self (hF (c : ℂ) (mem_univ _)) p]
      ring
    · have hexp : k + 1 - p = (k - 1 - p) + 2 := by omega
      rw [ite_eq_right_iff.mpr fun heq => absurd heq hpk, hexp,
        triIntegral_inv_sub_pow_ge_two hc hR hm (k - 1 - p), mul_zero]
  rw [Finset.sum_congr rfl hterm_val, Finset.sum_ite_eq']
  simp

private lemma neg_X_pow (n : ℕ) :
    (-Polynomial.X : Polynomial ℂ) ^ n = Polynomial.C ((-1 : ℂ) ^ n) * Polynomial.X ^ n := by
  have hneg : ((-1 : Polynomial ℂ) ^ n) = Polynomial.C ((-1 : ℂ) ^ n) := by
    rw [← Polynomial.C_1, ← Polynomial.C_neg, ← Polynomial.C_pow]
  rw [← neg_one_mul (Polynomial.X : Polynomial ℂ), mul_pow, hneg]

private def polePoly (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (m : ℕ) : Polynomial ℂ :=
  (2 * (Real.pi : ℂ) * I) •
    ∑ s ∈ Finset.Icc 1 (ord m),
      Polynomial.C (pp m s / ((s - 1).factorial : ℂ)) * (-Polynomial.X) ^ (s - 1)

private lemma polePoly_coeff (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (m k : ℕ) :
    (polePoly pp ord m).coeff k =
      if k < ord m then
        2 * (Real.pi : ℂ) * I * (pp m (k + 1) / (k.factorial : ℂ)) * (-1 : ℂ) ^ k
      else 0 := by
  unfold polePoly
  rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, poly_finset_sum_coeff]
  have hterm : ∀ s ∈ Finset.Icc 1 (ord m),
      (Polynomial.C (pp m s / ((s - 1).factorial : ℂ)) * (-Polynomial.X) ^ (s - 1)).coeff k =
        if s = k + 1 then (pp m (k + 1) / (k.factorial : ℂ)) * (-1 : ℂ) ^ k else 0 := by
    intro s hhs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hhs).1
    rw [neg_X_pow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
    by_cases hs : s = k + 1
    · subst hs; simp
    · have hne : k ≠ s - 1 := by omega
      simp [hs, hne]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with hmem hk
  · have : k + 1 ≤ ord m := (Finset.mem_Icc.mp hmem).2
    ring
  · rw [Finset.mem_Icc] at hmem; omega
  · rw [Finset.mem_Icc] at hmem; omega
  · simp

private lemma polePoly_natDegree {pp : ℕ → ℕ → ℂ} {ord : ℕ → ℕ}
    (hord : ∀ m, 1 ≤ ord m) (hpp : ∀ m, pp m (ord m) ≠ 0) (m : ℕ) :
    (polePoly pp ord m).natDegree = ord m - 1 := by
  have hm1 : 1 ≤ ord m := hord m
  have hcoeff_top : (polePoly pp ord m).coeff (ord m - 1) ≠ 0 := by
    rw [polePoly_coeff]
    have hlt : ord m - 1 < ord m := by omega
    rw [ite_eq_left_iff.mpr fun hnot => absurd hlt hnot, show ord m - 1 + 1 = ord m by omega]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hfac : ((ord m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero)
      (div_ne_zero (hpp m) hfac)) (pow_ne_zero _ (by norm_num))
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero hcoeff_top)
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [polePoly_coeff]
  have hnot : ¬ N < ord m := by omega
  rw [ite_eq_right_iff.mpr fun h => absurd h hnot]

private lemma polePoly_leadingCoeff {pp : ℕ → ℕ → ℂ} {ord : ℕ → ℕ}
    (hord : ∀ m, 1 ≤ ord m) (hpp : ∀ m, pp m (ord m) ≠ 0) (m : ℕ) :
    (polePoly pp ord m).leadingCoeff ≠ 0 := by
  have hm1 : 1 ≤ ord m := hord m
  refine Polynomial.leadingCoeff_ne_zero.mpr ?_
  intro h0
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff (ord m - 1)) h0
  rw [Polynomial.coeff_zero, polePoly_coeff] at hc
  have hlt : ord m - 1 < ord m := by omega
  rw [ite_eq_left_iff.mpr fun hnot => absurd hlt hnot, show ord m - 1 + 1 = ord m by omega] at hc
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfac : ((ord m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero)
    (div_ne_zero (hpp m) hfac)) (pow_ne_zero _ (by norm_num)) hc

private lemma iteratedDeriv_neg_pow (j a : ℕ) (z : ℂ) :
    iteratedDeriv a (fun w : ℂ => (-w) ^ j) z =
      (-1 : ℂ) ^ a * ((j.descFactorial a : ℂ) * (-z) ^ (j - a)) := by
  induction a generalizing z with
  | zero => simp
  | succ a ih =>
    rw [iteratedDeriv_succ, show (iteratedDeriv a (fun w : ℂ => (-w) ^ j)) =
      fun w => (-1 : ℂ) ^ a * ((j.descFactorial a : ℂ) * (-w) ^ (j - a)) from funext ih]
    by_cases hja : j ≤ a
    · have hsub0 : j - a = 0 := by omega
      have hdesc0 : j.descFactorial (a + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp only [hsub0, pow_zero, mul_one, hdesc0, Nat.cast_zero, zero_mul, mul_zero]
      exact deriv_const z _
    · have haj : a < j := by omega
      have hd : HasDerivAt (fun w : ℂ => (-1 : ℂ) ^ a * ((j.descFactorial a : ℂ) * (-w) ^ (j - a)))
          ((-1 : ℂ) ^ (a + 1) * ((j.descFactorial (a + 1) : ℂ) * (-z) ^ (j - (a + 1)))) z := by
        have h1 : HasDerivAt (fun w : ℂ => (-w) ^ (j - a))
            (((j - a : ℕ) : ℂ) * (-z) ^ (j - a - 1) * (-1)) z :=
          (hasDerivAt_pow (j - a) (-z)).comp z (hasDerivAt_neg z)
        have h2 := h1.const_mul ((-1 : ℂ) ^ a * (j.descFactorial a : ℂ))
        have hfun : (fun w : ℂ => (-1 : ℂ) ^ a * ((j.descFactorial a : ℂ) * (-w) ^ (j - a))) =
            fun y : ℂ => (-1 : ℂ) ^ a * (j.descFactorial a : ℂ) * (-y) ^ (j - a) := by
          funext y; ring
        rw [hfun]
        refine h2.congr_deriv ?_
        rw [Nat.descFactorial_succ, show j - a - 1 = j - (a + 1) by omega, pow_succ]
        push_cast [haj.le]
        ring
      exact hd.deriv

private lemma iteratedDeriv_exp_neg_mul (u : ℝ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w : ℂ => Complex.exp (-w * (u : ℂ))) z =
      (-(u : ℂ)) ^ k * Complex.exp (-z * (u : ℂ)) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, show (iteratedDeriv k (fun w : ℂ => Complex.exp (-w * (u : ℂ)))) =
      fun w => (-(u : ℂ)) ^ k * Complex.exp (-w * (u : ℂ)) from funext ih]
    have hd : HasDerivAt (fun w : ℂ => (-(u : ℂ)) ^ k * Complex.exp (-w * (u : ℂ)))
        ((-(u : ℂ)) ^ (k + 1) * Complex.exp (-z * (u : ℂ))) z := by
      have h1 : HasDerivAt (fun w : ℂ => -w * (u : ℂ)) (-(u : ℂ)) z :=
        ((hasDerivAt_neg z).mul_const (u : ℂ)).congr_deriv (by ring)
      exact ((h1.cexp).const_mul ((-(u : ℂ)) ^ k)).congr_deriv (by rw [pow_succ]; ring)
    exact hd.deriv

private lemma iterate_deriv_C_mul_X_pow (c : ℂ) (p a : ℕ) :
    Polynomial.derivative^[a] (Polynomial.C c * Polynomial.X ^ p) =
      Polynomial.C (c * (p.descFactorial a : ℂ)) * Polynomial.X ^ (p - a) := by
  induction a generalizing c p with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih, Polynomial.derivative_C_mul_X_pow]
    cases hpa : p - a with
    | zero =>
      have hpa' : p ≤ a := Nat.sub_eq_zero_iff_le.mp hpa
      have hd0 : p.descFactorial (a + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hd0]
      simp
    | succ d =>
      have halt : a < p := by omega
      rw [Nat.descFactorial_succ, show p - (a + 1) = d by omega, Nat.add_sub_cancel]
      congr 2
      push_cast [hpa, halt.le]
      ring

private lemma iterate_deriv_neg_X_pow_eval (p a : ℕ) (u : ℂ) :
    (Polynomial.derivative^[a] ((-Polynomial.X : Polynomial ℂ) ^ p)).eval u =
      (-1 : ℂ) ^ a * ((p.descFactorial a : ℂ) * (-u) ^ (p - a)) := by
  rw [neg_X_pow, iterate_deriv_C_mul_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  by_cases hap : a ≤ p
  · have hneg : (-u) ^ (p - a) = (-1 : ℂ) ^ (p - a) * u ^ (p - a) := by
      rw [← neg_one_mul u, mul_pow]
    rw [hneg]
    calc (-1 : ℂ) ^ p * (p.descFactorial a : ℂ) * u ^ (p - a)
        = (-1 : ℂ) ^ (a + (p - a)) * (p.descFactorial a : ℂ) * u ^ (p - a) := by
          rw [Nat.add_sub_cancel' hap]
      _ = (-1 : ℂ) ^ a * ((p.descFactorial a : ℂ) * ((-1 : ℂ) ^ (p - a) * u ^ (p - a))) := by
          rw [pow_add]; ring
  · have hd0 : p.descFactorial a = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [hd0]

private lemma Q_jet_polePoly_eval (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (ω : ℕ → ℝ) (m j : ℕ) (u : ℝ) :
    (Q_jet (polePoly pp ord m) (ω m : ℂ) j).eval (u : ℂ) * Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
      ∑ s ∈ Finset.Icc 1 (ord m),
        2 * (Real.pi : ℂ) * I * pp m s *
          (iteratedDeriv (s - 1) (fun z : ℂ => (-z) ^ j * Complex.exp (-z * (u : ℂ))) (ω m : ℂ) /
            ((s - 1).factorial : ℂ)) := by
  have heval_Q : ∀ a : ℕ, (Polynomial.derivative^[a] (polePoly pp ord m)).eval (u : ℂ) =
      (2 * (Real.pi : ℂ) * I) * ∑ s ∈ Finset.Icc 1 (ord m),
        (pp m s / ((s - 1).factorial : ℂ)) * (-1 : ℂ) ^ a *
          (((s - 1).descFactorial a : ℂ) * (-(u : ℂ)) ^ (s - 1 - a)) := by
    intro a
    have hsmul : ∀ (k : ℕ) (c : ℂ) (f : Polynomial ℂ),
        Polynomial.derivative^[k] (c • f) = c • Polynomial.derivative^[k] f := by
      intro k c f
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihk,
          Polynomial.derivative_smul]
    have hsum_d : ∀ (k : ℕ) (S : Finset ℕ) (g : ℕ → Polynomial ℂ),
        Polynomial.derivative^[k] (∑ i ∈ S, g i) = ∑ i ∈ S, Polynomial.derivative^[k] (g i) := by
      intro k S g
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [Function.iterate_succ_apply', ihk, Polynomial.derivative_sum]
        exact Finset.sum_congr rfl fun i _ => (Function.iterate_succ_apply' _ k (g i)).symm
    have hC_d : ∀ (k : ℕ) (c : ℂ) (f : Polynomial ℂ),
        Polynomial.derivative^[k] (Polynomial.C c * f) = Polynomial.C c * Polynomial.derivative^[k] f := by
      intro k c f
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihk, Polynomial.derivative_C_mul]
    unfold polePoly
    rw [hsmul, hsum_d]
    change Polynomial.evalRingHom (u : ℂ) _ = _
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_smul, smul_eq_mul,
      ← Polynomial.coe_evalRingHom, map_sum, Polynomial.coe_evalRingHom]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hC_d, Polynomial.eval_mul, Polynomial.eval_C, iterate_deriv_neg_X_pow_eval]
    ring
  rw [Q_jet]
  change (Polynomial.evalRingHom (u : ℂ) _) * _ = _
  simp only [map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C]
  rw [Finset.sum_mul]
  trans ∑ a ∈ Finset.range (j + 1), ∑ s ∈ Finset.Icc 1 (ord m),
      ((Nat.choose j a : ℂ) * (-(ω m : ℂ)) ^ (j - a)) *
        ((2 * (Real.pi : ℂ) * I * pp m s / ((s - 1).factorial : ℂ)) * (-1 : ℂ) ^ a *
          (((s - 1).descFactorial a : ℂ) * (-(u : ℂ)) ^ (s - 1 - a)) *
          Complex.exp (-(ω m : ℂ) * (u : ℂ)))
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [heval_Q a, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => by ring
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
  have hit := iteratedDeriv_fun_mul (n := s - 1) (x := (ω m : ℂ))
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => (-z) ^ j) (ω m : ℂ)).contDiffAt
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z * (u : ℂ))) (ω m : ℂ)).contDiffAt
  change iteratedDeriv (s - 1) (fun z : ℂ => (-z) ^ j * Complex.exp (-z * (u : ℂ))) (ω m : ℂ) = _ at hit
  rw [hit, Finset.sum_div, Finset.mul_sum]
  have hterm_eq : ∀ a ∈ Finset.range (j + 1),
      ((Nat.choose j a : ℂ) * (-(ω m : ℂ)) ^ (j - a)) *
        ((2 * (Real.pi : ℂ) * I * pp m s / ((s - 1).factorial : ℂ)) * (-1 : ℂ) ^ a *
          (((s - 1).descFactorial a : ℂ) * (-(u : ℂ)) ^ (s - 1 - a)) *
          Complex.exp (-(ω m : ℂ) * (u : ℂ))) =
      if a < s then
        2 * (Real.pi : ℂ) * I * pp m s *
          (((Nat.choose (s - 1) a : ℂ) * iteratedDeriv a (fun z : ℂ => (-z) ^ j) (ω m : ℂ) *
            iteratedDeriv (s - 1 - a) (fun z : ℂ => Complex.exp (-z * (u : ℂ))) (ω m : ℂ)) /
            ((s - 1).factorial : ℂ))
      else 0 := by
    intro a _
    by_cases has : a < s
    · rw [ite_eq_left_iff.mpr (fun h => absurd has h), iteratedDeriv_neg_pow j a,
        iteratedDeriv_exp_neg_mul]
      have hchoose : ((s - 1).choose a : ℂ) / ((s - 1).factorial : ℂ) * (j.descFactorial a : ℂ) =
          ((s - 1).descFactorial a : ℂ) / ((s - 1).factorial : ℂ) * (j.choose a : ℂ) := by
        have hnat : (s - 1).choose a * j.descFactorial a = (s - 1).descFactorial a * j.choose a := by
          rw [Nat.descFactorial_eq_factorial_mul_choose j a,
            Nat.descFactorial_eq_factorial_mul_choose (s - 1) a]
          ring
        have hc : ((s - 1).choose a : ℂ) * (j.descFactorial a : ℂ) =
            ((s - 1).descFactorial a : ℂ) * (j.choose a : ℂ) := by exact_mod_cast hnat
        calc ((s - 1).choose a : ℂ) / ((s - 1).factorial : ℂ) * (j.descFactorial a : ℂ)
            = (((s - 1).choose a : ℂ) * (j.descFactorial a : ℂ)) / ((s - 1).factorial : ℂ) := by ring
          _ = (((s - 1).descFactorial a : ℂ) * (j.choose a : ℂ)) / ((s - 1).factorial : ℂ) := by rw [hc]
          _ = ((s - 1).descFactorial a : ℂ) / ((s - 1).factorial : ℂ) * (j.choose a : ℂ) := by ring
      calc ((Nat.choose j a : ℂ) * (-(ω m : ℂ)) ^ (j - a)) *
            ((2 * (Real.pi : ℂ) * I * pp m s / ((s - 1).factorial : ℂ)) * (-1 : ℂ) ^ a *
              (((s - 1).descFactorial a : ℂ) * (-(u : ℂ)) ^ (s - 1 - a)) *
              Complex.exp (-(ω m : ℂ) * (u : ℂ)))
          = 2 * (Real.pi : ℂ) * I * pp m s *
              (((s - 1).descFactorial a : ℂ) / ((s - 1).factorial : ℂ) * (j.choose a : ℂ)) *
              ((-1 : ℂ) ^ a * (-(ω m : ℂ)) ^ (j - a) * (-(u : ℂ)) ^ (s - 1 - a) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ))) := by ring
        _ = 2 * (Real.pi : ℂ) * I * pp m s *
              (((Nat.choose (s - 1) a : ℂ) / ((s - 1).factorial : ℂ) * (j.descFactorial a : ℂ))) *
              ((-1 : ℂ) ^ a * (-(ω m : ℂ)) ^ (j - a) * (-(u : ℂ)) ^ (s - 1 - a) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ))) := by rw [hchoose]
        _ = _ := by ring
    · have hdesc : (s - 1).descFactorial a = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [has, hdesc]
  rw [Finset.sum_congr rfl hterm_eq]
  rw [show s - 1 + 1 = s by omega]
  have hsplit_a : ∑ a ∈ Finset.range (j + 1), (if a < s then
        2 * (Real.pi : ℂ) * I * pp m s *
          (((Nat.choose (s - 1) a : ℂ) * iteratedDeriv a (fun z : ℂ => (-z) ^ j) (ω m : ℂ) *
            iteratedDeriv (s - 1 - a) (fun z : ℂ => Complex.exp (-z * (u : ℂ))) (ω m : ℂ)) /
            ((s - 1).factorial : ℂ))
      else 0) =
      ∑ a ∈ Finset.range s,
        2 * (Real.pi : ℂ) * I * pp m s *
          (((Nat.choose (s - 1) a : ℂ) * iteratedDeriv a (fun z : ℂ => (-z) ^ j) (ω m : ℂ) *
            iteratedDeriv (s - 1 - a) (fun z : ℂ => Complex.exp (-z * (u : ℂ))) (ω m : ℂ)) /
            ((s - 1).factorial : ℂ)) := by
    rw [← Finset.sum_filter]
    have hfilt : (Finset.range (j + 1)).filter (· < s) = Finset.range (min (j + 1) s) := by
      ext a; simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
    rw [hfilt]
    refine Finset.sum_subset (Finset.range_mono (min_le_right _ _)) fun a ha hnot => ?_
    rw [Finset.mem_range] at ha
    rw [Finset.mem_range, lt_min_iff] at hnot
    have hja : j < a := by omega
    have hdesc0 : j.descFactorial a = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hja
    rw [iteratedDeriv_neg_pow j a]
    simp [hdesc0]
  exact hsplit_a

private def cutRH {φ ω ord pp} (_h : HigherOrderBorelData φ 0 ω ord pp) (n : ℕ) : ℝ :=
  (ω n + ω (n + 1)) / 2

private lemma cutRH_pos {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) (n : ℕ) :
    0 < cutRH h n := by
  have h1 : 0 < ω n := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le n))
  have h2 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
  dsimp only [cutRH]; linarith

private lemma ω_lt_cutRH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) {m n : ℕ}
    (hm : m ≤ n) : ω m < cutRH h n := by
  have h1 : ω m ≤ ω n := h.ω_mono.monotone hm
  have h2 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
  dsimp only [cutRH]; linarith

private lemma cutRH_lt_ω {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) {m n : ℕ}
    (hm : n + 1 ≤ m) : cutRH h n < ω m := by
  have h1 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
  have h2 : ω (n + 1) ≤ ω m := h.ω_mono.monotone hm
  dsimp only [cutRH]; linarith

private lemma closedTri_subset_cutOpenH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp)
    (n : ℕ) :
    closedTri (cutRH h n) (Real.tan h.θ) ⊆
      borelWedge h.α₀ (ε₀H h) ∩ {z : ℂ | z.re < ω (n + 1)} := by
  intro z hz
  have hlt_next : z.re < ω (n + 1) := lt_of_le_of_lt hz.2.1 (cutRH_lt_ω h le_rfl)
  refine ⟨?_, hlt_next⟩
  rcases eq_or_lt_of_le hz.1 with hz0 | hzpos
  · left
    have him0 : z.im = 0 := by
      have habs : |z.im| ≤ 0 := by simpa [← hz0] using hz.2.2
      exact abs_nonpos_iff.mp habs
    have hz_eq : z = 0 := Complex.ext hz0.symm him0
    simpa [hz_eq, Metric.mem_ball, dist_zero_right] using ε₀H_pos h
  · right
    refine ⟨hzpos, lt_of_le_of_lt hz.2.2 ?_⟩
    exact mul_lt_mul_of_pos_right (tan_lt_tanH h) hzpos

private lemma continuousAt_iff_tendsto_nhdsWithin_ne {f : ℂ → ℂ} {z₀ L : ℂ}
    (hf : Tendsto f (𝓝[≠] z₀) (𝓝 L)) (hf0 : f z₀ = L) :
    ContinuousAt f z₀ :=
  continuousAt_iff_punctured_nhds.mpr (by simpa [hf0] using hf)

private lemma poleSub_analyticOn_cutOpenH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp)
    (n : ℕ) :
    let Sn (z : ℂ) : ℂ := ∑ m ∈ Finset.range (n + 1),
      ∑ s ∈ Finset.Icc 1 (ord m), pp m s / (z - (ω m : ℂ)) ^ s
    let Pset : Set ℂ := (fun m : ℕ => (ω m : ℂ)) '' (Finset.range (n + 1) : Set ℕ)
    let ψn (z : ℂ) : ℂ :=
      by classical exact if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => φ w - Sn w) else φ z - Sn z
    AnalyticOnNhd ℂ ψn (borelWedge h.α₀ (ε₀H h) ∩ {z : ℂ | z.re < ω (n + 1)}) := by
  classical
  intro Sn Pset ψn
  let Un : Set ℂ := borelWedge h.α₀ (ε₀H h) ∩ {z : ℂ | z.re < ω (n + 1)}
  have hUn_open : IsOpen Un :=
    (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im)
        (continuous_const.mul Complex.continuous_re)))).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hP_fin : Pset.Finite := (Finset.finite_toSet (Finset.range (n + 1))).image _
  have hP_closed : IsClosed Pset := hP_fin.isClosed
  have hUn_sub : Un \ Pset ⊆ rotatedPuncturedWedge 0 h.α₀ h.ε ω := by
    rw [rotatedPuncturedWedge_zero_eq]
    intro w ⟨hwU, hwP⟩
    refine ⟨?_, ?_⟩
    · rcases hwU.1 with hw_ball | hw_sec
      · left; exact Metric.ball_subset_ball (ε₀H_le_ε h) hw_ball
      · right; exact hw_sec
    · rintro ⟨m, rfl⟩
      have hm_lt : ω m < ω (n + 1) := by simpa using hwU.2
      have hm_idx : m < n + 1 := h.ω_mono.lt_iff_lt.mp hm_lt
      exact hwP ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr hm_idx), rfl⟩
  have hSn_an : ∀ z ∈ Un \ Pset, AnalyticAt ℂ Sn z := by
    intro z hz
    refine Finset.analyticAt_fun_sum _ fun m hm => Finset.analyticAt_fun_sum _ fun s _ => ?_
    refine analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow s) ?_
    intro h0
    apply hz.2
    have hzsub : z - (ω m : ℂ) = 0 := eq_zero_of_pow_eq_zero h0
    exact ⟨m, Finset.mem_coe.mpr hm, (sub_eq_zero.mp hzsub).symm⟩
  intro z hzU
  by_cases hzP : z ∈ Pset
  · obtain ⟨k, hk_mem, rfl⟩ := hzP
    have hk : k < n + 1 := Finset.mem_range.mp hk_mem
    let Qk : Set ℂ := Pset \ {(ω k : ℂ)}
    have hQk_closed : IsClosed Qk := (hP_fin.subset Set.sdiff_subset).isClosed
    let Vk : Set ℂ := Un \ Qk
    have hVk_open : IsOpen Vk := hUn_open.sdiff hQk_closed
    have hwk_Vk : (ω k : ℂ) ∈ Vk := ⟨hzU, fun hmem => hmem.2 rfl⟩
    have hmem_punc : Vk \ {(ω k : ℂ)} ∈ 𝓝[≠] (ω k : ℂ) := by
      rw [Set.sdiff_eq, inter_comm]
      exact inter_mem_nhdsWithin _ (hVk_open.mem_nhds hwk_Vk)
    have hsub_open : Vk \ {(ω k : ℂ)} ⊆ Un \ Pset := by
      intro ζ hζ
      exact ⟨hζ.1.1, fun hP => hζ.2 (by
        by_contra hne
        exact hζ.1.2 ⟨hP, hne⟩)⟩
    have hψ_diff_punc : ∀ᶠ w in 𝓝[≠] (ω k : ℂ), DifferentiableAt ℂ ψn w := by
      filter_upwards [hmem_punc] with w hw
      have hdiff_sub : DifferentiableAt ℂ (fun ζ => φ ζ - Sn ζ) w :=
        ((h.analyticOn w (hUn_sub (hsub_open hw))).sub (hSn_an w (hsub_open hw))).differentiableAt
      have heq : ψn =ᶠ[𝓝 w] fun ζ => φ ζ - Sn ζ := by
        filter_upwards [(hUn_open.sdiff hP_closed).mem_nhds (hsub_open hw)] with ζ hζ
        dsimp only [ψn]
        exact ite_eq_right_iff.mpr fun hmem => absurd hmem hζ.2
      exact hdiff_sub.congr_of_eventuallyEq heq
    let PP_k (w : ℂ) : ℂ := ∑ s ∈ Finset.Icc 1 (ord k), pp k s / (w - (ω k : ℂ)) ^ s
    let Sn_rest (w : ℂ) : ℂ := ∑ m ∈ (Finset.range (n + 1)).erase k,
      ∑ s ∈ Finset.Icc 1 (ord m), pp m s / (w - (ω m : ℂ)) ^ s
    have hSn_split : ∀ w : ℂ, φ w - Sn w = (φ w - PP_k w) - Sn_rest w := by
      intro w
      dsimp only [Sn, PP_k, Sn_rest]
      rw [← Finset.add_sum_erase (Finset.range (n + 1))
        (fun m => ∑ s ∈ Finset.Icc 1 (ord m), pp m s / (w - (ω m : ℂ)) ^ s) hk_mem]
      ring
    have hrest_an : AnalyticAt ℂ Sn_rest (ω k : ℂ) := by
      refine Finset.analyticAt_fun_sum _ fun m hm => Finset.analyticAt_fun_sum _ fun s _ => ?_
      have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
      refine analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow s) ?_
      intro h0
      exact h.ω_mono.injective.ne hmk.symm (by exact_mod_cast sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0))
    obtain ⟨L, hL⟩ := h.pole_principalPart k
    have hL' : Tendsto (fun w => φ w - PP_k w) (𝓝[≠] (ω k : ℂ)) (𝓝 L) := by
      simpa [PP_k] using hL
    have h_tend : Tendsto (fun w => φ w - Sn w) (𝓝[≠] (ω k : ℂ)) (𝓝 (L - Sn_rest (ω k : ℂ))) := by
      simp_rw [hSn_split]
      exact hL'.sub hrest_an.continuousAt.continuousWithinAt.tendsto
    have hlim_eq : Filter.limUnder (𝓝[≠] (ω k : ℂ)) (fun w => φ w - Sn w) = L - Sn_rest (ω k : ℂ) :=
      h_tend.limUnder_eq
    have hψ_tend : Tendsto ψn (𝓝[≠] (ω k : ℂ)) (𝓝 (L - Sn_rest (ω k : ℂ))) := by
      refine h_tend.congr' ?_
      filter_upwards [hmem_punc] with w hw
      have hw_notP : w ∉ Pset := (hsub_open hw).2
      dsimp only [ψn]
      rw [ite_eq_right_iff.mpr fun hmem => absurd hmem hw_notP]
    have hψ_at : ψn (ω k : ℂ) = L - Sn_rest (ω k : ℂ) := by
      have hmemP : (ω k : ℂ) ∈ Pset := ⟨k, Finset.mem_coe.mpr hk_mem, rfl⟩
      dsimp only [ψn]
      rw [ite_eq_left_iff.mpr fun hnot => absurd hmemP hnot, hlim_eq]
    have hψ_cont : ContinuousAt ψn (ω k : ℂ) :=
      continuousAt_iff_tendsto_nhdsWithin_ne hψ_tend hψ_at
    exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hψ_diff_punc hψ_cont
  · have hopen : IsOpen (Un \ Pset) := hUn_open.sdiff hP_closed
    have hmem : Un \ Pset ∈ 𝓝 z := hopen.mem_nhds ⟨hzU, hzP⟩
    have hdiff_an : AnalyticAt ℂ (fun w => φ w - Sn w) z :=
      (h.analyticOn z (hUn_sub ⟨hzU, hzP⟩)).sub (hSn_an z ⟨hzU, hzP⟩)
    have heq : ψn =ᶠ[𝓝 z] fun w => φ w - Sn w := by
      filter_upwards [hmem] with w hw
      dsimp only [ψn]
      exact ite_eq_right_iff.mpr fun hmemP => absurd hmemP hw.2
    exact hdiff_an.congr heq.symm

private lemma triBd_avoid_polesH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) (n : ℕ) :
    (∀ x : ℝ, ∀ m : ℕ, (x : ℂ) * (1 - I * (Real.tan h.θ : ℂ)) ≠ (ω m : ℂ)) ∧
    (∀ x : ℝ, ∀ m : ℕ, (x : ℂ) * (1 + I * (Real.tan h.θ : ℂ)) ≠ (ω m : ℂ)) ∧
    (∀ y : ℝ, ∀ m : ℕ, (cutRH h n : ℂ) + (y : ℂ) * I ≠ (ω m : ℂ)) := by
  have hm_pos : 0 < Real.tan h.θ := tan_pos_of_memH h.hθ_pos (h.hθ_lt.trans h.hα₀_lt)
  refine ⟨?_, ?_, ?_⟩
  · intro x m h0
    have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, zero_sub, add_zero] at him
    have hx0 : x = 0 := by
      have : x * (-Real.tan h.θ) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right (neg_ne_zero.mpr hm_pos.ne')
    subst hx0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
    have hωm : 0 < ω m := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
    linarith
  · intro x m h0
    have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add] at him
    have hx0 : x = 0 := by
      have : x * Real.tan h.θ = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hm_pos.ne'
    subst hx0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
    have hωm : 0 < ω m := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
    linarith
  · intro y m h0
    have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, Complex.ofReal_im] at hre
    have hre' : cutRH h n = ω m := by simpa using hre
    rcases le_or_gt m n with hmn | hnm
    · exact (ω_lt_cutRH h hmn).ne hre'.symm
    · exact (cutRH_lt_ω h hnm).ne hre'

private lemma triIntegral_φ_kernelH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp)
    (n j : ℕ) (u : ℝ) :
    triIntegral (fun z => (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z) (cutRH h n) (Real.tan h.θ) =
      ∑ m ∈ Finset.range (n + 1),
        (Q_jet (polePoly pp ord m) (ω m : ℂ) j).eval (u : ℂ) * Complex.exp (-(ω m : ℂ) * (u : ℂ)) := by
  classical
  let R : ℝ := cutRH h n
  let mθ : ℝ := Real.tan h.θ
  have hR_pos : 0 < R := cutRH_pos h n
  have hm_pos : 0 < mθ := tan_pos_of_memH h.hθ_pos (h.hθ_lt.trans h.hα₀_lt)
  let Sn (z : ℂ) : ℂ := ∑ m ∈ Finset.range (n + 1),
    ∑ s ∈ Finset.Icc 1 (ord m), pp m s / (z - (ω m : ℂ)) ^ s
  let Pset : Set ℂ := (fun m : ℕ => (ω m : ℂ)) '' (Finset.range (n + 1) : Set ℕ)
  let ψn (z : ℂ) : ℂ :=
    if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => φ w - Sn w) else φ z - Sn z
  let Un : Set ℂ := borelWedge h.α₀ (ε₀H h) ∩ {z : ℂ | z.re < ω (n + 1)}
  have hUn_open : IsOpen Un :=
    (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im)
        (continuous_const.mul Complex.continuous_re)))).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hψ_an : AnalyticOnNhd ℂ ψn Un := poleSub_analyticOn_cutOpenH h n
  let Fψ (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * ψn z
  have hFψ_an : AnalyticOnNhd ℂ Fψ Un :=
    ((analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)).mul
      hψ_an
  have htri_ψ : triIntegral Fψ R mθ = 0 :=
    triIntegral_eq_zero_of_analyticOn hR_pos.le hm_pos.le hUn_open
      (closedTri_subset_cutOpenH h n) hFψ_an
  have h_avoid := triBd_avoid_polesH h n
  let termMS (m s : ℕ) (z : ℂ) : ℂ :=
    (-z) ^ j * Complex.exp (-z * (u : ℂ)) * (pp m s / (z - (ω m : ℂ)) ^ s)
  let termM (m : ℕ) (z : ℂ) : ℂ := ∑ s ∈ Finset.Icc 1 (ord m), termMS m s z
  have htermMS_int : ∀ m ∈ Finset.range (n + 1), ∀ s ∈ Finset.Icc 1 (ord m),
      TriBdIntegrableH (termMS m s) R mθ := by
    intro m _ s _
    refine triBdIntegrable_of_continuousOnH hR_pos.le hm_pos.le
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div ((by fun_prop : Continuous fun x : ℝ =>
          ((x : ℂ) * (1 - I * (mθ : ℂ)) - (ω m : ℂ)) ^ s)) fun x h0 =>
          h_avoid.1 x m (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)))))
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div ((by fun_prop : Continuous fun y : ℝ =>
          ((R : ℂ) + (y : ℂ) * I - (ω m : ℂ)) ^ s)) fun y h0 =>
          h_avoid.2.2 y m (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)))))
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div ((by fun_prop : Continuous fun x : ℝ =>
          ((x : ℂ) * (1 + I * (mθ : ℂ)) - (ω m : ℂ)) ^ s)) fun x h0 =>
          h_avoid.2.1 x m (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)))))
  have htermM_int : ∀ m ∈ Finset.range (n + 1), TriBdIntegrableH (termM m) R mθ := by
    intro m hm
    refine ⟨?_, ?_, ?_⟩
    · have heq : (fun x : ℝ => (1 - I * (mθ : ℂ)) *
          ∑ s ∈ Finset.Icc 1 (ord m), termMS m s ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
          ∑ s ∈ Finset.Icc 1 (ord m), fun x : ℝ =>
            (1 - I * (mθ : ℂ)) * termMS m s ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun s hs => (htermMS_int m hm s hs).1
    · have heq : (fun y : ℝ => ∑ s ∈ Finset.Icc 1 (ord m), termMS m s ((R : ℂ) + (y : ℂ) * I)) =
          ∑ s ∈ Finset.Icc 1 (ord m), fun y : ℝ => termMS m s ((R : ℂ) + (y : ℂ) * I) := by
        funext y; rw [Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun s hs => (htermMS_int m hm s hs).2.1
    · have heq : (fun x : ℝ => (1 + I * (mθ : ℂ)) *
          ∑ s ∈ Finset.Icc 1 (ord m), termMS m s ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
          ∑ s ∈ Finset.Icc 1 (ord m), fun x : ℝ =>
            (1 + I * (mθ : ℂ)) * termMS m s ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun s hs => (htermMS_int m hm s hs).2.2
  have h_pole_term : ∀ m ∈ Finset.range (n + 1),
      triIntegral (termM m) R mθ =
        (Q_jet (polePoly pp ord m) (ω m : ℂ) j).eval (u : ℂ) * Complex.exp (-(ω m : ℂ) * (u : ℂ)) := by
    intro m hm
    rw [Q_jet_polePoly_eval pp ord ω m j u]
    dsimp only [termM]
    rw [triIntegral_sumH _ _ R mθ fun s hs => htermMS_int m hm s hs]
    refine Finset.sum_congr rfl fun s hs => ?_
    have h_eq : termMS m s = fun z : ℂ =>
        pp m s * (((-z) ^ j * Complex.exp (-z * (u : ℂ))) / (z - (ω m : ℂ)) ^ s) := by
      funext z; dsimp only [termMS]; ring
    rw [h_eq, triIntegral_const_mulH]
    have hFn : AnalyticOnNhd ℂ (fun z : ℂ => (-z) ^ j * Complex.exp (-z * (u : ℂ))) univ :=
      (analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)
    rw [triIntegral_mul_inv_sub_pow hFn
      (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m)))
      (ω_lt_cutRH h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
      hm_pos (Finset.mem_Icc.mp hs).1]
    ring
  have h_Fψ_int : TriBdIntegrableH Fψ R mθ :=
    triBdIntegrable_of_continuousOnH hR_pos.le hm_pos.le
      (hFψ_an.continuousOn.comp (by fun_prop) fun x hx => by
        refine closedTri_subset_cutOpenH h n ?_
        have heq : (x : ℂ) * (1 - I * (mθ : ℂ)) = (x : ℂ) * (1 + I * ((-mθ : ℝ) : ℂ)) := by
          push_cast; ring
        rw [heq]
        exact mem_closedTri_mul_one_addH hR_pos.le hm_pos.le hx ⟨le_rfl, by linarith⟩)
      (hFψ_an.continuousOn.comp (by fun_prop) fun y hy => by
        refine closedTri_subset_cutOpenH h n ?_
        refine ⟨by simp [hR_pos.le], by simp [R], ?_⟩
        rw [show -mθ * R = -(mθ * R) by ring] at hy
        simpa [R, mθ] using abs_le.mpr hy)
      (hFψ_an.continuousOn.comp (by fun_prop) fun x hx =>
        closedTri_subset_cutOpenH h n (mem_closedTri_mul_one_addH hR_pos.le hm_pos.le hx ⟨by linarith, le_rfl⟩))
  have h_sum_int : TriBdIntegrableH (fun z => ∑ m ∈ Finset.range (n + 1), termM m z) R mθ := by
    refine ⟨?_, ?_, ?_⟩
    · have heq : (fun x : ℝ => (1 - I * (mθ : ℂ)) *
          ∑ m ∈ Finset.range (n + 1), termM m ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
          ∑ m ∈ Finset.range (n + 1), fun x : ℝ =>
            (1 - I * (mθ : ℂ)) * termM m ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).1
    · have heq : (fun y : ℝ => ∑ m ∈ Finset.range (n + 1), termM m ((R : ℂ) + (y : ℂ) * I)) =
          ∑ m ∈ Finset.range (n + 1), fun y : ℝ => termM m ((R : ℂ) + (y : ℂ) * I) := by
        funext y; rw [Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).2.1
    · have heq : (fun x : ℝ => (1 + I * (mθ : ℂ)) *
          ∑ m ∈ Finset.range (n + 1), termM m ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
          ∑ m ∈ Finset.range (n + 1), fun x : ℝ =>
            (1 + I * (mθ : ℂ)) * termM m ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).2.2
  have h_pt_eq : ∀ z : ℂ, z ∉ Pset →
      (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z =
        Fψ z + ∑ m ∈ Finset.range (n + 1), termM m z := by
    intro z hz
    dsimp only [Fψ, ψn, termM, termMS, Sn]
    rw [ite_eq_right_iff.mpr (fun hmem => absurd hmem hz)]
    simp only [mul_sub, Finset.mul_sum]
    ring
  have h_not_Pset_minus : ∀ x : ℝ, (x : ℂ) * (1 - I * (mθ : ℂ)) ∉ Pset := by
    rintro x ⟨m, _, hm_eq⟩; exact h_avoid.1 x m hm_eq.symm
  have h_not_Pset_plus : ∀ x : ℝ, (x : ℂ) * (1 + I * (mθ : ℂ)) ∉ Pset := by
    rintro x ⟨m, _, hm_eq⟩; exact h_avoid.2.1 x m hm_eq.symm
  have h_not_Pset_vert : ∀ y : ℝ, (R : ℂ) + (y : ℂ) * I ∉ Pset := by
    rintro y ⟨m, _, hm_eq⟩; exact h_avoid.2.2 y m hm_eq.symm
  have h_main_congr := triIntegral_congrH
    (F := fun z => (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z)
    (G := fun z => Fψ z + ∑ m ∈ Finset.range (n + 1), termM m z)
    hR_pos.le hm_pos.le
    (fun x _ => h_pt_eq ((x : ℂ) * (1 - I * (mθ : ℂ))) (h_not_Pset_minus x))
    (fun y _ => h_pt_eq ((R : ℂ) + (y : ℂ) * I) (h_not_Pset_vert y))
    (fun x _ => h_pt_eq ((x : ℂ) * (1 + I * (mθ : ℂ))) (h_not_Pset_plus x))
  rw [h_main_congr, triIntegral_addH h_Fψ_int h_sum_int, htri_ψ, zero_add,
    triIntegral_sumH _ _ R mθ htermM_int]
  exact Finset.sum_congr rfl h_pole_term

private lemma jet_residual_densityH (φ : ℂ → ℂ) (j : ℕ) (z : ℂ) :
    ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhiH φ)).density z =
      (-z) ^ j * φ z := by
  induction j with
  | zero => simp [aPhiH, BorelExpr.residual]
  | succ j ih =>
    rw [Function.iterate_succ_apply', BorelExpr.residual, Minor.jet]
    dsimp only; rw [ih, pow_succ']; ring

private lemma jet_residual_atomH (φ : ℂ → ℂ) (j : ℕ) :
    ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhiH φ)).atom = 0 := by
  cases j with
  | zero => rfl
  | succ j => rw [Function.iterate_succ_apply', BorelExpr.residual, Minor.jet]

private lemma iteratedDeriv_lateral_eq_laplaceH {φ ω ord pp}
    (_h : HigherOrderBorelData φ 0 ω ord pp)
    {U : Set ℂ} {d : ℂ} (hU : Domain U) (ray : ContainsRay U d)
    (ha : (aPhiH φ).Good U d) (hd : 0 < d.re) (j : ℕ) :
    ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (fun t : ℝ => (aPhiH φ).value d (t : ℂ)) u =
        ∫ v in Ioi (0 : ℝ), d * ((-(d * (v : ℂ))) ^ j *
          Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ))) := by
  let e := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have he_rep := (tendsto_coe_far hd).eventually (e.represents hU ray ha).2
  have he_deriv := (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiH φ) hU ray ha hd j).1
  filter_upwards [he_rep, he_deriv] with u hurep hud
  rw [← hud, hurep, Minor.value, jet_residual_atomH φ j, zero_add]
  unfold complexLaplace
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [damped, Minor.pull, jet_residual_densityH φ j]
  have hexp : -((u : ℂ) * d) * (v : ℂ) = -(d * (v : ℂ)) * (u : ℂ) := by ring
  rw [hexp]; ring

private lemma exp_tail_boundH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp)
    {U : Set ℂ} {d : ℂ} (hd_norm : ‖d‖ = 1) (hd_re : d.re = Real.cos h.θ)
    (hExp : ExpType (Minor.pull d φ))
    (hGood : (aPhiH φ).Good U d)
    (hRay : ContainsRay U d)
    (hDom : Domain U)
    (n j : ℕ) :
    ∃ K : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖∫ v in Ioi (cutRH h n / Real.cos h.θ), d * ((-(d * (v : ℂ))) ^ j *
        Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ)))‖ ≤
        K * Real.exp (-cutRH h n * u) := by
  obtain ⟨Cexp, Dexp, hCexp, hDexp, hexp_bd⟩ := hExp
  have hcos : 0 < Real.cos h.θ := cos_pos_θH h
  let v₀ : ℝ := cutRH h n / Real.cos h.θ
  have hv₀_pos : 0 < v₀ := div_pos (cutRH_pos h n) hcos
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
  have hej_good : (ej.residual (aPhiH φ)).Good _ d := (ej.represents hDom hRay hGood).1
  have hej_int := (tendsto_coe_far (by rw [hd_re]; exact hcos)).eventually (hej_good.integrable hRay)
  refine ⟨K, ?_⟩
  filter_upwards [hej_int, eventually_ge_atTop ((Dexp + 1) / Real.cos h.θ)] with u hu_int hu_ge
  have hu_re : Dexp + 1 ≤ u * Real.cos h.θ := (div_le_iff₀ hcos).mp hu_ge
  let Ftail (v : ℝ) : ℂ := d * ((-(d * (v : ℂ))) ^ j *
    Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ)))
  have h_eq_damped : ∀ v : ℝ,
      damped ((u : ℂ) * d) (Minor.pull d (ej.residual (aPhiH φ)).density) v = Ftail v := by
    intro v
    rw [damped, Minor.pull, jet_residual_densityH φ j]
    have hexp : -((u : ℂ) * d) * (v : ℂ) = -(d * (v : ℂ)) * (u : ℂ) := by ring
    rw [hexp]; dsimp only [Ftail]; ring
  have hF_int_Ioi0 : IntegrableOn Ftail (Ioi 0) :=
    hu_int.congr_fun (fun v _ => h_eq_damped v) measurableSet_Ioi
  have hF_int_tail : IntegrableOn Ftail (Ioi v₀) :=
    hF_int_Ioi0.mono_set (Ioi_subset_Ioi hv₀_pos.le)
  let bnd (v : ℝ) : ℝ :=
    (Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutRH h n * u)) *
      (v ^ j * Real.exp (-(1 / 2 : ℝ) * v))
  have hbnd_int : IntegrableOn bnd (Ioi 0) :=
    h_base_int.const_mul (Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutRH h n * u))
  have h_pt_le : ∀ v ∈ Ioi v₀, ‖Ftail v‖ ≤ bnd v := by
    intro v hv
    change v₀ < v at hv
    have hv0 : 0 ≤ v := le_trans hv₀_pos.le hv.le
    have hF_rew : Ftail v = (-(d * (v : ℂ))) ^ j * Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) *
        Minor.pull d φ v := by dsimp only [Ftail, Minor.pull]; ring
    rw [hF_rew, norm_mul, norm_mul, norm_pow, norm_neg, norm_mul, hd_norm, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
    have hexp_re : (-(d * (v : ℂ)) * (u : ℂ)).re = -(u * Real.cos h.θ) * v := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, hd_re]
      ring
    rw [Complex.norm_exp, hexp_re]
    have hpull := hexp_bd v hv0
    have h_exp_split : Real.exp (-(u * Real.cos h.θ) * v) * (Cexp * Real.exp (Dexp * v)) =
        Cexp * Real.exp (-(u * Real.cos h.θ - Dexp) * v) := by
      rw [mul_left_comm _ Cexp, ← Real.exp_add]; congr 2; ring
    have h_exp_le : Real.exp (-(u * Real.cos h.θ - Dexp) * v) ≤
        Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutRH h n * u) * Real.exp (-(1 / 2 : ℝ) * v) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have h_rem_pos : 0 ≤ u * Real.cos h.θ - Dexp - 1 / 2 := by linarith
      have h_v0_mul : (u * Real.cos h.θ - Dexp - 1 / 2) * v₀ ≤
          (u * Real.cos h.θ - Dexp - 1 / 2) * v :=
        mul_le_mul_of_nonneg_left hv.le h_rem_pos
      have hv₀_eq : Real.cos h.θ * v₀ = cutRH h n := by
        dsimp only [v₀]; field_simp [hcos.ne']
      nlinarith [hv₀_eq]
    calc v ^ j * Real.exp (-(u * Real.cos h.θ) * v) * ‖Minor.pull d φ v‖
        ≤ v ^ j * Real.exp (-(u * Real.cos h.θ) * v) * (Cexp * Real.exp (Dexp * v)) :=
          mul_le_mul_of_nonneg_left hpull (by positivity)
      _ = Cexp * (v ^ j * Real.exp (-(u * Real.cos h.θ - Dexp) * v)) := by
          rw [mul_assoc, h_exp_split]; ring
      _ ≤ Cexp * (v ^ j * (Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutRH h n * u) *
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
    _ = K * Real.exp (-cutRH h n * u) := by
        dsimp only [bnd, K, Ij]; rw [integral_const_mul]; ring

private lemma stokes_jump_expansion_higher_order {φ ω ord pp}
    (h : HigherOrderBorelData φ 0 ω ord pp) (n j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aPhiH φ).value (dMinusH h) (t : ℂ) -
          (aPhiH φ).value (dPlusH h) (t : ℂ)) u -
        ∑ m ∈ Finset.range (n + 1),
          (Q_jet (polePoly pp ord m) (ω m : ℂ) j).eval (u : ℂ) * Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
        C * Real.exp (-cutRH h n * u) := by
  let R : ℝ := cutRH h n
  let mθ : ℝ := Real.tan h.θ
  let v₀ : ℝ := R / Real.cos h.θ
  have hR_pos : 0 < R := cutRH_pos h n
  have hcos : 0 < Real.cos h.θ := cos_pos_θH h
  have hm_pos : 0 < mθ := tan_pos_of_memH h.hθ_pos (h.hθ_lt.trans h.hα₀_lt)
  have hv₀_pos : 0 < v₀ := div_pos hR_pos hcos
  have hreP : 0 < (dPlusH h).re := by rw [dPlusH_re h]; exact hcos
  have hreM : 0 < (dMinusH h).re := by rw [dMinusH_re h]; exact hcos
  let Up := wedgePlusH h.α₀ (ε₀H h)
  let Um := wedgeMinusH h.α₀ (ε₀H h)
  have hUp_dom := wedgePlusH_domain h.α₀ (ε₀H_pos h)
  have hUm_dom := wedgeMinusH_domain h.α₀ (ε₀H_pos h)
  have hrayP := wedgePlusH_containsRay h
  have hrayM := wedgeMinusH_containsRay h
  have hgoodP := aPhiH_good_plus h
  have hgoodM := aPhiH_good_minus h
  have h_sub_deriv : ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (fun t : ℝ => (aPhiH φ).value (dMinusH h) (t : ℂ) -
          (aPhiH φ).value (dPlusH h) (t : ℂ)) u =
        iteratedDeriv j (fun t : ℝ => (aPhiH φ).value (dMinusH h) (t : ℂ)) u -
          iteratedDeriv j (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ)) u :=
    eventually_iteratedDeriv_sub
      (fun i _ => (lateral_eventually_differentiableH h i).2)
      (fun i _ => (lateral_eventually_differentiableH h i).1)
  have h_lapP := iteratedDeriv_lateral_eq_laplaceH h hUp_dom hrayP hgoodP hreP j
  have h_lapM := iteratedDeriv_lateral_eq_laplaceH h hUm_dom hrayM hgoodM hreM j
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have h_intP := (tendsto_coe_far hreP).eventually
    ((ej.represents hUp_dom hrayP hgoodP).1.integrable hrayP)
  have h_intM := (tendsto_coe_far hreM).eventually
    ((ej.represents hUm_dom hrayM hgoodM).1.integrable hrayM)
  have hexp_m : ExpType (Minor.pull (dMinusH h) φ) := by
    simpa [dMinusH, neg_mul] using h.expType_minus
  have hexp_p : ExpType (Minor.pull (dPlusH h) φ) := by
    simpa [dPlusH] using h.expType_plus
  obtain ⟨Km, hKm⟩ := exp_tail_boundH h (norm_dMinusH h) (dMinusH_re h) hexp_m
    hgoodM hrayM hUm_dom n j
  obtain ⟨Kp, hKp⟩ := exp_tail_boundH h (norm_dPlusH h) (dPlusH_re h) hexp_p
    hgoodP hrayP hUp_dom n j
  have h_vert_sub : ∀ y ∈ Icc (-mθ * R) (mθ * R),
      (R : ℂ) + (y : ℂ) * I ∈ rotatedPuncturedWedge 0 h.α₀ h.ε ω := by
    rw [rotatedPuncturedWedge_zero_eq]
    intro y hy
    refine ⟨Or.inr ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
        mul_one, zero_add]
      rw [show -mθ * R = -(mθ * R) by ring] at hy
      have hy_abs : |y| ≤ mθ * R := abs_le.mpr hy
      have htan := tan_lt_tanH h
      exact ⟨hR_pos, lt_of_le_of_lt hy_abs (mul_lt_mul_of_pos_right htan hR_pos)⟩
    · rintro ⟨m, hm_eq⟩
      exact (triBd_avoid_polesH h n).2.2 y m hm_eq.symm
  have hφ_vert_cont : ContinuousOn (fun y : ℝ => φ ((R : ℂ) + (y : ℂ) * I)) (Icc (-mθ * R) (mθ * R)) :=
    h.analyticOn.continuousOn.comp (by fun_prop) h_vert_sub
  obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ_vert_cont
  let Kv : ℝ := (2 * mθ * R) * ((R / Real.cos h.θ) ^ j * max Mφ 0)
  have h_vert_bd : ∀ u : ℝ,
      ‖I * (∫ y : ℝ in (-mθ * R)..(mθ * R),
        (-((R : ℂ) + (y : ℂ) * I)) ^ j * Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ)) *
          φ ((R : ℂ) + (y : ℂ) * I))‖ ≤ Kv * Real.exp (-R * u) := by
    intro u
    rw [norm_mul, Complex.norm_I, one_mul]
    have hpt : ∀ y ∈ uIoc (-mθ * R) (mθ * R),
        ‖(-((R : ℂ) + (y : ℂ) * I)) ^ j * Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ)) *
          φ ((R : ℂ) + (y : ℂ) * I)‖ ≤
          ((R / Real.cos h.θ) ^ j * max Mφ 0) * Real.exp (-R * u) := by
      intro y hy
      rw [uIoc_of_le (by nlinarith : -mθ * R ≤ mθ * R)] at hy
      have hy_cc : y ∈ Icc (-mθ * R) (mθ * R) := ⟨hy.1.le, hy.2⟩
      have hnorm_z : ‖-((R : ℂ) + (y : ℂ) * I)‖ ≤ R / Real.cos h.θ := by
        rw [norm_neg, Complex.norm_def]
        have hy_sq : y ^ 2 ≤ mθ ^ 2 * R ^ 2 := by
          have hy_cc' : y ∈ Icc (-(mθ * R)) (mθ * R) := by simpa [neg_mul] using hy_cc
          have : |y| ≤ mθ * R := abs_le.mpr hy_cc'
          have h1 : y ^ 2 = |y| ^ 2 := (sq_abs y).symm
          rw [h1]
          calc |y| ^ 2 ≤ (mθ * R) ^ 2 := sq_le_sq' (by linarith [abs_nonneg y]) this
            _ = mθ ^ 2 * R ^ 2 := by ring
        have hnsq : Complex.normSq ((R : ℂ) + (y : ℂ) * I) ≤ (R / Real.cos h.θ) ^ 2 := by
          rw [Complex.normSq_apply]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
            mul_one, zero_add]
          have hsec : 1 + mθ ^ 2 = (Real.cos h.θ) ^ (-2 : ℤ) := by
            dsimp only [mθ]
            rw [Real.tan_eq_sin_div_cos, _root_.zpow_neg, zpow_two]
            have hc := hcos.ne'
            have hid := Real.sin_sq_add_cos_sq h.θ
            field_simp [hc]; linarith
          calc R * R + y * y = R ^ 2 + y ^ 2 := by ring
            _ ≤ R ^ 2 + mθ ^ 2 * R ^ 2 := by linarith
            _ = R ^ 2 * (1 + mθ ^ 2) := by ring
            _ = R ^ 2 * (Real.cos h.θ) ^ (-2 : ℤ) := by rw [hsec]
            _ = (R / Real.cos h.θ) ^ 2 := by rw [_root_.zpow_neg, zpow_two, div_pow]; ring
        exact Real.sqrt_le_iff.mpr ⟨div_nonneg hR_pos.le hcos.le, hnsq⟩
      have hexp_norm : ‖Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ))‖ = Real.exp (-R * u) := by
        rw [Complex.norm_exp]; simp [Complex.mul_re]
      have hφ_le : ‖φ ((R : ℂ) + (y : ℂ) * I)‖ ≤ max Mφ 0 :=
        (hMφ y hy_cc).trans (le_max_left _ _)
      rw [norm_mul, norm_mul, norm_pow, hexp_norm]
      calc ‖-((R : ℂ) + (y : ℂ) * I)‖ ^ j * Real.exp (-R * u) * ‖φ ((R : ℂ) + (y : ℂ) * I)‖
          ≤ (R / Real.cos h.θ) ^ j * Real.exp (-R * u) * max Mφ 0 := by gcongr
        _ = ((R / Real.cos h.θ) ^ j * max Mφ 0) * Real.exp (-R * u) := by ring
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    calc ‖∫ y : ℝ in (-mθ * R)..(mθ * R), _‖
        ≤ ((R / Real.cos h.θ) ^ j * max Mφ 0) * Real.exp (-R * u) * |mθ * R - -mθ * R| := hle
      _ = Kv * Real.exp (-R * u) := by
          have habs : |mθ * R - -mθ * R| = 2 * mθ * R := by
            rw [show mθ * R - -mθ * R = 2 * mθ * R by ring, abs_of_pos (by positivity)]
          rw [habs]; dsimp only [Kv]; ring
  refine ⟨Kv + Km + Kp, ?_⟩
  filter_upwards [h_sub_deriv, h_lapP, h_lapM, h_intP, h_intM, hKp, hKm] with
    u hsub hlp hlm hip him hkp_bd hkm_bd
  let Fkern (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z
  have heq_p : ∀ v : ℝ, damped ((u : ℂ) * dPlusH h)
      (Minor.pull (dPlusH h) (ej.residual (aPhiH φ)).density) v =
      dPlusH h * Fkern (dPlusH h * (v : ℂ)) := by
    intro v
    rw [damped, Minor.pull, jet_residual_densityH φ j]
    have hexp : -((u : ℂ) * dPlusH h) * (v : ℂ) = -(dPlusH h * (v : ℂ)) * (u : ℂ) := by ring
    rw [hexp]; dsimp only [Fkern]; ring
  have heq_m : ∀ v : ℝ, damped ((u : ℂ) * dMinusH h)
      (Minor.pull (dMinusH h) (ej.residual (aPhiH φ)).density) v =
      dMinusH h * Fkern (dMinusH h * (v : ℂ)) := by
    intro v
    rw [damped, Minor.pull, jet_residual_densityH φ j]
    have hexp : -((u : ℂ) * dMinusH h) * (v : ℂ) = -(dMinusH h * (v : ℂ)) * (u : ℂ) := by ring
    rw [hexp]; dsimp only [Fkern]; ring
  have hintP_Ioi : IntegrableOn (fun v : ℝ => dPlusH h * Fkern (dPlusH h * (v : ℂ))) (Ioi 0) :=
    hip.congr_fun (fun v _ => heq_p v) measurableSet_Ioi
  have hintM_Ioi : IntegrableOn (fun v : ℝ => dMinusH h * Fkern (dMinusH h * (v : ℂ))) (Ioi 0) :=
    him.congr_fun (fun v _ => heq_m v) measurableSet_Ioi
  have hsplitP : (∫ v in (0 : ℝ)..v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ))) +
      (∫ v in Ioi v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ))) =
      ∫ v in Ioi (0 : ℝ), dPlusH h * Fkern (dPlusH h * (v : ℂ)) :=
    intervalIntegral.integral_interval_add_Ioi hintP_Ioi (hintP_Ioi.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hsplitM : (∫ v in (0 : ℝ)..v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))) +
      (∫ v in Ioi v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))) =
      ∫ v in Ioi (0 : ℝ), dMinusH h * Fkern (dMinusH h * (v : ℂ)) :=
    intervalIntegral.integral_interval_add_Ioi hintM_Ioi (hintM_Ioi.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hcovP : ∫ v in (0 : ℝ)..v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 + I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun v : ℝ => dPlusH h * Fkern (dPlusH h * (v : ℂ))) hcos.ne' (a := 0) (b := R)
    have hmul_eq : (1 + I * (mθ : ℂ)) = ((Real.cos h.θ)⁻¹ : ℂ) * dPlusH h := by
      rw [dPlusH_eq h]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
      have hc : (Real.cos h.θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
      field_simp [hc]
    have harg_eq : ∀ x : ℝ, (x : ℂ) * (1 + I * (mθ : ℂ)) = dPlusH h * ((x / Real.cos h.θ : ℝ) : ℂ) := by
      intro x; rw [hmul_eq]; push_cast; ring
    have heq_int : (fun x : ℝ => (1 + I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos h.θ)⁻¹ • (dPlusH h * Fkern (dPlusH h * ((x / Real.cos h.θ : ℝ) : ℂ))) := by
      funext x; rw [harg_eq x, Complex.real_smul, hmul_eq]; push_cast; ring
    rw [heq_int, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne',
      one_smul, zero_div]
  have hcovM : ∫ v in (0 : ℝ)..v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 - I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun v : ℝ => dMinusH h * Fkern (dMinusH h * (v : ℂ))) hcos.ne' (a := 0) (b := R)
    have hmul_eq : (1 - I * (mθ : ℂ)) = ((Real.cos h.θ)⁻¹ : ℂ) * dMinusH h := by
      rw [dMinusH_eq h]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
      have hc : (Real.cos h.θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
      field_simp [hc]
    have harg_eq : ∀ x : ℝ, (x : ℂ) * (1 - I * (mθ : ℂ)) = dMinusH h * ((x / Real.cos h.θ : ℝ) : ℂ) := by
      intro x; rw [hmul_eq]; push_cast; ring
    have heq_int : (fun x : ℝ => (1 - I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos h.θ)⁻¹ • (dMinusH h * Fkern (dMinusH h * ((x / Real.cos h.θ : ℝ) : ℂ))) := by
      funext x; rw [harg_eq x, Complex.real_smul, hmul_eq]; push_cast; ring
    rw [heq_int, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne',
      one_smul, zero_div]
  have htri := triIntegral_φ_kernelH h n j u
  have h_id : iteratedDeriv j (fun t : ℝ => (aPhiH φ).value (dMinusH h) (t : ℂ) -
        (aPhiH φ).value (dPlusH h) (t : ℂ)) u -
      ∑ m ∈ Finset.range (n + 1),
        (Q_jet (polePoly pp ord m) (ω m : ℂ) j).eval (u : ℂ) * Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
      -(I * (∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I))) +
        (∫ v in Ioi v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))) -
        (∫ v in Ioi v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ))) := by
    rw [hsub, hlm, hlp, ← htri]
    change (∫ v in Ioi (0 : ℝ), dMinusH h * Fkern (dMinusH h * (v : ℂ))) -
        (∫ v in Ioi (0 : ℝ), dPlusH h * Fkern (dPlusH h * (v : ℂ))) -
        triIntegral Fkern R mθ = _
    rw [← hsplitM, ← hsplitP, hcovM, hcovP]
    unfold triIntegral
    ring
  rw [h_id]
  have hv_le := h_vert_bd u
  calc ‖-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I)) +
          (∫ v in Ioi v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))) -
          (∫ v in Ioi v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ)))‖
      ≤ ‖-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I))‖ +
          ‖∫ v in Ioi v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))‖ +
          ‖∫ v in Ioi v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ))‖ := by
        linarith [norm_sub_le (-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I)) +
            (∫ v in Ioi v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))))
            (∫ v in Ioi v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ))),
          norm_add_le (-(I * ∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I)))
            (∫ v in Ioi v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ)))]
    _ ≤ Kv * Real.exp (-R * u) + Km * Real.exp (-R * u) + Kp * Real.exp (-R * u) := by
        rw [norm_neg]
        exact add_le_add (add_le_add hv_le hkm_bd) hkp_bd
    _ = (Kv + Km + Kp) * Real.exp (-cutRH h n * u) := by ring

/-! ### 6. End-to-End Higher-Order Non-Autonomous Stokes–Vandermonde Theorems -/

private lemma evalU_eq_sum_coeffU {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (u : ℂ) :
    evalU P u = ∑ k ∈ Finset.range (maxUDeg P + 1), u ^ k • coeffU k P := by
  ext α
  rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, coeffU_coeff, smul_eq_mul]
  have hdeg : (P.coeff α).natDegree < maxUDeg P + 1 := Nat.lt_succ_of_le (natDegree_le_maxUDeg P α)
  have hsum := Polynomial.as_sum_range_C_mul_X_pow' (P.coeff α) hdeg
  conv_lhs => rw [hsum]
  change Polynomial.evalRingHom u _ = _
  simp only [map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    Polynomial.eval_X]
  refine Finset.sum_congr rfl fun k _ => mul_comm _ _

private lemma pow_mul_exp_neg_le_one (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
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
        rw [pow_succ u K]
        field_simp [hu_pos.ne', hδ_pos.ne']
    _ ≤ u / u := div_le_div_of_nonneg_right hU_ge hu_pos.le
    _ = 1 := div_self hu_pos.ne'

private lemma poly_eval_inv_pow_bdd (q : Polynomial ℂ) {D : ℕ} (hq : q.natDegree ≤ D)
    {u : ℝ} (hu : 1 ≤ u) :
    ‖(u : ℂ)⁻¹ ^ D * q.eval (u : ℂ)‖ ≤ ∑ k ∈ Finset.range (D + 1), ‖q.coeff k‖ := by
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
  rw [← revPoly_eval_inv q hq hu_ne, Polynomial.eval_eq_sum_range' (p := revPoly D q)
    (n := D + 1) (by
      refine Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_)
      rw [revPoly, poly_finset_sum_coeff]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk_le : k ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [Polynomial.coeff_C_mul_X_pow]
      have hne : N ≠ D - k := by omega
      simp [hne])]
  refine (norm_sum_le _ _).trans ?_
  have hterm_le : ∑ k ∈ Finset.range (D + 1), ‖(revPoly D q).coeff k * (u : ℂ)⁻¹ ^ k‖ ≤
      ∑ k ∈ Finset.range (D + 1), ‖(revPoly D q).coeff k‖ := by
    refine Finset.sum_le_sum fun k _ => ?_
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
    exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hu))
  refine hterm_le.trans_eq ?_
  have hcoeff_rev : ∀ k ∈ Finset.range (D + 1), (revPoly D q).coeff k = q.coeff (D - k) := by
    intro k hk
    have hk_le : k ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [revPoly, poly_finset_sum_coeff]
    have ht : ∀ i ∈ Finset.range (D + 1),
        (Polynomial.C (q.coeff i) * Polynomial.X ^ (D - i)).coeff k =
          if i = D - k then q.coeff (D - k) else 0 := by
      intro i hi
      have hi_le : i ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [Polynomial.coeff_C_mul_X_pow]
      by_cases hid : i = D - k
      · subst hid
        have hkk : D - (D - k) = k := by omega
        rw [hkk]
        simp
      · have hne : k ≠ D - i := by omega
        simp [hid, hne]
    rw [Finset.sum_congr rfl ht, Finset.sum_ite_eq']
    simp [Finset.mem_range.mpr (show D - k < D + 1 by omega)]
  have hcongr : ∑ k ∈ Finset.range (D + 1), ‖(revPoly D q).coeff k‖ =
      ∑ k ∈ Finset.range (D + 1), ‖q.coeff (D - k)‖ :=
    Finset.sum_congr rfl fun k hk => by rw [hcoeff_rev k hk]
  rw [hcongr]
  exact Finset.sum_range_reflect (fun k => ‖q.coeff k‖) (D + 1)

private lemma pow_mul_exp_neg_le (K : ℕ) {δ C : ℝ} (hδ : 0 < δ) (_hC : 0 ≤ C) :
    ∀ᶠ u : ℝ in atTop, C * (u ^ K * Real.exp (-δ * u)) ≤ 1 := by
  filter_upwards [pow_mul_exp_neg_le_one K (half_pos hδ), eventually_ge_atTop (max 1 (2 * C / δ))]
    with u hu1 huC
  have hu1_pos : 0 < u := lt_of_lt_of_le zero_lt_one (le_trans (le_max_left _ _) huC)
  have h1 : C * Real.exp (-(δ / 2) * u) ≤ 1 := by
    have hpow1 := Real.pow_div_factorial_le_exp ((δ / 2) * u) (by positivity) 1
    rw [pow_one, Nat.factorial_one, Nat.cast_one, div_one] at hpow1
    have hexp : Real.exp (-(δ / 2) * u) = (Real.exp ((δ / 2) * u))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    have hge : C ≤ (δ / 2) * u := by
      have : 2 * C / δ ≤ u := le_trans (le_max_right _ _) huC
      calc C = (δ / 2) * (2 * C / δ) := by field_simp [hδ.ne']
        _ ≤ (δ / 2) * u := mul_le_mul_of_nonneg_left this (by positivity)
    calc C * Real.exp (-(δ / 2) * u)
        ≤ ((δ / 2) * u) * ((δ / 2) * u)⁻¹ := by
          rw [hexp]
          exact mul_le_mul hge (inv_anti₀ (by positivity) hpow1)
            (inv_nonneg.mpr (Real.exp_pos _).le) (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hexp2 : Real.exp (-δ * u) = Real.exp (-(δ / 2) * u) * Real.exp (-(δ / 2) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  calc C * (u ^ K * Real.exp (-δ * u))
      = (C * Real.exp (-(δ / 2) * u)) * (u ^ K * Real.exp (-(δ / 2) * u)) := by rw [hexp2]; ring
    _ ≤ 1 * 1 := mul_le_mul h1 hu1 (by positivity) zero_le_one
    _ = 1 := mul_one 1

private lemma poly_eval_exp_neg_eventually_le {q : Polynomial ℂ} {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, ‖q.eval (u : ℂ) * Complex.exp (-δ * (u : ℂ))‖ ≤ 1 := by
  let D : ℕ := q.natDegree
  let B : ℝ := ∑ k ∈ Finset.range (D + 1), ‖q.coeff k‖
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => norm_nonneg _
  filter_upwards [pow_mul_exp_neg_le D hδ hB, eventually_ge_atTop (1 : ℝ)] with u huB hu1
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
  have hre : (-(δ : ℂ) * (u : ℂ)).re = -δ * u := by simp [Complex.mul_re]
  rw [norm_mul, Complex.norm_exp, hre]
  have heq : q.eval (u : ℂ) = (u : ℂ) ^ D * ((u : ℂ)⁻¹ ^ D * q.eval (u : ℂ)) := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu_ne, one_pow, one_mul]
  have hq_le : ‖q.eval (u : ℂ)‖ ≤ u ^ D * B := by
    conv_lhs => rw [heq]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
    exact mul_le_mul_of_nonneg_left (poly_eval_inv_pow_bdd q le_rfl hu1) (pow_nonneg hu_pos.le D)
  calc ‖q.eval (u : ℂ)‖ * Real.exp (-δ * u)
      ≤ (u ^ D * B) * Real.exp (-δ * u) := mul_le_mul_of_nonneg_right hq_le (Real.exp_pos _).le
    _ = B * (u ^ D * Real.exp (-δ * u)) := by ring
    _ ≤ 1 := huB

private lemma stokes_sum_eventually_le_one {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp)
    (r n : ℕ) :
    ∀ᶠ u : ℝ in atTop, ∀ j : Fin (r + 1),
      ‖∑ m ∈ Finset.range (n + 1),
        (Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
          Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤ 1 := by
  have hterm : ∀ (j : Fin (r + 1)) (m : ℕ), ∀ᶠ u : ℝ in atTop,
      ‖(Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
        Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
    intro j m
    have hωm : 0 < ω m := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
    have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    let qm := ((n + 1 : ℕ) : ℂ) • Q_jet (polePoly pp ord m) (ω m : ℂ) j.val
    filter_upwards [poly_eval_exp_neg_eventually_le (q := qm) hωm] with u hu
    have hmul : qm.eval (u : ℂ) = ((n + 1 : ℕ) : ℂ) *
        (Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) := by
      simp [qm, Polynomial.eval_smul]
    rw [norm_mul] at hu ⊢
    rw [hmul, norm_mul, Complex.norm_natCast, mul_assoc] at hu
    exact (le_div_iff₀' hn1).mpr hu
  have hall := Filter.eventually_all.mpr fun j : Fin (r + 1) =>
    (Filter.eventually_all_finset (Finset.range (n + 1))).mpr fun m _ => hterm j m
  filter_upwards [hall] with u hu j
  refine (norm_sum_le _ _).trans ?_
  calc ∑ m ∈ Finset.range (n + 1),
        ‖(Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
          Complex.exp (-(ω m : ℂ) * (u : ℂ))‖
      ≤ ∑ _m ∈ Finset.range (n + 1), (1 / ((n + 1 : ℕ) : ℝ)) :=
        Finset.sum_le_sum fun m hm => hu j m hm
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div, mul_inv_cancel₀ (by positivity)]

/-- **Unrotated Higher-Order Non-Autonomous Stokes–Vandermonde Theorem (`θ₀ = 0`, `P ∈ ℂ[u][Y_0,...,Y_r]`)**:
For arbitrary pole orders `ord m ≥ 1`, formal solutions of `formalEvalPoly (formalSeries φ) P = 0` force `P = 0`. -/
theorem higher_order_stokes_vandermonde_no_ade_zero
    {φ : ℂ → ℂ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ 0 ω ord pp)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries φ) P = 0) : P = 0 := by
  classical
  by_contra hP_ne
  have hex : ∃ d : ℕ, ∃ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
      Q.totalDegree = d ∧ Q ≠ 0 ∧ formalEvalPoly (formalSeries φ) Q = 0 :=
    ⟨P.totalDegree, P, rfl, hP_ne, hP⟩
  let Pmin := Classical.choose (Nat.find_spec hex)
  have hPmin_spec := Classical.choose_spec (Nat.find_spec hex)
  have hPmin_deg : Pmin.totalDegree = Nat.find hex := hPmin_spec.1
  have hPmin_ne : Pmin ≠ 0 := hPmin_spec.2.1
  have hPmin_zero : formalEvalPoly (formalSeries φ) Pmin = 0 := hPmin_spec.2.2
  have hPmin_min : ∀ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ),
      Q ≠ 0 → Q.totalDegree < Pmin.totalDegree → ¬ formalEvalPoly (formalSeries φ) Q = 0 := by
    intro Q hQ_ne hQ_deg hQ_zero
    rw [hPmin_deg] at hQ_deg
    exact Nat.find_min hex hQ_deg ⟨Q, rfl, hQ_ne, hQ_zero⟩
  have hPmin_pos_deg : 0 < Pmin.totalDegree := by
    by_contra! hle
    have h0 : Pmin.totalDegree = 0 := Nat.eq_zero_of_le_zero hle
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    have hev0 : formalEvalPoly (formalSeries φ)
        (MvPolynomial.C (Pmin.coeff 0) : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) = 0 := by
      rw [← hC]; exact hPmin_zero
    have hp0 : polyToLaurent (Pmin.coeff 0) = 0 := by
      simpa [formalEvalPoly] using hev0
    have hcoeff0 : Pmin.coeff 0 = 0 := polyToLaurent_injective (hp0.trans (map_zero _).symm)
    exact hPmin_ne (hC.trans (by rw [hcoeff0, map_zero]))
  let gapMin : ℝ := (Finset.range (r + 1)).inf'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero r)) (fun n => (ω (n + 1) - ω n) / 2)
  let δ₀ : ℝ := min (ω 0) gapMin
  have hgap_pos : 0 < gapMin := by
    rw [Finset.lt_inf'_iff]
    intro n _
    have hlt : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
    linarith
  have hδ₀_pos : 0 < δ₀ := lt_min h.ω_pos hgap_pos
  have hω_low : ∀ m : ℕ, δ₀ ≤ ω m := fun m =>
    (min_le_left (ω 0) gapMin).trans (h.ω_mono.monotone (Nat.zero_le m))
  have hω_pos : ∀ m : ℕ, 0 < ω m := fun m => lt_of_lt_of_le hδ₀_pos (hω_low m)
  have hδ_le_cut : ∀ n : ℕ, n < r + 1 → ω n + δ₀ ≤ cutRH h n := by
    intro n hn
    have h1 : δ₀ ≤ gapMin := min_le_right _ _
    have h2 : gapMin ≤ (ω (n + 1) - ω n) / 2 :=
      Finset.inf'_le (fun k => (ω (k + 1) - ω k) / 2) (Finset.mem_range.mpr hn)
    dsimp only [cutRH]
    linarith
  let g_pos : ℝ → ℂ := fun t => (aPhiH φ).value (dPlusH h) (t : ℂ)
  let g_neg : ℝ → ℂ := fun t => (aPhiH φ).value (dMinusH h) (t : ℂ)
  have h_sub_deriv : ∀ j : Fin (r + 1), ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j.val (fun t => g_neg t - g_pos t) u =
        iteratedDeriv j.val g_neg u - iteratedDeriv j.val g_pos u := fun j =>
    eventually_iteratedDeriv_sub
      (fun i _ => (lateral_eventually_differentiableH h i).2)
      (fun i _ => (lateral_eventually_differentiableH h i).1)
  obtain ⟨hP_pos, hP_neg⟩ := formalEvalPoly_zero_implies_lateral_zero h Pmin hPmin_zero
  have hL_zero : ∀ n : ℕ, n < r + 1 → L_op r (polePoly pp ord n) (ω n : ℂ) Pmin = 0 := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      have h_prev : ∀ m < n, L_op r (polePoly pp ord m) (ω m : ℂ) Pmin = 0 := fun m hm =>
        ih m hm (lt_trans hm hn)
      have h_shift_sum : ∀ k ≤ n, ∀ (u : ℝ) (x : Fin (r + 1) → ℂ) (a : ℕ → ℂ),
          MvPolynomial.eval
            (fun j => x j + ∑ m ∈ Finset.range k,
              a m * (Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ))
            (evalU Pmin (u : ℂ)) =
          MvPolynomial.eval x (evalU Pmin (u : ℂ)) := by
        intro k hk u x a
        induction k with
        | zero => simp
        | succ k ihk =>
          have hkk : k < n := Nat.lt_of_succ_le hk
          have hL_u : ∑ j : Fin (r + 1),
              (Q_jet (polePoly pp ord k) (ω k : ℂ) j.val).eval (u : ℂ) •
                MvPolynomial.pderiv j (evalU Pmin (u : ℂ)) = 0 := by
            rw [← evalU_L_op, h_prev k hkk, evalU, map_zero]
          have h1 : (fun j : Fin (r + 1) =>
              x j + ∑ m ∈ Finset.range (k + 1),
                a m * (Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ)) =
              (fun j : Fin (r + 1) =>
                (x j + ∑ m ∈ Finset.range k,
                  a m * (Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ)) +
                  a k * (Q_jet (polePoly pp ord k) (ω k : ℂ) j.val).eval (u : ℂ)) := by
            funext j; rw [Finset.sum_range_succ, add_assoc]
          rw [h1, shift_invariant_of_pderiv_sum_eq_zero _ _ hL_u, ihk (Nat.le_of_lt hkk)]
      choose Bg hBg using fun j : Fin (r + 1) => lateral_bounded_derivativesH h j.val
      have h_all_bg : ∀ᶠ u in atTop, ∀ j : Fin (r + 1), ‖iteratedDeriv j.val g_pos u‖ ≤ Bg j :=
        Filter.eventually_all.mpr hBg
      let D_q : ℕ := Finset.univ.sup fun j : Fin (r + 1) =>
        (Q_jet (polePoly pp ord n) (ω n : ℂ) j.val).natDegree
      have hD_q : ∀ j : Fin (r + 1),
          (Q_jet (polePoly pp ord n) (ω n : ℂ) j.val).natDegree ≤ D_q := fun j =>
        Finset.le_sup (f := fun j : Fin (r + 1) =>
          (Q_jet (polePoly pp ord n) (ω n : ℂ) j.val).natDegree) (Finset.mem_univ j)
      let M_q : ℝ := ∑ j : Fin (r + 1), ∑ k ∈ Finset.range (D_q + 1),
        ‖(Q_jet (polePoly pp ord n) (ω n : ℂ) j.val).coeff k‖
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
          ‖(u : ℂ)⁻¹ ^ D_q * (Q_jet (polePoly pp ord n) (ω n : ℂ) j.val).eval (u : ℂ)‖ ≤ M := by
        intro u hu j
        have h1 := poly_eval_inv_pow_bdd (Q_jet (polePoly pp ord n) (ω n : ℂ) j.val) (hD_q j) hu
        have h2 : ∑ k ∈ Finset.range (D_q + 1),
            ‖(Q_jet (polePoly pp ord n) (ω n : ℂ) j.val).coeff k‖ ≤ M_q :=
          Finset.single_le_sum
            (f := fun j' : Fin (r + 1) => ∑ k ∈ Finset.range (D_q + 1),
              ‖(Q_jet (polePoly pp ord n) (ω n : ℂ) j'.val).coeff k‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
        have h3 : 0 ≤ ∑ i : Fin (r + 1), |Bg i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        dsimp only [M]; linarith
      choose Cexp h_exp_ev using fun j : Fin (r + 1) => stokes_jump_expansion_higher_order h n j.val
      have h_all_exp : ∀ᶠ u in atTop, ∀ j : Fin (r + 1),
          ‖iteratedDeriv j.val (fun t => g_neg t - g_pos t) u -
            ∑ m ∈ Finset.range (n + 1),
              (Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
            Cexp j * Real.exp (-cutRH h n * u) :=
        Filter.eventually_all.mpr h_exp_ev
      have h_all_sub : ∀ᶠ u in atTop, ∀ j : Fin (r + 1),
          iteratedDeriv j.val (fun t => g_neg t - g_pos t) u =
            iteratedDeriv j.val g_neg u - iteratedDeriv j.val g_pos u :=
        Filter.eventually_all.mpr h_sub_deriv
      let C_rem : ℝ := ∑ j : Fin (r + 1), max (Cexp j) 0
      have hC_rem_nonneg : 0 ≤ C_rem := Finset.sum_nonneg fun _ _ => le_max_right _ _
      let Du : ℕ := maxUDeg Pmin
      choose C_lip_k hC_lip_k h_lip_k using
        fun k : ℕ => eval_lipschitz_of_bounded (coeffU k Pmin) hM_nonneg
      choose C_tay_k hC_tay_k h_tay_k using
        fun k : ℕ => eval_shift_taylor_bound (coeffU k Pmin) hM_nonneg
      let C_L : ℝ := ∑ k ∈ Finset.range (Du + 1), C_lip_k k
      let C_T : ℝ := ∑ k ∈ Finset.range (Du + 1), C_tay_k k
      have hC_L_nonneg : 0 ≤ C_L := Finset.sum_nonneg fun k _ => hC_lip_k k
      have hC_T_nonneg : 0 ≤ C_T := Finset.sum_nonneg fun k _ => hC_tay_k k
      have ha_small : ∀ᶠ u : ℝ in atTop, u ^ D_q * Real.exp (-ω n * u) ≤ 1 :=
        pow_mul_exp_neg_le_one D_q (hω_pos n)
      have hrem_small : ∀ᶠ u : ℝ in atTop, C_rem * Real.exp (-cutRH h n * u) ≤ 1 := by
        filter_upwards [pow_mul_exp_neg_le 0 (cutRH_pos h n) hC_rem_nonneg] with u hu
        simpa using hu
      have hu_poly_exp : ∀ᶠ u : ℝ in atTop,
          u ^ (Du + 2 * D_q) * Real.exp (-(δ₀ / 2) * u) ≤ 1 :=
        pow_mul_exp_neg_le_one (Du + 2 * D_q) (half_pos hδ₀_pos)
      have h_bridge_bound : ∀ᶠ u : ℝ in atTop,
          ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u)
            (evalU (L_op r (polePoly pp ord n) (ω n : ℂ) Pmin) (u : ℂ))‖ ≤
            (C_L * C_rem + C_T) * Real.exp (-(δ₀ / 2) * u) := by
        filter_upwards [h_all_bg, h_all_exp, h_all_sub, hP_pos, hP_neg,
          stokes_sum_eventually_le_one h r n, ha_small, hrem_small, hu_poly_exp,
          eventually_ge_atTop (1 : ℝ)] with u hbg hexp hsub hpos hneg hS_le1 ha1 hrem1 hpoly_u hu1
        have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
        have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
        let x : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val g_pos u
        let S : Fin (r + 1) → ℂ := fun j => ∑ m ∈ Finset.range (n + 1),
          (Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
            Complex.exp (-(ω m : ℂ) * (u : ℂ))
        let y : Fin (r + 1) → ℂ := fun j => x j + S j
        let z : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val g_neg u
        let a : ℂ := (u : ℂ) ^ D_q * Complex.exp (-(ω n : ℂ) * (u : ℂ))
        let v : Fin (r + 1) → ℂ := fun j =>
          (u : ℂ)⁻¹ ^ D_q * (Q_jet (polePoly pp ord n) (ω n : ℂ) j.val).eval (u : ℂ)
        have h_exp_norm (m : ℕ) :
            ‖Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ = Real.exp (-ω m * u) := by
          rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]
        have hx_le : ∀ j, ‖x j‖ ≤ M := fun j =>
          (hbg j).trans ((le_abs_self _).trans ((by linarith [hBg_le j] : |Bg j| ≤ M)))
        have hy_le : ∀ j, ‖y j‖ ≤ M := fun j => by
          calc ‖y j‖ ≤ ‖x j‖ + ‖S j‖ := norm_add_le _ _
            _ ≤ |Bg j| + 1 := add_le_add ((hbg j).trans (le_abs_self _)) (hS_le1 j)
            _ ≤ M := by linarith [hBg_le j]
        have hzy_le : ∀ j, ‖z j - y j‖ ≤ C_rem * Real.exp (-cutRH h n * u) := fun j => by
          have hsub_eq : z j - y j = iteratedDeriv j.val (fun t => g_neg t - g_pos t) u - S j := by
            rw [hsub j]; simp only [y, x, z]; ring
          rw [hsub_eq]
          refine (hexp j).trans ?_
          calc Cexp j * Real.exp (-cutRH h n * u)
              ≤ max (Cexp j) 0 * Real.exp (-cutRH h n * u) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
            _ ≤ C_rem * Real.exp (-cutRH h n * u) :=
                mul_le_mul_of_nonneg_right
                  (Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j))
                  (Real.exp_pos _).le
        have hz_le : ∀ j, ‖z j‖ ≤ M := fun j => by
          have hid : z j = y j + (z j - y j) := by ring
          rw [hid]
          calc ‖y j + (z j - y j)‖ ≤ ‖y j‖ + ‖z j - y j‖ := norm_add_le _ _
            _ ≤ (|Bg j| + 1) + 1 :=
                add_le_add ((norm_add_le _ _).trans
                  (add_le_add ((hbg j).trans (le_abs_self _)) (hS_le1 j)))
                  ((hzy_le j).trans hrem1)
            _ ≤ M := by linarith [hBg_le j]
        have ha_norm : ‖a‖ = u ^ D_q * Real.exp (-ω n * u) := by
          simp only [a, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos,
            h_exp_norm]
        have ha_le1 : ‖a‖ ≤ 1 := by rw [ha_norm]; exact ha1
        have hu_pow_le : ∀ k ∈ Finset.range (Du + 1), ‖(u : ℂ) ^ k‖ ≤ u ^ Du := fun k hk => by
          rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
          exact pow_le_pow_right₀ hu1 (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
        have h_lip_y : ‖MvPolynomial.eval y (evalU Pmin (u : ℂ))‖ ≤
            (C_L * C_rem) * u ^ Du * Real.exp (-cutRH h n * u) := by
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
                  u ^ Du * (C_lip_k k * (C_rem * Real.exp (-cutRH h n * u))) := by
                refine Finset.sum_le_sum fun k hk => ?_
                rw [norm_mul]
                have hlk := h_lip_k k z y (C_rem * Real.exp (-cutRH h n * u))
                  (mul_nonneg hC_rem_nonneg (Real.exp_pos _).le) hz_le hy_le hzy_le
                rw [norm_sub_rev] at hlk
                exact mul_le_mul (hu_pow_le k hk) hlk (norm_nonneg _) (pow_nonneg hu_pos.le Du)
            _ = (C_L * C_rem) * u ^ Du * Real.exp (-cutRH h n * u) := by
                dsimp only [C_L]
                rw [← Finset.mul_sum, ← Finset.sum_mul]
                ring
        have hav : ∀ j : Fin (r + 1),
            a * v j = (Q_jet (polePoly pp ord n) (ω n : ℂ) j.val).eval (u : ℂ) *
              Complex.exp (-(ω n : ℂ) * (u : ℂ)) := fun j => by
          dsimp only [a, v]
          calc (u : ℂ) ^ D_q * Complex.exp (-(ω n : ℂ) * (u : ℂ)) *
                ((u : ℂ)⁻¹ ^ D_q * (Q_jet (polePoly pp ord n) (ω n : ℂ) j.val).eval (u : ℂ))
              = ((u : ℂ) * (u : ℂ)⁻¹) ^ D_q *
                  ((Q_jet (polePoly pp ord n) (ω n : ℂ) j.val).eval (u : ℂ) *
                    Complex.exp (-(ω n : ℂ) * (u : ℂ))) := by rw [mul_pow]; ring
            _ = _ := by rw [mul_inv_cancel₀ hu_ne, one_pow, one_mul]
        have hy_eq : MvPolynomial.eval y (evalU Pmin (u : ℂ)) =
            MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ)) := by
          have hy_split : y = fun j => (x j + a * v j) +
              ∑ m ∈ Finset.range n,
                Complex.exp (-(ω m : ℂ) * (u : ℂ)) *
                  (Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) := by
            funext j
            simp only [y, S, Finset.sum_range_succ, hav j]
            have hcomm : ∀ m, (Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
                Complex.exp (-(ω m : ℂ) * (u : ℂ)) *
                  (Q_jet (polePoly pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) := fun _ => by ring
            simp_rw [hcomm]
            ring
          rw [hy_split]
          exact h_shift_sum n le_rfl u (fun j => x j + a * v j)
            (fun m => Complex.exp (-(ω m : ℂ) * (u : ℂ)))
        have h_tay_y :
            ‖MvPolynomial.eval y (evalU Pmin (u : ℂ)) -
                a * ∑ j : Fin (r + 1),
                  MvPolynomial.eval x (MvPolynomial.pderiv j (evalU Pmin (u : ℂ))) * v j‖ ≤
              C_T * u ^ Du * ‖a‖ ^ 2 := by
          have hsum_id :
              MvPolynomial.eval y (evalU Pmin (u : ℂ)) -
                a * ∑ j : Fin (r + 1),
                  MvPolynomial.eval x (MvPolynomial.pderiv j (evalU Pmin (u : ℂ))) * v j =
              ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                (MvPolynomial.eval (fun j => x j + a * v j) (coeffU k Pmin) -
                  MvPolynomial.eval x (coeffU k Pmin) -
                  a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (coeffU k Pmin)) * v j) := by
            have hx0 : MvPolynomial.eval x (evalU Pmin (u : ℂ)) = 0 := hpos
            rw [hy_eq, ← sub_zero (MvPolynomial.eval (fun j => x j + a * v j) (evalU Pmin (u : ℂ))),
              ← hx0]
            have hpd_u : ∑ j : Fin (r + 1),
                  MvPolynomial.eval x (MvPolynomial.pderiv j (evalU Pmin (u : ℂ))) * v j =
                ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                  ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (coeffU k Pmin)) * v j := by
              have hexp_j : ∀ j : Fin (r + 1),
                  MvPolynomial.eval x (MvPolynomial.pderiv j (evalU Pmin (u : ℂ))) * v j =
                    ∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k *
                      (MvPolynomial.eval x (MvPolynomial.pderiv j (coeffU k Pmin)) * v j) := by
                intro j
                rw [evalU_eq_sum_coeffU Pmin (u : ℂ), map_sum, map_sum, Finset.sum_mul]
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [(MvPolynomial.pderiv j).map_smul_of_tower, MvPolynomial.smul_eq_C_mul, map_mul,
                  MvPolynomial.eval_C, mul_assoc]
              simp_rw [hexp_j]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.mul_sum]
            rw [hpd_u, Finset.mul_sum]
            dsimp only [Du]
            simp only [evalU_eq_sum_coeffU Pmin (u : ℂ), map_sum, MvPolynomial.smul_eq_C_mul,
              map_mul, MvPolynomial.eval_C, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun k _ => by ring
          rw [hsum_id]
          calc ‖∑ k ∈ Finset.range (Du + 1), (u : ℂ) ^ k * _‖
              ≤ ∑ k ∈ Finset.range (Du + 1), ‖(u : ℂ) ^ k * _‖ := norm_sum_le _ _
            _ ≤ ∑ k ∈ Finset.range (Du + 1), u ^ Du * (C_tay_k k * ‖a‖ ^ 2) := by
                refine Finset.sum_le_sum fun k hk => ?_
                rw [norm_mul]
                exact mul_le_mul (hu_pow_le k hk)
                  (h_tay_k k x v a hx_le (hv_bdd u hu1) ha_le1) (norm_nonneg _)
                  (pow_nonneg hu_pos.le Du)
            _ = C_T * u ^ Du * ‖a‖ ^ 2 := by
                dsimp only [C_T]; rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
        have hL_rew :
            a * ∑ j : Fin (r + 1),
              MvPolynomial.eval x (MvPolynomial.pderiv j (evalU Pmin (u : ℂ))) * v j =
            Complex.exp (-(ω n : ℂ) * (u : ℂ)) *
              MvPolynomial.eval x (evalU (L_op r (polePoly pp ord n) (ω n : ℂ) Pmin) (u : ℂ)) := by
          rw [evalU_L_op, map_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, ← mul_assoc,
            mul_comm a, mul_assoc _ a, hav j]
          ring
        rw [hL_rew] at h_tay_y
        have h_main :
            Real.exp (-ω n * u) *
              ‖MvPolynomial.eval x (evalU (L_op r (polePoly pp ord n) (ω n : ℂ) Pmin) (u : ℂ))‖ ≤
            (C_L * C_rem) * u ^ Du * Real.exp (-cutRH h n * u) +
              C_T * u ^ Du * (u ^ D_q * Real.exp (-ω n * u)) ^ 2 := by
          have htri := norm_sub_le (MvPolynomial.eval y (evalU Pmin (u : ℂ)))
            (MvPolynomial.eval y (evalU Pmin (u : ℂ)) -
              Complex.exp (-(ω n : ℂ) * (u : ℂ)) *
                MvPolynomial.eval x (evalU (L_op r (polePoly pp ord n) (ω n : ℂ) Pmin) (u : ℂ)))
          have hsimp : MvPolynomial.eval y (evalU Pmin (u : ℂ)) -
              (MvPolynomial.eval y (evalU Pmin (u : ℂ)) -
                Complex.exp (-(ω n : ℂ) * (u : ℂ)) *
                  MvPolynomial.eval x (evalU (L_op r (polePoly pp ord n) (ω n : ℂ) Pmin) (u : ℂ))) =
              Complex.exp (-(ω n : ℂ) * (u : ℂ)) *
                MvPolynomial.eval x (evalU (L_op r (polePoly pp ord n) (ω n : ℂ) Pmin) (u : ℂ)) := by
            ring
          rw [hsimp, norm_mul, h_exp_norm n] at htri
          rw [ha_norm] at h_tay_y
          exact htri.trans (add_le_add h_lip_y h_tay_y)
        have hcut : ω n + δ₀ ≤ cutRH h n := hδ_le_cut n hn
        have h1_bound : u ^ Du * Real.exp (-cutRH h n * u) ≤
            Real.exp (-ω n * u) * Real.exp (-(δ₀ / 2) * u) := by
          have hexp_cut : Real.exp (-cutRH h n * u) ≤ Real.exp (-(ω n + δ₀) * u) := by
            rw [Real.exp_le_exp]; nlinarith [hu_pos.le]
          have hpow_le : u ^ Du ≤ u ^ (Du + 2 * D_q) :=
            pow_le_pow_right₀ hu1 (Nat.le_add_right Du _)
          have hexp_eq : Real.exp (-(ω n + δ₀) * u) =
              Real.exp (-ω n * u) * (Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u)) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          calc u ^ Du * Real.exp (-cutRH h n * u)
              ≤ u ^ (Du + 2 * D_q) * Real.exp (-(ω n + δ₀) * u) :=
                mul_le_mul hpow_le hexp_cut (Real.exp_pos _).le (pow_nonneg hu_pos.le _)
            _ = Real.exp (-ω n * u) *
                  ((u ^ (Du + 2 * D_q) * Real.exp (-(δ₀ / 2) * u)) * Real.exp (-(δ₀ / 2) * u)) := by
                rw [hexp_eq]; ring
            _ ≤ Real.exp (-ω n * u) * (1 * Real.exp (-(δ₀ / 2) * u)) := by
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le) (Real.exp_pos _).le
            _ = Real.exp (-ω n * u) * Real.exp (-(δ₀ / 2) * u) := by rw [one_mul]
        have h2_bound : u ^ Du * (u ^ D_q * Real.exp (-ω n * u)) ^ 2 ≤
            Real.exp (-ω n * u) * Real.exp (-(δ₀ / 2) * u) := by
          have hexp_om : Real.exp (-ω n * u) ≤ Real.exp (-δ₀ * u) := by
            rw [Real.exp_le_exp]; nlinarith [hω_low n, hu_pos.le]
          have hexp_eq : Real.exp (-δ₀ * u) =
              Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u) := by
            rw [← Real.exp_add]; congr 1; ring
          calc u ^ Du * (u ^ D_q * Real.exp (-ω n * u)) ^ 2
              = Real.exp (-ω n * u) * (u ^ (Du + 2 * D_q) * Real.exp (-ω n * u)) := by
                rw [mul_pow, ← pow_mul, pow_add]; ring
            _ ≤ Real.exp (-ω n * u) * (u ^ (Du + 2 * D_q) * Real.exp (-δ₀ * u)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hexp_om (pow_nonneg hu_pos.le _)) (Real.exp_pos _).le
            _ = Real.exp (-ω n * u) *
                  ((u ^ (Du + 2 * D_q) * Real.exp (-(δ₀ / 2) * u)) * Real.exp (-(δ₀ / 2) * u)) := by
                rw [hexp_eq]; ring
            _ ≤ Real.exp (-ω n * u) * (1 * Real.exp (-(δ₀ / 2) * u)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le) (Real.exp_pos _).le
            _ = Real.exp (-ω n * u) * Real.exp (-(δ₀ / 2) * u) := by rw [one_mul]
        have h_rhs :
            (C_L * C_rem) * u ^ Du * Real.exp (-cutRH h n * u) +
              C_T * u ^ Du * (u ^ D_q * Real.exp (-ω n * u)) ^ 2 ≤
            Real.exp (-ω n * u) * ((C_L * C_rem + C_T) * Real.exp (-(δ₀ / 2) * u)) := by
          calc (C_L * C_rem) * u ^ Du * Real.exp (-cutRH h n * u) +
                C_T * u ^ Du * (u ^ D_q * Real.exp (-ω n * u)) ^ 2
              = (C_L * C_rem) * (u ^ Du * Real.exp (-cutRH h n * u)) +
                  C_T * (u ^ Du * (u ^ D_q * Real.exp (-ω n * u)) ^ 2) := by ring
            _ ≤ (C_L * C_rem) * (Real.exp (-ω n * u) * Real.exp (-(δ₀ / 2) * u)) +
                  C_T * (Real.exp (-ω n * u) * Real.exp (-(δ₀ / 2) * u)) :=
                add_le_add (mul_le_mul_of_nonneg_left h1_bound (mul_nonneg hC_L_nonneg hC_rem_nonneg))
                  (mul_le_mul_of_nonneg_left h2_bound hC_T_nonneg)
            _ = Real.exp (-ω n * u) * ((C_L * C_rem + C_T) * Real.exp (-(δ₀ / 2) * u)) := by ring
        have h_main' :
            Real.exp (-ω n * u) *
              ‖MvPolynomial.eval x (evalU (L_op r (polePoly pp ord n) (ω n : ℂ) Pmin) (u : ℂ))‖ ≤
            Real.exp (-ω n * u) * ((C_L * C_rem + C_T) * Real.exp (-(δ₀ / 2) * u)) :=
          h_main.trans h_rhs
        exact le_of_mul_le_mul_left h_main' (Real.exp_pos _)
      have h_iso := eval_lateral_flat_implies_formalEvalPoly_zero h (half_pos hδ₀_pos)
        (L_op r (polePoly pp ord n) (ω n : ℂ) Pmin) ⟨C_L * C_rem + C_T, h_bridge_bound⟩
      by_contra h_ne
      exact hPmin_min _ h_ne (degree_L_op_lt _ _ Pmin hPmin_pos_deg) h_iso
  exact D_freq_top_of_L_op_eq_zero Pmin hPmin_pos_deg ω h.ω_mono (polePoly pp ord) ord
    h.ord_pos (fun k _ => polePoly_natDegree h.ord_pos h.pp_lead_ne_zero k)
    (fun k _ => polePoly_leadingCoeff h.ord_pos h.pp_lead_ne_zero k) hL_zero

/-- **General Sectorial Higher-Order Non-Autonomous Stokes–Vandermonde Theorem (Arbitrary Ray `θ₀`, Arbitrary Orders `ord m ≥ 1`, Coefficients in `ℂ[u]`)**:
Given `HigherOrderBorelData φ θ₀ ω ord pp`, the formal Laplace series `formalSeries φ`
satisfies NO nonzero non-autonomous polynomial differential equation over `ℂ[u]`. -/
theorem higher_order_stokes_vandermonde_no_ade
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries φ) P = 0) : P = 0 := by
  let μ : ℂ := Complex.exp (I * (θ₀ : ℂ))
  have hμ_ne : μ ≠ 0 := Complex.exp_ne_zero _
  have hμ_inv : μ⁻¹ = Complex.exp (-I * (θ₀ : ℂ)) := by
    rw [← Complex.exp_neg]; congr 1; ring
  let φ_rot : ℂ → ℂ := fun z => φ (μ * z)
  let pp_rot : ℕ → ℕ → ℂ := fun m s => μ⁻¹ ^ s * pp m s
  have hmem0 : (0 : ℂ) ∈ rotatedPuncturedWedge θ₀ h.α₀ h.ε ω := by
    refine ⟨Or.inl ?_, ?_⟩
    · simp [h.hε_pos]
    · rintro ⟨m, hm⟩
      have hm_re := congrArg Complex.re hm
      simp only [mul_zero, Complex.zero_re, Complex.ofReal_re] at hm_re
      have hωm : 0 < ω m := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
      linarith
  have hφ0 : AnalyticAt ℂ φ 0 := h.analyticOn 0 hmem0
  have h_rot : HigherOrderBorelData φ_rot 0 ω ord pp_rot :=
    { α₀ := h.α₀
      θ := h.θ
      ε := h.ε
      hθ_pos := h.hθ_pos
      hθ_lt := h.hθ_lt
      hα₀_lt := h.hα₀_lt
      hε_pos := h.hε_pos
      ω_pos := h.ω_pos
      ω_mono := h.ω_mono
      ord_pos := h.ord_pos
      pp_lead_ne_zero := fun m => mul_ne_zero (pow_ne_zero _ (inv_ne_zero hμ_ne)) (h.pp_lead_ne_zero m)
      analyticOn := fun z hz => by
        have hz_rot : μ * z ∈ rotatedPuncturedWedge θ₀ h.α₀ h.ε ω := by
          rw [rotatedPuncturedWedge_zero_eq] at hz
          change Complex.exp (-I * (θ₀ : ℂ)) * (μ * z) ∈ puncturedWedge h.α₀ h.ε ω
          rw [← mul_assoc, ← hμ_inv, inv_mul_cancel₀ hμ_ne, one_mul]
          exact hz
        exact (h.analyticOn (μ * z) hz_rot).comp (analyticAt_const.mul analyticAt_id)
      pole_principalPart := fun m => by
        obtain ⟨L, hL⟩ := h.pole_principalPart m
        refine ⟨L, ?_⟩
        have htend_mul : Tendsto (fun z : ℂ => μ * z) (𝓝[≠] (ω m : ℂ)) (𝓝[≠] (μ * (ω m : ℂ))) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨(continuous_const.mul continuous_id).continuousAt.continuousWithinAt, ?_⟩
          exact eventually_nhdsWithin_of_forall fun z hz heq => hz (mul_left_cancel₀ hμ_ne heq)
        have hcomp := hL.comp htend_mul
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
        refine hcomp.congr' (eventually_nhdsWithin_of_forall fun z _ => ?_)
        simp only [Function.comp_def, φ_rot]
        congr 1
        refine Finset.sum_congr rfl fun s _ => ?_
        dsimp only [pp_rot]
        rw [← mul_sub, mul_pow, inv_pow]
        field_simp [hμ_ne]
      expType_plus := by
        obtain ⟨C, D, hC, hD, hbd⟩ := h.expType_plus
        refine ⟨C, D, hC, hD, fun v hv => ?_⟩
        have h_exp : μ * Complex.exp (I * (h.θ : ℂ)) = Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ)) := by
          dsimp only [μ]; rw [← Complex.exp_add]; congr 1; push_cast; ring
        have h_eq : Minor.pull (Complex.exp (I * ((0 + h.θ : ℝ) : ℂ))) φ_rot v =
            μ⁻¹ * Minor.pull (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ))) φ v := by
          simp only [Minor.pull, φ_rot, zero_add]
          rw [← mul_assoc (μ : ℂ), h_exp]
          calc Complex.exp (I * (h.θ : ℂ)) * φ (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ)) * (v : ℂ))
              = (μ⁻¹ * (μ * Complex.exp (I * (h.θ : ℂ)))) *
                  φ (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ)) * (v : ℂ)) := by
                rw [← mul_assoc, inv_mul_cancel₀ hμ_ne, one_mul]
            _ = μ⁻¹ * (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ)) *
                  φ (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ)) * (v : ℂ))) := by
                rw [h_exp, mul_assoc]
        have hnorm_inv : ‖μ⁻¹‖ = 1 := by
          rw [hμ_inv, show -I * (θ₀ : ℂ) = ((-θ₀ : ℝ) : ℂ) * I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I (-θ₀)
        rw [h_eq, norm_mul, hnorm_inv, one_mul]
        exact hbd v hv
      expType_minus := by
        obtain ⟨C, D, hC, hD, hbd⟩ := h.expType_minus
        refine ⟨C, D, hC, hD, fun v hv => ?_⟩
        have h_exp : μ * Complex.exp (I * ((-h.θ : ℝ) : ℂ)) =
            Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ)) := by
          dsimp only [μ]; rw [← Complex.exp_add]; congr 1; push_cast; ring
        have h_eq : Minor.pull (Complex.exp (I * ((0 - h.θ : ℝ) : ℂ))) φ_rot v =
            μ⁻¹ * Minor.pull (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ))) φ v := by
          simp only [Minor.pull, φ_rot, zero_sub]
          rw [← mul_assoc (μ : ℂ), h_exp]
          calc Complex.exp (I * ((-h.θ : ℝ) : ℂ)) *
                  φ (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ)) * (v : ℂ))
              = (μ⁻¹ * (μ * Complex.exp (I * ((-h.θ : ℝ) : ℂ)))) *
                  φ (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ)) * (v : ℂ)) := by
                rw [← mul_assoc, inv_mul_cancel₀ hμ_ne, one_mul]
            _ = μ⁻¹ * (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ)) *
                  φ (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ)) * (v : ℂ))) := by
                rw [h_exp, mul_assoc]
        have hnorm_inv : ‖μ⁻¹‖ = 1 := by
          rw [hμ_inv, show -I * (θ₀ : ℂ) = ((-θ₀ : ℝ) : ℂ) * I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I (-θ₀)
        rw [h_eq, norm_mul, hnorm_inv, one_mul]
        exact hbd v hv }
  exact (rotPoly_eq_zero_iff hμ_ne P).mp
    (higher_order_stokes_vandermonde_no_ade_zero h_rot (rotPoly r μ P)
      (formalEvalPoly_rot_eq_zero hφ0 hμ_ne P hP))

private def clearDenomPoly {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    Polynomial ℂ :=
  ∏ α ∈ P.support, (P.coeff α).denom

private lemma clearDenomPoly_ne_zero {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    clearDenomPoly P ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => RatFunc.denom_ne_zero _

private def clearDenomMvPoly {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
  ∑ α ∈ P.support, MvPolynomial.monomial α
    ((P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom)

private lemma clearDenomMvPoly_coeff {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (α : Fin (r + 1) →₀ ℕ) :
    (clearDenomMvPoly P).coeff α =
      (P.coeff α).num * ∏ β ∈ P.support.erase α, (P.coeff β).denom := by
  classical
  unfold clearDenomMvPoly
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
    rw [hP0, RatFunc.num_zero, zero_mul, Finset.sum_eq_zero]
    intro β hβ
    have hne : β ≠ α := fun h => hα (h ▸ hβ)
    simp [hne]

private lemma clearDenomMvPoly_eq_zero_iff {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    clearDenomMvPoly P = 0 ↔ P = 0 := by
  constructor
  · intro h0
    ext α
    have hc := congrArg (fun Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) => Q.coeff α) h0
    change (clearDenomMvPoly P).coeff α = 0 at hc
    rw [clearDenomMvPoly_coeff] at hc
    have hden_ne : (∏ β ∈ P.support.erase α, (P.coeff β).denom) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun _ _ => RatFunc.denom_ne_zero _
    have hnum0 : (P.coeff α).num = 0 := (mul_eq_zero.mp hc).resolve_right hden_ne
    exact RatFunc.num_eq_zero_iff.mp hnum0
  · rintro rfl
    simp [clearDenomMvPoly]

private lemma formalEvalPoly_clearDenomMvPoly {r : ℕ} (S : PowerSeries ℂ)
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) :
    formalEvalPoly S (clearDenomMvPoly P) = polyToLaurent (clearDenomPoly P) * formalEvalRat S P := by
  have hPsum : formalEvalRat S P =
      ∑ α ∈ P.support, ratToLaurent (P.coeff α) *
        α.prod fun j e => ((d_u^[j.val] S : PowerSeries ℂ) : LaurentSeries ℂ) ^ e := by
    conv_lhs => rw [MvPolynomial.as_sum P, formalEvalRat, MvPolynomial.eval₂_sum]
    refine Finset.sum_congr rfl fun α _ => MvPolynomial.eval₂_monomial _ _
  unfold formalEvalPoly clearDenomMvPoly
  rw [MvPolynomial.eval₂_sum, hPsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [MvPolynomial.eval₂_monomial, ← mul_assoc]
  congr 1
  unfold clearDenomPoly
  rw [← Finset.mul_prod_erase P.support (fun β => (P.coeff β).denom) hα]
  simp only [map_mul, map_prod]
  have hrat : ratToLaurent (P.coeff α) =
      polyToLaurent (P.coeff α).num / polyToLaurent (P.coeff α).denom := by
    unfold ratToLaurent
    exact RatFunc.liftRingHom_apply polyToLaurent _ (P.coeff α)
  have hden_ne : polyToLaurent (P.coeff α).denom ≠ 0 := fun h0 =>
    RatFunc.denom_ne_zero (P.coeff α) (polyToLaurent_injective (h0.trans (map_zero _).symm))
  rw [hrat]
  field_simp [hden_ne]

/-- **General Sectorial Higher-Order Non-Autonomous Stokes–Vandermonde Theorem over `ℂ(u)`**:
Given `HigherOrderBorelData φ θ₀ ω ord pp`, the formal Laplace series `formalSeries φ`
satisfies NO nonzero non-autonomous rational-coefficient differential equation over `ℂ(u)`. -/
theorem higher_order_stokes_vandermonde_no_rat_ade
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries φ) P = 0) : P = 0 := by
  have hclear : formalEvalPoly (formalSeries φ) (clearDenomMvPoly P) = 0 := by
    rw [formalEvalPoly_clearDenomMvPoly, hP, mul_zero]
  exact (clearDenomMvPoly_eq_zero_iff P).mp (higher_order_stokes_vandermonde_no_ade h _ hclear)

private lemma formalEvalPoly_of_autonomous {r : ℕ} (S : PowerSeries ℂ)
    (P : MvPolynomial (Fin (r + 1)) ℂ) :
    formalEvalPoly S (MvPolynomial.map Polynomial.C P) =
      ((formalEval S P : PowerSeries ℂ) : LaurentSeries ℂ) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.map_C, formalEvalPoly, formalEval, MvPolynomial.eval₂_C,
      MvPolynomial.aeval_C, polyToLaurent, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Polynomial.aeval_C]
    have h1 : algebraMap ℂ (LaurentSeries ℂ) c = HahnSeries.C c := HahnSeries.ofPowerSeries_C c
    have h2 : (((algebraMap ℂ (PowerSeries ℂ) c : PowerSeries ℂ) : LaurentSeries ℂ)) =
        HahnSeries.C c := by
      rw [PowerSeries.algebraMap_eq]
      exact PowerSeries.coe_C c
    exact h1.trans h2.symm
  | add A B hA hB =>
    simp only [map_add, formalEvalPoly, formalEval, MvPolynomial.eval₂_add] at hA hB ⊢
    rw [hA, hB]
  | mul_X A j hA =>
    simp only [map_mul, MvPolynomial.map_X, formalEvalPoly, formalEval, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_X, MvPolynomial.aeval_X] at hA ⊢
    rw [hA]

/-- **Autonomous Corollary of Higher-Order Sectorial Stokes–Vandermonde**:
Recovers autonomous non-existence of ADEs over `ℂ` from arbitrary rotated `HigherOrderBorelData`. -/
theorem higher_order_stokes_vandermonde_no_autonomous_ade
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : formalEval (formalSeries φ) P = 0) : P = 0 := by
  have hP' : formalEvalPoly (formalSeries φ) (MvPolynomial.map Polynomial.C P) = 0 := by
    rw [formalEvalPoly_of_autonomous, hP, PowerSeries.coe_zero]
  have hC := higher_order_stokes_vandermonde_no_ade h (MvPolynomial.map Polynomial.C P) hP'
  exact MvPolynomial.map_injective Polynomial.C Polynomial.C_injective (hC.trans (map_zero _).symm)

/-- **Backward Compatibility Bridge (`General Theorem 2 ⊆ Theorem PY-1`)**:
Every simple-pole `MeromorphicBorelData φ ω res` canonically induces a `HigherOrderBorelData`
witness at `θ₀ = 0`, `ord _ = 1`, and `pp m s = if s = 1 then res m else 0`. -/
def MeromorphicBorelData.toHigherOrderBorelData
    {φ : ℂ → ℂ} {ω : ℕ → ℝ} {res : ℕ → ℂ}
    (h : MeromorphicBorelData φ ω res) :
    HigherOrderBorelData φ 0 ω (fun _ => 1) (fun m s => if s = 1 then res m else 0) where
  α₀ := h.θ₀
  θ := h.θ
  ε := h.ε
  hθ_pos := h.hθ_pos
  hθ_lt := h.hθ_lt
  hα₀_lt := h.hθ₀_lt
  hε_pos := h.hε_pos
  ω_pos := h.ω_pos
  ω_mono := h.ω_mono
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun m => by simpa using h.res_ne_zero m
  analyticOn := by
    rw [rotatedPuncturedWedge_zero_eq]
    exact h.analyticOn
  pole_principalPart := fun m => by
    have htan_pos : 0 < Real.tan h.θ₀ :=
      Real.tan_pos_of_pos_of_lt_pi_div_two (h.hθ_pos.trans h.hθ_lt) h.hθ₀_lt
    have hωm_pos : 0 < ω m := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
    have hmem_wedge : (ω m : ℂ) ∈ borelWedge h.θ₀ h.ε :=
      Or.inr ⟨by simpa using hωm_pos, by simpa using mul_pos htan_pos hωm_pos⟩
    have hopen_wedge : IsOpen (borelWedge h.θ₀ h.ε) :=
      Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt (continuous_abs.comp Complex.continuous_im)
          (continuous_const.mul Complex.continuous_re)))
    obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.isOpen_iff.mp hopen_wedge (ω m : ℂ) hmem_wedge
    let r₁ : ℝ := if hm0 : m = 0 then (ω 1 - ω 0) / 2
      else min ((ω m - ω (m - 1)) / 2) ((ω (m + 1) - ω m) / 2)
    have hr₁_pos : 0 < r₁ := by
      dsimp only [r₁]
      split_ifs with hm0
      · have h01 : ω 0 < ω 1 := h.ω_mono zero_lt_one; linarith
      · have hm_pos : 1 ≤ m := Nat.pos_of_ne_zero hm0
        have h1 : ω (m - 1) < ω m := h.ω_mono (by omega)
        have h2 : ω m < ω (m + 1) := h.ω_mono (Nat.lt_succ_self m)
        exact lt_min (by linarith) (by linarith)
    let r : ℝ := min r₀ r₁
    have hr_pos : 0 < r := lt_min hr₀_pos hr₁_pos
    have hsub_punc : Metric.ball (ω m : ℂ) r \ {(ω m : ℂ)} ⊆ puncturedWedge h.θ₀ h.ε ω := by
      intro z ⟨hz_ball, hz_ne⟩
      refine ⟨hr₀_sub ((Metric.ball_subset_ball (min_le_left _ _)) hz_ball), ?_⟩
      rintro ⟨k, hk⟩
      have hkm : k ≠ m := fun h0 => hz_ne (by subst h0; exact hk.symm)
      rw [Metric.mem_ball, dist_eq_norm, ← hk, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] at hz_ball
      have hdist_ge : r₁ ≤ |ω k - ω m| := by
        rcases lt_or_gt_of_ne hkm with hlt | hgt
        · have hm0 : m ≠ 0 := by omega
          have hkle : k ≤ m - 1 := by omega
          have hwk : ω k ≤ ω (m - 1) := h.ω_mono.monotone hkle
          have hwm : ω (m - 1) < ω m := h.ω_mono (by omega)
          have hr1_le : r₁ ≤ (ω m - ω (m - 1)) / 2 := by
            dsimp only [r₁]
            simp only [hm0, ↓reduceDIte]
            exact min_le_left _ _
          rw [abs_of_neg (by linarith)]
          linarith
        · have hm1 : m + 1 ≤ k := by omega
          have hwk : ω (m + 1) ≤ ω k := h.ω_mono.monotone hm1
          have hr1_le : r₁ ≤ (ω (m + 1) - ω m) / 2 := by
            dsimp only [r₁]
            split_ifs with hm0
            · subst hm0; simp
            · exact min_le_right _ _
          have hwm : ω m < ω (m + 1) := h.ω_mono (Nat.lt_succ_self m)
          rw [abs_of_pos (by linarith)]
          linarith
      linarith [min_le_right r₀ r₁]
    let g : ℂ → ℂ := fun z => if z = (ω m : ℂ) then res m else (z - (ω m : ℂ)) * φ z
    have hdiff_punc : ∀ᶠ w in 𝓝[≠] (ω m : ℂ), DifferentiableAt ℂ g w := by
      have hmem : Metric.ball (ω m : ℂ) r \ {(ω m : ℂ)} ∈ 𝓝[≠] (ω m : ℂ) := by
        rw [Set.sdiff_eq, Set.inter_comm]
        exact inter_mem_nhdsWithin _ (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))
      filter_upwards [hmem] with w hw
      have hd_prod : DifferentiableAt ℂ (fun ζ => (ζ - (ω m : ℂ)) * φ ζ) w :=
        (differentiableAt_id.sub_const _).mul (h.analyticOn w (hsub_punc hw)).differentiableAt
      have heq : g =ᶠ[𝓝 w] fun ζ => (ζ - (ω m : ℂ)) * φ ζ := by
        have hopen : IsOpen (Metric.ball (ω m : ℂ) r \ {(ω m : ℂ)}) :=
          Metric.isOpen_ball.sdiff isClosed_singleton
        filter_upwards [hopen.mem_nhds hw] with ζ hζ
        dsimp only [g]
        exact ite_eq_right_iff.mpr fun h0 => absurd h0 hζ.2
      exact hd_prod.congr_of_eventuallyEq heq
    have hcont_g : ContinuousAt g (ω m : ℂ) := by
      refine continuousAt_iff_punctured_nhds.mpr ?_
      have hg_at : g (ω m : ℂ) = res m := by simp [g]
      rw [hg_at]
      refine (h.simple_pole m).congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
      exact (ite_eq_right_iff.mpr fun h0 => absurd h0 hz).symm
    have hg_an : AnalyticAt ℂ g (ω m : ℂ) :=
      Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hdiff_punc hcont_g
    have hdslope_cont : ContinuousAt (dslope g (ω m : ℂ)) (ω m : ℂ) :=
      hg_an.hasFPowerSeriesAt.dslope_fslope.continuousAt
    refine ⟨dslope g (ω m : ℂ) (ω m : ℂ), ?_⟩
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    refine hdslope_cont.continuousWithinAt.tendsto.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)
    have hsub : z - (ω m : ℂ) ≠ 0 := sub_ne_zero.mpr hz
    rw [dslope_of_ne g hz, slope_def_field]
    have hgz : g z = (z - (ω m : ℂ)) * φ z := ite_eq_right_iff.mpr fun h0 => absurd h0 hz
    have hgm : g (ω m : ℂ) = res m := by simp [g]
    rw [hgz, hgm]
    simp only [Finset.Icc_self, Finset.sum_singleton, ↓reduceIte, pow_one]
    field_simp [hsub]
  expType_plus := by simpa using h.expType_plus
  expType_minus := by
    have heq : (Complex.exp (I * ((0 - h.θ : ℝ) : ℂ))) = Complex.exp (-I * (h.θ : ℂ)) := by
      congr 1; push_cast; ring
    rw [heq]; exact h.expType_minus

private lemma HasAsympExp.inv :
    HasAsympExp (fun u : ℝ => (u : ℂ)⁻¹) PowerSeries.X := by
  intro M
  cases M with
  | zero =>
    refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
    simpa [norm_inv, abs_of_pos hu_pos] using inv_le_one_of_one_le₀ hu
  | succ M =>
    cases M with
    | zero =>
      refine ⟨1, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      simp [norm_inv, abs_of_pos hu, div_eq_mul_inv]
    | succ m =>
      refine ⟨0, ?_⟩
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
      have hsum : ∑ k ∈ Finset.range (m + 2),
          PowerSeries.coeff k (PowerSeries.X : PowerSeries ℂ) * ((u : ℂ)⁻¹ ^ k) = (u : ℂ)⁻¹ := by
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        simp only [PowerSeries.coeff_zero_X, zero_mul, add_zero]
        have h1 : PowerSeries.coeff (0 + 1) (PowerSeries.X : PowerSeries ℂ) = 1 := by
          rw [PowerSeries.coeff_X, ite_eq_left_iff.mpr fun h => absurd rfl h]
        rw [h1, one_mul, pow_one]
        have htail : ∑ k ∈ Finset.range m,
            PowerSeries.coeff (k + 1 + 1) (PowerSeries.X : PowerSeries ℂ) * ((u : ℂ)⁻¹ ^ (k + 1 + 1)) = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          rw [PowerSeries.coeff_X, ite_eq_right_iff.mpr (by omega), zero_mul]
        rw [htail, zero_add]
      rw [hsum, sub_self, norm_zero, zero_div]

private lemma HasAsympExp.inv_pow (k : ℕ) :
    HasAsympExp (fun u : ℝ => (u : ℂ)⁻¹ ^ k) ((PowerSeries.X : PowerSeries ℂ) ^ k) := by
  induction k with
  | zero => simpa using HasAsympExp.const 1
  | succ k ih =>
    simp only [pow_succ]
    exact ih.mul HasAsympExp.inv

private lemma HasAsympExp.poly_inv (q : Polynomial ℂ) :
    HasAsympExp (fun u : ℝ => q.eval (u : ℂ)⁻¹) (q : PowerSeries ℂ) := by
  induction q using Polynomial.induction_on' with
  | add a b ha hb =>
    simp only [Polynomial.eval_add, Polynomial.coe_add]
    exact ha.add hb
  | monomial k c =>
    have h1 : (fun u : ℝ => (Polynomial.monomial k c).eval (u : ℂ)⁻¹) =
        fun u : ℝ => c * (u : ℂ)⁻¹ ^ k := by
      funext u; simp [Polynomial.eval_monomial]
    have h2 : ((Polynomial.monomial k c : Polynomial ℂ) : PowerSeries ℂ) =
        PowerSeries.C c * (PowerSeries.X : PowerSeries ℂ) ^ k := by
      rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
        Polynomial.coe_pow, Polynomial.coe_X]
    rw [h1, h2]
    exact (HasAsympExp.const c).mul (HasAsympExp.inv_pow k)

/-- All-orders `1/u` asymptotic expansion of non-autonomous polynomial differential expressions
in `w = 1/u`. -/
lemma HasAsympExp.mvPolynomial_evalW {r : ℕ}
    {f : Fin (r + 1) → ℝ → ℂ} {S : Fin (r + 1) → PowerSeries ℂ}
    (hf : ∀ j, HasAsympExp (f j) (S j))
    (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) :
    HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => f j u) (evalU Q (u : ℂ)⁻¹))
      (MvPolynomial.eval₂ Polynomial.coeToPowerSeries.ringHom S Q) := by
  induction Q using MvPolynomial.induction_on with
  | C q =>
    have h1 : (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => f j u)
        (evalU (MvPolynomial.C q) (u : ℂ)⁻¹)) = fun u : ℝ => q.eval (u : ℂ)⁻¹ := by
      funext u; simp [evalU]
    rw [h1, MvPolynomial.eval₂_C, Polynomial.coeToPowerSeries.ringHom_apply]
    exact HasAsympExp.poly_inv q
  | add A B hA hB =>
    have h1 : (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => f j u)
        (evalU (A + B) (u : ℂ)⁻¹)) = fun u =>
        MvPolynomial.eval (fun j : Fin (r + 1) => f j u) (evalU A (u : ℂ)⁻¹) +
          MvPolynomial.eval (fun j : Fin (r + 1) => f j u) (evalU B (u : ℂ)⁻¹) := by
      funext u; simp only [evalU, map_add]
    rw [h1, MvPolynomial.eval₂_add]
    exact hA.add hB
  | mul_X A j hA =>
    have h1 : (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => f j u)
        (evalU (A * MvPolynomial.X j) (u : ℂ)⁻¹)) = fun u =>
        MvPolynomial.eval (fun j : Fin (r + 1) => f j u) (evalU A (u : ℂ)⁻¹) * f j u := by
      funext u; simp only [evalU, map_mul, MvPolynomial.map_X, MvPolynomial.eval_X]
    rw [h1, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact hA.mul (hf j)

/-- Evaluation of `RatFunc ℂ` at `u : ℂ` as `num.eval u / denom.eval u`. -/
@[expose] def ratEval (q : RatFunc ℂ) (u : ℂ) : ℂ :=
  q.num.eval u / q.denom.eval u

/-- Evaluation of the rational coefficients `P ∈ ℂ(u)[Y_0,...,Y_r]` at `u : ℂ`. -/
@[expose] def evalRatU {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) (u : ℂ) :
    MvPolynomial (Fin (r + 1)) ℂ :=
  ∑ α ∈ P.support, MvPolynomial.monomial α (ratEval (P.coeff α) u)

private lemma poly_eval_eventually_ne_zero {q : Polynomial ℂ} (hq : q ≠ 0) :
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

private lemma evalU_clearDenomMvPoly {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) {u : ℂ}
    (hu : ∀ β ∈ P.support, (P.coeff β).denom.eval u ≠ 0) :
    evalU (clearDenomMvPoly P) u = (clearDenomPoly P).eval u • evalRatU P u := by
  classical
  ext α
  rw [evalU, MvPolynomial.coeff_map, Polynomial.coe_evalRingHom, clearDenomMvPoly_coeff,
    MvPolynomial.coeff_smul, smul_eq_mul, evalRatU, MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hα : α ∈ P.support
  · rw [Finset.sum_eq_single α]
    · simp only [↓reduceIte, ratEval, clearDenomPoly, Polynomial.eval_prod]
      rw [← Finset.mul_prod_erase P.support (fun β => (P.coeff β).denom.eval u) hα,
        Polynomial.eval_mul, Polynomial.eval_prod]
      field_simp [hu α hα]
    · intro β _ hβα; simp [hβα]
    · intro hnot; exact absurd hα hnot
  · have hP0 : P.coeff α = 0 := MvPolynomial.notMem_support_iff.mp hα
    rw [hP0, RatFunc.num_zero, zero_mul, Polynomial.eval_zero, Finset.sum_eq_zero]
    · simp
    · intro β hβ
      rw [ite_eq_right_iff]
      intro hβα
      subst hβα
      exact absurd hβ hα

/-- **Asymptotic-Transfer Higher-Order Non-Autonomous Theorem (`ℂ[u]`)**:
Any function `f : ℝ → ℂ` sharing the all-orders `1/u` asymptotic expansion `d_u^[j] (formalSeries φ)`
satisfies NO nonzero non-autonomous polynomial differential equation over `ℂ[u]`. -/
theorem no_nonautonomous_ade_of_higher_order_borel
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp)
    {f : ℝ → ℂ}
    (hf_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j f) (d_u^[j] (formalSeries φ)))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) (evalU P (u : ℂ)) = 0) :
    P = 0 := by
  let N := maxUDeg P
  let Q := revMvPoly N P
  have hNP : ∀ α, (P.coeff α).natDegree ≤ N := natDegree_le_maxUDeg P
  have hexp : HasAsympExp
      (fun u : ℝ =>
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) (evalU Q (u : ℂ)⁻¹))
      (formalEvalW (formalSeries φ) Q) :=
    HasAsympExp.mvPolynomial_evalW (fun j => hf_asymp j.val) Q
  have hflat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in Filter.atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u)
        (evalU Q (u : ℂ)⁻¹)‖ ≤ C / u ^ M := by
    intro M
    refine ⟨0, ?_⟩
    filter_upwards [hP, eventually_gt_atTop (0 : ℝ)] with u hu hu_pos
    have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    rw [show Q = revMvPoly N P from rfl, evalU_revMvPoly P hNP hu_ne,
      MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, hu, mul_zero, norm_zero, zero_div]
  have hW0 : formalEvalW (formalSeries φ) Q = 0 := hexp.eq_zero_of_flat hflat
  exact higher_order_stokes_vandermonde_no_ade h P
    ((formalEvalW_eq_zero_iff_formalEvalPoly (formalSeries φ) P hNP).mp hW0)

/-- **Asymptotic-Transfer Higher-Order Non-Autonomous Theorem (`ℂ(u)`)**:
Any function `f : ℝ → ℂ` sharing the all-orders `1/u` asymptotic expansion `d_u^[j] (formalSeries φ)`
satisfies NO nonzero non-autonomous rational-coefficient differential equation over `ℂ(u)`. -/
theorem no_rat_ade_of_higher_order_borel
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp)
    {f : ℝ → ℂ}
    (hf_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j f) (d_u^[j] (formalSeries φ)))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) (evalRatU P (u : ℂ)) = 0) :
    P = 0 := by
  have hden : ∀ᶠ u : ℝ in Filter.atTop, ∀ β ∈ P.support, (P.coeff β).denom.eval (u : ℂ) ≠ 0 :=
    (Filter.eventually_all_finset P.support).mpr fun β _ =>
      poly_eval_eventually_ne_zero (RatFunc.denom_ne_zero _)
  have hP_clear : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u)
        (evalU (clearDenomMvPoly P) (u : ℂ)) = 0 := by
    filter_upwards [hP, hden] with u hu hdu
    rw [evalU_clearDenomMvPoly P hdu, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, hu,
      mul_zero]
  exact (clearDenomMvPoly_eq_zero_iff P).mp
    (no_nonautonomous_ade_of_higher_order_borel h hf_asymp (clearDenomMvPoly P) hP_clear)

/-- **Asymptotic-Transfer Autonomous Corollary**:
Any function `f : ℝ → ℂ` sharing `d_u^[j] (formalSeries φ)` satisfies NO nonzero autonomous
polynomial differential equation over `ℂ`. -/
theorem no_autonomous_ade_of_higher_order_borel
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp)
    {f : ℝ → ℂ}
    (hf_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j f) (d_u^[j] (formalSeries φ)))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) P = 0) :
    P = 0 := by
  have hexp : HasAsympExp
      (fun u => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) P)
      (formalEval (formalSeries φ) P) :=
    HasAsympExp.mvPolynomial (fun j => hf_asymp j.val) P
  have hflat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in Filter.atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) P‖ ≤ C / u ^ M := by
    intro M
    refine ⟨0, ?_⟩
    filter_upwards [hP] with u hu
    simp [hu]
  exact higher_order_stokes_vandermonde_no_autonomous_ade h P (hexp.eq_zero_of_flat hflat)

/-! ### 7. Tier-1 Non-Vacuity Instantiations: Double-Pole Trigamma, Triple-Pole, and Lambert Divisor Series -/

/-- General Dirichlet-pole Borel transform `∑_{n ≥ 1} c(n) / (e^{i θ₀} n - z)^p`. -/
@[expose] def dirichletPoleSeries (c : ℕ → ℂ) (θ₀ : ℝ) (p : ℕ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - z) ^ p

private lemma dirichletPole_tail_diff_norm_ge (θ₀ : ℝ) (w₀ : ℂ) (R : ℝ) :
    ∃ N : ℕ, ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w₀ R →
      ((k + N + 1 : ℕ) : ℝ) / 2 ≤
        ‖Complex.exp (I * (θ₀ : ℂ)) * ((k + N + 1 : ℕ) : ℂ) - z‖ := by
  let N : ℕ := Nat.ceil (2 * (‖w₀‖ + R))
  refine ⟨N, fun k z hz => ?_⟩
  have hN : 2 * (‖w₀‖ + R) ≤ (N : ℝ) := Nat.le_ceil _
  have hM : 2 * (‖w₀‖ + R) ≤ ((k + N + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [show (0 : ℝ) ≤ (k : ℝ) by positivity]
  have hz_norm : ‖z‖ ≤ ‖w₀‖ + R := by
    have hball : ‖z - w₀‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    calc ‖z‖ = ‖(z - w₀) + w₀‖ := by ring_nf
      _ ≤ ‖z - w₀‖ + ‖w₀‖ := norm_add_le _ _
      _ ≤ R + ‖w₀‖ := by linarith
      _ = ‖w₀‖ + R := by ring
  have hexp_norm : ‖Complex.exp (I * (θ₀ : ℂ))‖ = 1 := by
    rw [show I * (θ₀ : ℂ) = (θ₀ : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I θ₀
  have hterm_norm :
      ‖Complex.exp (I * (θ₀ : ℂ)) * ((k + N + 1 : ℕ) : ℂ)‖ = ((k + N + 1 : ℕ) : ℝ) := by
    rw [norm_mul, hexp_norm, one_mul, Complex.norm_natCast]
  have htri := norm_add_le (Complex.exp (I * (θ₀ : ℂ)) * ((k + N + 1 : ℕ) : ℂ) - z) z
  rw [sub_add_cancel, hterm_norm] at htri
  linarith

private lemma dirichletPole_term_norm_le_half {c : ℕ → ℂ} {θ₀ : ℝ} {p : ℕ}
    {z : ℂ} {n : ℕ}
    (hge : ((n + 1 : ℕ) : ℝ) / 2 ≤
      ‖Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - z‖) :
    ‖c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - z) ^ p‖ ≤
      (2 : ℝ) ^ p * (‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p) := by
  have hMpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h1 :
      ‖c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - z) ^ p‖ ≤
        ‖c (n + 1)‖ / (((n + 1 : ℕ) : ℝ) / 2) ^ p := by
    rw [norm_div, norm_pow]; gcongr
  refine h1.trans_eq ?_
  rw [div_pow]
  field_simp [pow_ne_zero p hMpos.ne']

private lemma dirichletPole_tail_summable {c : ℕ → ℂ} {θ₀ : ℝ} {p : ℕ}
    (hsumm : Summable (fun n : ℕ => ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p))
    (N : ℕ) {z : ℂ}
    (hge : ∀ k : ℕ, ((k + N + 1 : ℕ) : ℝ) / 2 ≤
      ‖Complex.exp (I * (θ₀ : ℂ)) * ((k + N + 1 : ℕ) : ℂ) - z‖) :
    Summable (fun k : ℕ =>
      c (k + N + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((k + N + 1 : ℕ) : ℂ) - z) ^ p) := by
  have hdom : Summable (fun k : ℕ => (2 : ℝ) ^ p * (‖c (k + N + 1)‖ / ((k + N + 1 : ℕ) : ℝ) ^ p)) :=
    ((summable_nat_add_iff N).2 hsumm).mul_left ((2 : ℝ) ^ p)
  exact hdom.of_norm_bounded fun k => dirichletPole_term_norm_le_half (hge k)

private lemma norm_nat_sub_exp_mul_real_ge (θ₀ σ : ℝ) (n : ℕ) (v : ℝ) :
    |((n + 1 : ℕ) : ℝ) * Real.sin σ| ≤
      ‖Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
        Complex.exp (I * ((θ₀ + σ : ℝ) : ℂ)) * (v : ℂ)‖ := by
  let μ₀ : ℂ := Complex.exp (I * (θ₀ : ℂ))
  have hμ₀_norm : ‖μ₀‖ = 1 := by
    dsimp only [μ₀]
    rw [show I * (θ₀ : ℂ) = (θ₀ : ℂ) * I by ring]
    exact Complex.norm_exp_ofReal_mul_I θ₀
  have hfactor :
      μ₀ * ((n + 1 : ℕ) : ℂ) - Complex.exp (I * ((θ₀ + σ : ℝ) : ℂ)) * (v : ℂ) =
        μ₀ * (((n + 1 : ℕ) : ℂ) - Complex.exp (I * (σ : ℂ)) * (v : ℂ)) := by
    have hexp : Complex.exp (I * ((θ₀ + σ : ℝ) : ℂ)) = μ₀ * Complex.exp (I * (σ : ℂ)) := by
      dsimp only [μ₀]; rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp]; ring
  rw [hfactor, norm_mul, hμ₀_norm, one_mul]
  let x : ℝ := ((n + 1 : ℕ) : ℝ)
  let w : ℂ := (x : ℂ) - Complex.exp (I * (σ : ℂ)) * (v : ℂ)
  have hexp_σ : Complex.exp (I * (σ : ℂ)) = Complex.exp ((σ : ℂ) * I) := by congr 1; ring
  have hw_re : w.re = x - Real.cos σ * v := by
    dsimp only [w]
    rw [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, hexp_σ,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hw_im : w.im = -(Real.sin σ * v) := by
    dsimp only [w]
    rw [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, hexp_σ,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, zero_sub]
  have h_nsq : (x * Real.sin σ) ^ 2 ≤ Complex.normSq w := by
    rw [Complex.normSq_apply, hw_re, hw_im]
    have hid := Real.sin_sq_add_cos_sq σ
    have hid' : (x - Real.cos σ * v) * (x - Real.cos σ * v) +
        (-(Real.sin σ * v)) * (-(Real.sin σ * v)) =
        (v - x * Real.cos σ) ^ 2 + (x * Real.sin σ) ^ 2 +
          (v ^ 2 - x ^ 2) * (Real.sin σ ^ 2 + Real.cos σ ^ 2 - 1) := by ring
    rw [hid', hid, sub_self, mul_zero, add_zero]
    linarith [sq_nonneg (v - x * Real.cos σ)]
  change |x * Real.sin σ| ≤ ‖w‖
  rw [Complex.norm_def]
  refine Real.le_sqrt_of_sq_le ?_
  rw [sq_abs]
  exact h_nsq

/-- **General Higher-Order Borel Witness (`dirichletPoleSeries`)**:
Any convergent series `∑_{n ≥ 1} c(n) / (e^{i θ₀} n - z)^p` with `p ≥ 2` and `c n ≠ 0`
satisfies all hypotheses of `HigherOrderBorelData` with poles `ω m = m + 1` of exact order `p`,
wedge half-angle `α₀ = π/4`, flanking rays `θ = π/6`, and leading principal part `(-1)^p c(m+1)`. -/
def dirichletPoleSeries_borelData
    (c : ℕ → ℂ) (θ₀ : ℝ) (p : ℕ) (hp : 2 ≤ p)
    (hc_ne : ∀ n : ℕ, 1 ≤ n → c n ≠ 0)
    (hsumm : Summable (fun n : ℕ => ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p)) :
    HigherOrderBorelData (dirichletPoleSeries c θ₀ p) θ₀
      (fun m : ℕ => (m + 1 : ℝ)) (fun _ : ℕ => p)
      (fun m s => if s = p then (-1 : ℂ) ^ p * c (m + 1) else 0) where
  α₀ := Real.pi / 4
  θ := Real.pi / 6
  ε := 1 / 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by norm_num
  ω_pos := by norm_num
  ω_mono := fun a b hab => by dsimp only; exact_mod_cast Nat.succ_lt_succ hab
  ord_pos := fun _ => by omega
  pp_lead_ne_zero := fun m => by
    simp only [↓reduceIte]
    exact mul_ne_zero (pow_ne_zero p (by norm_num)) (hc_ne (m + 1) (by omega))
  analyticOn := fun w hw => by
    obtain ⟨N, hN⟩ := dirichletPole_tail_diff_norm_ge θ₀ w 1
    let head : ℂ → ℂ := fun z =>
      ∑ n ∈ Finset.range N, c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - z) ^ p
    let tail : ℂ → ℂ := fun z =>
      ∑' k : ℕ, c (k + N + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((k + N + 1 : ℕ) : ℂ) - z) ^ p
    have htail_diff : DifferentiableOn ℂ tail (Metric.ball w 1) := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun k : ℕ => (2 : ℝ) ^ p * (‖c (k + N + 1)‖ / ((k + N + 1 : ℕ) : ℝ) ^ p))
        (((summable_nat_add_iff N).2 hsumm).mul_left _) (fun k => ?_) Metric.isOpen_ball
        (fun k z hz => dirichletPole_term_norm_le_half (hN k z hz))
      refine DifferentiableOn.div (differentiableOn_const _)
        (((differentiableOn_const _).sub differentiableOn_id).pow p) fun z hz => ?_
      have hne_base : Complex.exp (I * (θ₀ : ℂ)) * ((k + N + 1 : ℕ) : ℂ) - z ≠ 0 := by
        intro h0
        have hnorm0 := hN k z hz
        rw [h0, norm_zero] at hnorm0
        linarith [show (0 : ℝ) < ((k + N + 1 : ℕ) : ℝ) / 2 by positivity]
      exact pow_ne_zero p hne_base
    have htail_ana : AnalyticAt ℂ tail w :=
      (htail_diff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self zero_lt_one)
    have hhead_ana : AnalyticAt ℂ head w := by
      refine Finset.analyticAt_fun_sum (Finset.range N) fun n _ => ?_
      refine AnalyticAt.div analyticAt_const
        ((analyticAt_const.sub analyticAt_id).pow p) ?_
      have hw_avoid : Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - w ≠ 0 := by
        intro h0
        apply hw.2
        refine ⟨n, ?_⟩
        have hweq : w = Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) := by
          linear_combination -h0
        rw [hweq]
        simp only [← mul_assoc, ← Complex.exp_add]
        have hzero : -I * (θ₀ : ℂ) + I * (θ₀ : ℂ) = 0 := by ring
        rw [hzero, Complex.exp_zero, one_mul]
        push_cast; rfl
      exact pow_ne_zero p hw_avoid
    have heq_ball : ∀ z ∈ Metric.ball w 1, dirichletPoleSeries c θ₀ p z = head z + tail z := by
      intro z hz
      have hts := dirichletPole_tail_summable hsumm N fun k => hN k z hz
      have hsum_all := (summable_nat_add_iff
        (f := fun n : ℕ => c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - z) ^ p)
        N).1 hts
      simpa only [dirichletPoleSeries, head, tail] using (hsum_all.sum_add_tsum_nat_add N).symm
    have hev : dirichletPoleSeries c θ₀ p =ᶠ[𝓝 w] fun z => head z + tail z :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
        heq_ball
    exact (hhead_ana.add htail_ana).congr hev.symm
  pole_principalPart := fun m => by
    let z_m : ℂ := Complex.exp (I * (θ₀ : ℂ)) * ((m + 1 : ℝ) : ℂ)
    have hz_m_eq : z_m = Complex.exp (I * (θ₀ : ℂ)) * ((m + 1 : ℕ) : ℂ) := by
      dsimp only [z_m]; push_cast; rfl
    obtain ⟨N₀, hN₀⟩ := dirichletPole_tail_diff_norm_ge θ₀ z_m (1 / 2)
    let N₁ : ℕ := max N₀ (m + 1)
    have hN₁ : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball z_m (1 / 2) →
        ((k + N₁ + 1 : ℕ) : ℝ) / 2 ≤
          ‖Complex.exp (I * (θ₀ : ℂ)) * ((k + N₁ + 1 : ℕ) : ℂ) - z‖ := by
      intro k z hz
      have hk := hN₀ (k + (N₁ - N₀)) z hz
      have hidx : k + (N₁ - N₀) + N₀ + 1 = k + N₁ + 1 := by omega
      simpa only [hidx] using hk
    let mid : ℂ → ℂ := fun z =>
      ∑ n ∈ (Finset.range N₁).erase m,
        c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - z) ^ p
    let tail : ℂ → ℂ := fun z =>
      ∑' k : ℕ, c (k + N₁ + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((k + N₁ + 1 : ℕ) : ℂ) - z) ^ p
    have htail_diff : DifferentiableOn ℂ tail (Metric.ball z_m (1 / 2)) := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun k : ℕ => (2 : ℝ) ^ p * (‖c (k + N₁ + 1)‖ / ((k + N₁ + 1 : ℕ) : ℝ) ^ p))
        (((summable_nat_add_iff N₁).2 hsumm).mul_left _) (fun k => ?_) Metric.isOpen_ball
        (fun k z hz => dirichletPole_term_norm_le_half (hN₁ k z hz))
      refine DifferentiableOn.div (differentiableOn_const _)
        (((differentiableOn_const _).sub differentiableOn_id).pow p) fun z hz => ?_
      have hne_base : Complex.exp (I * (θ₀ : ℂ)) * ((k + N₁ + 1 : ℕ) : ℂ) - z ≠ 0 := by
        intro h0
        have hnorm0 := hN₁ k z hz
        rw [h0, norm_zero] at hnorm0
        linarith [show (0 : ℝ) < ((k + N₁ + 1 : ℕ) : ℝ) / 2 by positivity]
      exact pow_ne_zero p hne_base
    have htail_cont : ContinuousAt tail z_m :=
      (htail_diff.differentiableAt (Metric.isOpen_ball.mem_nhds
        (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))).continuousAt
    have hmid_ana : AnalyticAt ℂ mid z_m := by
      refine Finset.analyticAt_fun_sum ((Finset.range N₁).erase m) fun n hn => ?_
      have hnm : n ≠ m := (Finset.mem_erase.mp hn).1
      refine AnalyticAt.div analyticAt_const ((analyticAt_const.sub analyticAt_id).pow p) ?_
      have hne_base : Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - z_m ≠ 0 := by
        rw [hz_m_eq, ← mul_sub]
        refine mul_ne_zero (Complex.exp_ne_zero _) ?_
        intro hsub
        have hcast : ((n + 1 : ℕ) : ℂ) = ((m + 1 : ℕ) : ℂ) := sub_eq_zero.mp hsub
        have : n + 1 = m + 1 := by exact_mod_cast hcast
        exact hnm (by omega)
      exact pow_ne_zero p hne_base
    have hmid_cont : ContinuousAt mid z_m := hmid_ana.continuousAt
    have hball : Metric.ball z_m (1 / 2) \ {z_m} ∈ 𝓝[≠] z_m := by
      rw [Set.sdiff_eq, Set.inter_comm]
      exact inter_mem_nhdsWithin _
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)))
    have heq_within :
        (fun z : ℂ => dirichletPoleSeries c θ₀ p z -
          ∑ s ∈ Finset.Icc 1 p,
            (if s = p then (-1 : ℂ) ^ p * c (m + 1) else 0) / (z - z_m) ^ s) =ᶠ[𝓝[≠] z_m]
          fun z => mid z + tail z := by
      filter_upwards [hball] with z ⟨hz_ball, hz_ne⟩
      have hts := dirichletPole_tail_summable hsumm N₁ fun k => hN₁ k z hz_ball
      have hsum_all := (summable_nat_add_iff
        (f := fun n : ℕ => c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - z) ^ p)
        N₁).1 hts
      have hdir_eq : dirichletPoleSeries c θ₀ p z =
          c (m + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((m + 1 : ℕ) : ℂ) - z) ^ p +
            mid z + tail z := by
        have hsplit := (hsum_all.sum_add_tsum_nat_add N₁).symm
        have hm_mem : m ∈ Finset.range N₁ := Finset.mem_range.mpr (by omega)
        have her := (Finset.add_sum_erase (Finset.range N₁)
          (fun n => c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) - z) ^ p)
          hm_mem).symm
        rw [dirichletPoleSeries, hsplit, her, add_assoc]
      have hpp_eq :
          (∑ s ∈ Finset.Icc 1 p,
              (if s = p then (-1 : ℂ) ^ p * c (m + 1) else 0) / (z - z_m) ^ s) =
            c (m + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((m + 1 : ℕ) : ℂ) - z) ^ p := by
        have hIcc :
            ∑ s ∈ Finset.Icc 1 p,
              (if s = p then (-1 : ℂ) ^ p * c (m + 1) else 0) / (z - z_m) ^ s =
              ∑ s ∈ Finset.Icc 1 p,
                if s = p then ((-1 : ℂ) ^ p * c (m + 1)) / (z - z_m) ^ p else 0 := by
          refine Finset.sum_congr rfl fun s _ => ?_
          split_ifs with hsp
          · subst hsp; rfl
          · simp
        rw [hIcc, Finset.sum_ite_eq']
        have hp_mem : p ∈ Finset.Icc 1 p := Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
        rw [ite_eq_left_iff.mpr fun hnot => absurd hp_mem hnot, ← hz_m_eq]
        have hsign : (z_m - z) ^ p = (-1 : ℂ) ^ p * (z - z_m) ^ p := by
          rw [show z_m - z = (-1 : ℂ) * (z - z_m) by ring, mul_pow]
        have hpow_neg : ((-1 : ℂ) ^ p) ^ 2 = 1 := by
          rw [← pow_mul, mul_comm p 2, pow_mul]; norm_num
        have hz_sub : z - z_m ≠ 0 := sub_ne_zero.mpr hz_ne
        rw [hsign]
        field_simp [pow_ne_zero p hz_sub, pow_ne_zero p (by norm_num : (-1 : ℂ) ≠ 0)]
        rw [hpow_neg, one_mul]
      rw [hdir_eq, hpp_eq]
      ring
    refine ⟨mid z_m + tail z_m, ?_⟩
    exact ((hmid_cont.add htail_cont).continuousWithinAt.tendsto).congr' heq_within.symm
  expType_plus := by
    refine ⟨(2 : ℝ) ^ p * ∑' n : ℕ, ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p, 0,
      by positivity, le_rfl, fun v _ => ?_⟩
    have hge : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) / 2 ≤
        ‖Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
          Complex.exp (I * ((θ₀ + Real.pi / 6 : ℝ) : ℂ)) * (v : ℂ)‖ := by
      intro n
      have h1 := norm_nat_sub_exp_mul_real_ge θ₀ (Real.pi / 6) n v
      have hsin : |((n + 1 : ℕ) : ℝ) * Real.sin (Real.pi / 6)| = ((n + 1 : ℕ) : ℝ) / 2 := by
        rw [Real.sin_pi_div_six, abs_of_pos (by positivity)]
        ring
      exact hsin.symm.trans_le h1
    have hdom_summ : Summable (fun n : ℕ => (2 : ℝ) ^ p * (‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p)) :=
      hsumm.mul_left ((2 : ℝ) ^ p)
    have hterm_bd : ∀ n : ℕ,
        ‖c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
          Complex.exp (I * ((θ₀ + Real.pi / 6 : ℝ) : ℂ)) * (v : ℂ)) ^ p‖ ≤
          (2 : ℝ) ^ p * (‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p) :=
      fun n => dirichletPole_term_norm_le_half (hge n)
    have hsumm_norm : Summable (fun n : ℕ =>
        ‖c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
          Complex.exp (I * ((θ₀ + Real.pi / 6 : ℝ) : ℂ)) * (v : ℂ)) ^ p‖) :=
      hdom_summ.of_norm_bounded fun n => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hterm_bd n
    have hnorm_μ : ‖Complex.exp (I * ((θ₀ + Real.pi / 6 : ℝ) : ℂ))‖ = 1 := by
      rw [show I * ((θ₀ + Real.pi / 6 : ℝ) : ℂ) = ((θ₀ + Real.pi / 6 : ℝ) : ℂ) * I by ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [Minor.pull, norm_mul, hnorm_μ, one_mul, dirichletPoleSeries, zero_mul, Real.exp_zero, mul_one]
    calc ‖∑' n : ℕ, c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
            Complex.exp (I * ((θ₀ + Real.pi / 6 : ℝ) : ℂ)) * (v : ℂ)) ^ p‖
        ≤ ∑' n : ℕ, ‖c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
            Complex.exp (I * ((θ₀ + Real.pi / 6 : ℝ) : ℂ)) * (v : ℂ)) ^ p‖ :=
          norm_tsum_le_tsum_norm hsumm_norm
      _ ≤ ∑' n : ℕ, (2 : ℝ) ^ p * (‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p) :=
          hsumm_norm.tsum_le_tsum hterm_bd hdom_summ
      _ = (2 : ℝ) ^ p * ∑' n : ℕ, ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p := tsum_mul_left
  expType_minus := by
    refine ⟨(2 : ℝ) ^ p * ∑' n : ℕ, ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p, 0,
      by positivity, le_rfl, fun v _ => ?_⟩
    have hge : ∀ n : ℕ, ((n + 1 : ℕ) : ℝ) / 2 ≤
        ‖Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
          Complex.exp (I * ((θ₀ - Real.pi / 6 : ℝ) : ℂ)) * (v : ℂ)‖ := by
      intro n
      have h1 := norm_nat_sub_exp_mul_real_ge θ₀ (-Real.pi / 6) n v
      have hsin : |((n + 1 : ℕ) : ℝ) * Real.sin (-Real.pi / 6)| = ((n + 1 : ℕ) : ℝ) / 2 := by
        rw [show (-Real.pi / 6 : ℝ) = -(Real.pi / 6) by ring, Real.sin_neg, mul_neg, abs_neg,
          Real.sin_pi_div_six, abs_of_pos (by positivity)]
        ring
      have hsub : θ₀ + (-Real.pi / 6) = θ₀ - Real.pi / 6 := by ring
      rw [← hsub]
      exact hsin.symm.trans_le h1
    have hdom_summ : Summable (fun n : ℕ => (2 : ℝ) ^ p * (‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p)) :=
      hsumm.mul_left ((2 : ℝ) ^ p)
    have hterm_bd : ∀ n : ℕ,
        ‖c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
          Complex.exp (I * ((θ₀ - Real.pi / 6 : ℝ) : ℂ)) * (v : ℂ)) ^ p‖ ≤
          (2 : ℝ) ^ p * (‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p) :=
      fun n => dirichletPole_term_norm_le_half (hge n)
    have hsumm_norm : Summable (fun n : ℕ =>
        ‖c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
          Complex.exp (I * ((θ₀ - Real.pi / 6 : ℝ) : ℂ)) * (v : ℂ)) ^ p‖) :=
      hdom_summ.of_norm_bounded fun n => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]
        exact hterm_bd n
    have hnorm_μ : ‖Complex.exp (I * ((θ₀ - Real.pi / 6 : ℝ) : ℂ))‖ = 1 := by
      rw [show I * ((θ₀ - Real.pi / 6 : ℝ) : ℂ) = ((θ₀ - Real.pi / 6 : ℝ) : ℂ) * I by ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [Minor.pull, norm_mul, hnorm_μ, one_mul, dirichletPoleSeries, zero_mul, Real.exp_zero, mul_one]
    calc ‖∑' n : ℕ, c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
            Complex.exp (I * ((θ₀ - Real.pi / 6 : ℝ) : ℂ)) * (v : ℂ)) ^ p‖
        ≤ ∑' n : ℕ, ‖c (n + 1) / (Complex.exp (I * (θ₀ : ℂ)) * ((n + 1 : ℕ) : ℂ) -
            Complex.exp (I * ((θ₀ - Real.pi / 6 : ℝ) : ℂ)) * (v : ℂ)) ^ p‖ :=
          norm_tsum_le_tsum_norm hsumm_norm
      _ ≤ ∑' n : ℕ, (2 : ℝ) ^ p * (‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p) :=
          hsumm_norm.tsum_le_tsum hterm_bd hdom_summ
      _ = (2 : ℝ) ^ p * ∑' n : ℕ, ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p := tsum_mul_left

/-- Any Dirichlet-pole Borel transform `∑_{n ≥ 1} c(n) / (e^{i θ₀} n - z)^p` (`p ≥ 2`,
`c n ≠ 0`) defines a formal Laplace series satisfying NO nonzero non-autonomous polynomial ODE
over `ℂ[u]`. -/
theorem dirichletPoleSeries_no_nonautonomous_ade
    (c : ℕ → ℂ) (θ₀ : ℝ) (p : ℕ) (hp : 2 ≤ p)
    (hc_ne : ∀ n : ℕ, 1 ≤ n → c n ≠ 0)
    (hsumm : Summable (fun n : ℕ => ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries (dirichletPoleSeries c θ₀ p)) P = 0) :
    P = 0 :=
  higher_order_stokes_vandermonde_no_ade
    (dirichletPoleSeries_borelData c θ₀ p hp hc_ne hsumm) P hP

/-- Any Dirichlet-pole Borel transform `∑_{n ≥ 1} c(n) / (e^{i θ₀} n - z)^p` (`p ≥ 2`,
`c n ≠ 0`) defines a formal Laplace series satisfying NO nonzero non-autonomous rational ODE
over `ℂ(u)`. -/
theorem dirichletPoleSeries_no_rat_ade
    (c : ℕ → ℂ) (θ₀ : ℝ) (p : ℕ) (hp : 2 ≤ p)
    (hc_ne : ∀ n : ℕ, 1 ≤ n → c n ≠ 0)
    (hsumm : Summable (fun n : ℕ => ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries (dirichletPoleSeries c θ₀ p)) P = 0) :
    P = 0 :=
  higher_order_stokes_vandermonde_no_rat_ade
    (dirichletPoleSeries_borelData c θ₀ p hp hc_ne hsumm) P hP

private lemma summable_one_div_nat_succ_pow {p : ℕ} (hp : 2 ≤ p) :
    Summable (fun n : ℕ => ‖(1 : ℂ)‖ / ((n + 1 : ℕ) : ℝ) ^ p) := by
  have hlt : -(p : ℝ) < -1 := by
    have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  have h1 : Summable (fun n : ℕ => ((n : ℝ) ^ (-(p : ℝ)))) :=
    Real.summable_nat_rpow.mpr hlt
  have h2 := (summable_nat_add_iff 1).2 h1
  refine h2.congr fun n => ?_
  rw [norm_one, one_div, ← Real.rpow_natCast, ← Real.rpow_neg (Nat.cast_nonneg _)]

/-- **Tier-1 Witness 1 (Double-Pole Series)**:
`∑_{n ≥ 1} 1 / (n - z)^2`, genuine double-pole Borel transform (`ord m = 2`). -/
@[expose] def trigammaSeries : ℂ → ℂ :=
  dirichletPoleSeries (fun _ => 1) 0 2

/-- **Rotated Trigamma Double-Pole Series**: `∑_{n ≥ 1} 1 / (e^{i θ₀} n - z)^2`. -/
@[expose] def trigammaSeriesRot (θ₀ : ℝ) : ℂ → ℂ :=
  dirichletPoleSeries (fun _ => 1) θ₀ 2

/-- Genuine `HigherOrderBorelData` witness on `trigammaSeries` (`ord _ = 2`). -/
def trigammaSeries_borelData :
    HigherOrderBorelData trigammaSeries 0 (fun m : ℕ => (m + 1 : ℝ)) (fun _ => 2)
      (fun _ s => if s = 2 then 1 else 0) := by
  have hpp : (fun (_ : ℕ) s => if s = 2 then (-1 : ℂ) ^ 2 * 1 else 0) =
      (fun _ s => if s = 2 then (1 : ℂ) else 0) := by
    funext _ s; split_ifs <;> norm_num
  exact hpp ▸ dirichletPoleSeries_borelData (fun _ => 1) 0 2 le_rfl (fun _ _ => one_ne_zero)
    (summable_one_div_nat_succ_pow le_rfl)

/-- **Tier-1 Concrete Double-Pole Non-Autonomous Theorem (`trigammaSeries`, `ℂ[u]`)**:
The formal Laplace series of `ψ'(1 - z) = ∑_{n ≥ 1} 1 / (n - z)^2` satisfies NO nonzero
non-autonomous polynomial differential equation over `ℂ[u]`. -/
theorem trigammaSeries_no_nonautonomous_ade {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries trigammaSeries) P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_ade trigammaSeries_borelData P hP

/-- **Tier-1 Concrete Rotated Double-Pole Non-Autonomous Theorem (`trigammaSeriesRot θ₀`, `ℂ(u)`)**:
Along ANY rotated ray `e^{i θ₀}`, `∑_{n ≥ 1} 1 / (e^{i θ₀} n - z)^2` satisfies NO nonzero
non-autonomous rational differential equation over `ℂ(u)`. -/
theorem trigammaSeriesRot_no_rat_ade (θ₀ : ℝ) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries (trigammaSeriesRot θ₀)) P = 0) : P = 0 :=
  dirichletPoleSeries_no_rat_ade (fun _ => 1) θ₀ 2 le_rfl (fun _ _ => one_ne_zero)
    (summable_one_div_nat_succ_pow le_rfl) P hP

/-- **Tier-1 Asymptotic-Transfer Corollary on `trigammaSeries`**:
Any function `f : ℝ → ℂ` with all-orders asymptotic expansion `d_u^[j] (formalSeries trigammaSeries)`
satisfies NO nonzero non-autonomous polynomial ODE over `ℂ[u]`. -/
theorem trigammaSeries_no_nonautonomous_ade_of_asymp {f : ℝ → ℂ}
    (hf_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j f) (d_u^[j] (formalSeries trigammaSeries)))
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u) (evalU P (u : ℂ)) = 0) :
    P = 0 :=
  no_nonautonomous_ade_of_higher_order_borel trigammaSeries_borelData hf_asymp P hP

private lemma card_divisors_le_two_sqrt {n : ℕ} (hn : 1 ≤ n) :
    (Nat.divisors n).card ≤ 2 * Nat.sqrt n := by
  let S : Finset ℕ := Finset.Icc 1 (Nat.sqrt n)
  have hsub : Nat.divisors n ⊆ S ∪ S.image (fun k => n / k) := by
    intro d hd
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd_dvd : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hmul : n = d * (n / d) := (Nat.mul_div_cancel' hd_dvd).symm
    rcases Nat.le_sqrt_of_eq_mul hmul with h1 | h2
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hd_pos, h1⟩)
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n / d, ?_, ?_⟩)
      · have hq_pos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hd_dvd) hd_pos
        exact Finset.mem_Icc.mpr ⟨hq_pos, h2⟩
      · exact Nat.div_div_self hd_dvd (by omega)
  have hcard : (S ∪ S.image (fun k => n / k)).card ≤ 2 * S.card := by
    calc (S ∪ S.image (fun k => n / k)).card
        ≤ S.card + (S.image (fun k => n / k)).card := Finset.card_union_le _ _
      _ ≤ S.card + S.card := Nat.add_le_add_left Finset.card_image_le _
      _ = 2 * S.card := by omega
  have hS : S.card = Nat.sqrt n := by
    dsimp only [S]
    rw [Nat.card_Icc]
    omega
  exact (Finset.card_le_card hsub).trans (hcard.trans_eq (by rw [hS]))

private lemma summable_card_divisors_div_sq :
    Summable (fun n : ℕ => ‖((Nat.divisors (n + 1)).card : ℂ)‖ / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 2 * ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
    have h1 : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
      Real.summable_nat_rpow.mpr (by norm_num)
    exact ((summable_nat_add_iff 1).2 h1).mul_left 2
  refine hbase.of_norm_bounded fun n => ?_
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [Real.norm_of_nonneg (by positivity), Complex.norm_natCast]
  have hdiv : ((Nat.divisors (n + 1)).card : ℝ) ≤ 2 * ((Nat.sqrt (n + 1) : ℕ) : ℝ) := by
    exact_mod_cast card_divisors_le_two_sqrt (by omega : 1 ≤ n + 1)
  have hsqrt : ((Nat.sqrt (n + 1) : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.le_sqrt_of_sq_le ?_
    exact_mod_cast Nat.sqrt_le' (n + 1)
  have hrpow : ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2 =
      ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast ((n + 1 : ℕ) : ℝ) 2, ← Real.rpow_sub hpos]
    congr 1; norm_num
  calc ((Nat.divisors (n + 1)).card : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2
      ≤ (2 * ((Nat.sqrt (n + 1) : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ 2 := by gcongr
    _ ≤ (2 * ((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) / ((n + 1 : ℕ) : ℝ) ^ 2 := by gcongr
    _ = 2 * (((n + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by ring
    _ = 2 * ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [hrpow]

/-- **Tier-1 Witness 2 (Lambert Divisor Double-Pole Borel Series)**:
`∑_{n ≥ 1} d(n) / (e^{i θ₀} n - z)^2`, the rotated double-pole Borel transform associated with
the classical Lambert divisor series `L₀(q) = ∑_{n ≥ 1} d(n) q^n`. -/
@[expose] def lambertBorelSeries (θ₀ : ℝ) : ℂ → ℂ :=
  dirichletPoleSeries (fun n => ((Nat.divisors n).card : ℂ)) θ₀ 2

/-- Genuine `HigherOrderBorelData` witness on `lambertBorelSeries θ₀` with `ord _ = 2` and
leading principal coefficient `d(m + 1) ≠ 0`. -/
def lambertBorelSeries_borelData (θ₀ : ℝ) :
    HigherOrderBorelData (lambertBorelSeries θ₀) θ₀ (fun m : ℕ => (m + 1 : ℝ)) (fun _ => 2)
      (fun m s => if s = 2 then ((Nat.divisors (m + 1)).card : ℂ) else 0) := by
  have hc_ne : ∀ n : ℕ, 1 ≤ n → ((Nat.divisors n).card : ℂ) ≠ 0 := by
    intro n hn
    have hcard : 0 < (Nat.divisors n).card :=
      Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩⟩
    exact_mod_cast hcard.ne'
  have hpp : (fun m s => if s = 2 then (-1 : ℂ) ^ 2 * ((Nat.divisors (m + 1)).card : ℂ) else 0) =
      (fun m s => if s = 2 then ((Nat.divisors (m + 1)).card : ℂ) else 0) := by
    funext m s; split_ifs <;> norm_num
  exact hpp ▸ dirichletPoleSeries_borelData (fun n => ((Nat.divisors n).card : ℂ)) θ₀ 2 le_rfl
    hc_ne summable_card_divisors_div_sq

/-- **Tier-1 Lambert Divisor Non-Autonomous Differential Transcendence (`ℂ[u]`)**:
The formal Laplace series of `lambertBorelSeries θ₀` satisfies NO nonzero non-autonomous
polynomial differential equation over `ℂ[u]`. -/
theorem lambertBorelSeries_no_nonautonomous_ade (θ₀ : ℝ) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries (lambertBorelSeries θ₀)) P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_ade (lambertBorelSeries_borelData θ₀) P hP

/-- **Tier-1 Lambert Divisor Non-Autonomous Differential Transcendence (`ℂ(u)`)**:
The formal Laplace series of `lambertBorelSeries θ₀` satisfies NO nonzero non-autonomous
rational differential equation over `ℂ(u)`. -/
theorem lambertBorelSeries_no_rat_ade (θ₀ : ℝ) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : formalEvalRat (formalSeries (lambertBorelSeries θ₀)) P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_rat_ade (lambertBorelSeries_borelData θ₀) P hP

/-- **Tier-1 Witness 3 (Triple-Pole Rotated Series)**:
`∑_{n ≥ 1} 1 / (e^{i θ₀} n - z)^3`, genuine order-3 pole witness (`ord m = 3`). -/
@[expose] def triplePoleSeries (θ₀ : ℝ) : ℂ → ℂ :=
  dirichletPoleSeries (fun _ => 1) θ₀ 3

/-- Genuine `HigherOrderBorelData` witness on `triplePoleSeries θ₀` (`ord _ = 3`). -/
def triplePoleSeries_borelData (θ₀ : ℝ) :
    HigherOrderBorelData (triplePoleSeries θ₀) θ₀ (fun m : ℕ => (m + 1 : ℝ)) (fun _ => 3)
      (fun _ s => if s = 3 then (-1 : ℂ) else 0) := by
  have hpp : (fun (_ : ℕ) s => if s = 3 then (-1 : ℂ) ^ 3 * 1 else 0) =
      (fun _ s => if s = 3 then (-1 : ℂ) else 0) := by
    funext _ s; split_ifs <;> norm_num
  exact hpp ▸ dirichletPoleSeries_borelData (fun _ => 1) θ₀ 3 (by omega) (fun _ _ => one_ne_zero)
    (summable_one_div_nat_succ_pow (by omega))

/-- **Tier-1 Triple-Pole Non-Autonomous Differential Transcendence (`ℂ[u]`)**:
The formal Laplace series of `triplePoleSeries θ₀` satisfies NO nonzero non-autonomous
polynomial differential equation over `ℂ[u]`. -/
theorem triplePoleSeries_no_nonautonomous_ade (θ₀ : ℝ) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : formalEvalPoly (formalSeries (triplePoleSeries θ₀)) P = 0) : P = 0 :=
  higher_order_stokes_vandermonde_no_ade (triplePoleSeries_borelData θ₀) P hP

end
end PakPrimes.HigherOrderStokes
