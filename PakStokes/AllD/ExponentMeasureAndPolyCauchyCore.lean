module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.MeasureTheory.VectorMeasure.Defs
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp

/-! # Section 7 Exponent-Measure Rank Core & Komatsu Poly-Cauchy Exact Algebraic Core

Unconditional Lean 4 formalization from Mathlib (zero placeholders, standard foundations only)
of the algebraic, measure-theoretic, and analytic core of Paper #12 Section 7 (Theorem 7.2,
shift-band pushforward, and Corollary 7.3 on Komatsu's poly-Cauchy numbers of both kinds):

1. **Polynomial-Weight Linear Independence on Infinite Real Supports:**
   - `poly_ae_zero_imp_zero_of_infinite_support`: if a Borel measure `μ` on `ℝ` has infinite
     topological support `(μ.support).Infinite`, no nonzero complex (or real) polynomial vanishes
     `μ`-a.e.
   - `poly_weight_rank_infinite_support`: for any positive finite measure `μ` on `ℝ` with infinite
     support (and integrable powers through `J`), `{β ↦ β^j : 0 ≤ j ≤ J}` are `ℂ`-linearly
     independent in `Lp ℂ 1 μ` with exact `Module.finrank ℂ = J + 1`.
   - `poly_weight_rank_complexMeasure_infinite_support`: for any density-weighted complex Borel
     measure `g • μ` (`μ.withDensityᵥ g`) whose total-variation support
     `(μ.withDensity (fun x => ‖g x‖ₑ)).support` is infinite, the complex measures
     `{j ↦ μ.withDensityᵥ (fun β => β^j * g β) : 0 ≤ j ≤ J}` are `ℂ`-linearly independent in
     `ComplexMeasure ℝ` with exact `Module.finrank ℂ = J + 1`.
   - `poly_weight_rank_finite_support_le`: conversely, if `μ` is carried by a finite set `S`, the
     span dimension is bounded by `S.card`.

2. **Exponent-Atom Series `F_β(x) = ∑ (β)_n x^n`, Operator `T = x ∂ - 1/x`, and Shift-Band Pushforward:**
   - Defines `risingFact β n = (β)_n` (matching `ascPochhammer`), `expAtomPS β : PowerSeries K`,
     `expAtomLaurent β : LaurentSeries K`, the formal Laurent derivative `laurentDeriv`, and
     `laurentT = x ∂ - 1/x`.
   - Proves `(laurentT + β • id) (expAtomLaurent β) = -X⁻¹`, `laurentT_pow_expAtom`, the
     commuting operator product `annihOp`, and `finite_support_measure_annihilated`:
     `∏_i (T + β_i)` annihilates any finite linear combination `∑ c_i F_{β_i}` up to a Laurent
     polynomial in `1/x` (and polynomial-cleared D-finite identity on `PowerSeries K`).
   - Proves `shift_band_coeff_identity` (`F_β = 1 + x β F_{β+1}`), its `m`-step iteration
     `shift_band_iter_identity`, and the measure-integral pushforward identity
     `shift_band_measure_identity`.

3. **Komatsu's Poly-Cauchy Numbers — Complete Exact Algebraic Core (Corollary 7.3):**
   - `polyCauchy_log_density_moment`: proves directly from Mathlib's Lebesgue integral that for
     every `k ≥ 1` and `m : ℕ`,
     `∫ v in Set.Ioo (0 : ℝ) 1, v ^ m * ((-Real.log v) ^ (k - 1) / (k - 1)!) = 1 / (m + 1) ^ k`.
   - `cauchy_first_second_kind_relation`: defines the classical OGFs `cauchyFirstPS` (`C_1`) and
     `cauchySecondPS` (`C_2`) and proves the exact formal power series differential identity
     `C_1 = (1 + x) * C_2 + x^2 * C_2'`.
   - `polyCauchy_densities_poly_indep`, `polyCauchy_densities_poly_indep_of_not_both_one`,
     `polyCauchy_densities_both_one_relation`, and `polyCauchy_jet_span_finrank`: proves via
     two-endpoint analytic peeling at `u → 0⁺` and `u → 1⁻` (using `AnalyticAt.dslope` and
     `Real.analyticAt_log`) that every finite selection of `k ≥ 1` poly-Cauchy densities is
     linearly independent over `ℝ[u]`, losing **exactly one** dimension (jet rank
     `(S₁.card + S₂.card - 1) * (J + 1) + 1` vs `(S₁.card + S₂.card) * (J + 1)`) if and only if
     both `k = 1` kinds are present!
   - `polyCauchy_nonpos_dfinite_poly`: constructs the explicit monic degree-`ℓ` Euler polynomials
     `polyCauchyEulerPoly ℓ`, proves `(1 + v ∂_v)^ℓ e^v = P_ℓ(v) e^v`, and establishes the exact
     nonpositive-index identities `∑ (m + 1)^ℓ v^m / m! = P_ℓ(v) e^v` (both in `PowerSeries ℝ`
     and as convergent real `tsum`s, specialized to `v = ±log(1 + s)`).
-/

public section

namespace CubicTheta.AllD

open Filter MeasureTheory Polynomial Set
open scoped BigOperators Classical Topology

noncomputable section

/-! ### 1. Polynomial-Weight Linear Independence on Infinite Real Supports -/

section PolynomialWeightRank

private lemma lp_coeFn_finset_sum {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {ι : Type*} (s : Finset ι) (f : ι → Lp E 1 μ) :
    (∑ i ∈ s, f i : Lp E 1 μ) =ᵐ[μ] fun x => ∑ i ∈ s, (f i : α → E) x := by
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [Lp.coeFn_zero E 1 μ] with x hx
    simpa using hx
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hadd hih
    simp only [Pi.add_apply] at hadd
    rw [hadd, hih, Finset.sum_insert ha]

private lemma poly_eval_finset_sum {R ι : Type*} [CommSemiring R] (s : Finset ι)
    (f : ι → Polynomial R) (x : R) :
    (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x :=
  map_sum (Polynomial.evalRingHom x) f s

private lemma poly_finset_sum_coeff {R ι : Type*} [Semiring R] (s : Finset ι)
    (f : ι → Polynomial R) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n :=
  map_sum (Polynomial.lcoeff R n) f s

/-- If a Borel measure `μ` on `ℝ` has infinite topological support, then any complex polynomial
vanishing `μ`-almost everywhere is the zero polynomial. -/
theorem poly_ae_zero_imp_zero_of_infinite_support
    {μ : Measure ℝ} (hinf : μ.support.Infinite) {P : Polynomial ℂ}
    (hzero : ∀ᵐ (β : ℝ) ∂μ, P.eval (β : ℂ) = 0) : P = 0 := by
  by_contra hP
  let Z : Set ℝ := {β : ℝ | P.eval (β : ℂ) = 0}
  have hZ_fin : Z.Finite := by
    have hroots : ((P.roots.toFinset : Set ℂ)).Finite := Finset.finite_toSet _
    have hsub : Z ⊆ (Complex.ofReal : ℝ → ℂ) ⁻¹' (P.roots.toFinset : Set ℂ) := by
      intro β hβ
      simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact hβ
    exact (hroots.preimage (Complex.ofReal_injective.injOn)).subset hsub
  have hdiff : (μ.support \ Z).Nonempty := (hinf.sdiff hZ_fin).nonempty
  obtain ⟨x₀, hx₀_supp, hx₀_notZ⟩ := hdiff
  have hU_open : IsOpen Zᶜ := hZ_fin.isClosed.isOpen_compl
  have hU_nhds : Zᶜ ∈ 𝓝 x₀ := hU_open.mem_nhds hx₀_notZ
  have hpos : 0 < μ Zᶜ := (Measure.mem_support_iff_forall x₀).mp hx₀_supp Zᶜ hU_nhds
  have hnull : μ Zᶜ = 0 := by
    rw [ae_iff] at hzero
    exact hzero
  exact hpos.ne' hnull

/-- Real-polynomial counterpart: if `(μ.support).Infinite` and `P.eval β = 0` `μ`-a.e.,
then `P = 0`. -/
theorem realPoly_ae_zero_imp_zero_of_infinite_support
    {μ : Measure ℝ} (hinf : μ.support.Infinite) {P : Polynomial ℝ}
    (hzero : ∀ᵐ (β : ℝ) ∂μ, P.eval β = 0) : P = 0 := by
  by_contra hP
  let Z : Set ℝ := {β : ℝ | P.eval β = 0}
  have hZ_fin : Z.Finite := by
    have hroots : ((P.roots.toFinset : Set ℝ)).Finite := Finset.finite_toSet _
    have hsub : Z ⊆ (P.roots.toFinset : Set ℝ) := by
      intro β hβ
      simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP]
      exact hβ
    exact hroots.subset hsub
  obtain ⟨x₀, hx₀_supp, hx₀_notZ⟩ := (hinf.sdiff hZ_fin).nonempty
  have hpos : 0 < μ Zᶜ :=
    (Measure.mem_support_iff_forall x₀).mp hx₀_supp Zᶜ (hZ_fin.isClosed.isOpen_compl.mem_nhds hx₀_notZ)
  rw [ae_iff] at hzero
  exact hpos.ne' hzero

/-- **Polynomial-Weight Rank in `L^1(μ)` for Infinite Supports:**
If `μ` is a Borel measure on `ℝ` with infinite support such that `β ↦ (β : ℂ)^j` belongs to
`L^1(μ)` for `0 ≤ j ≤ J`, then `{β ↦ β^j : 0 ≤ j ≤ J}` are `ℂ`-linearly independent in
`Lp ℂ 1 μ` and span a subspace of exact dimension `J + 1`. -/
theorem poly_weight_rank_infinite_support
    {μ : Measure ℝ} (hinf : μ.support.Infinite) (J : ℕ)
    (hmem : ∀ j : Fin (J + 1), MemLp (fun β : ℝ => (β : ℂ) ^ (j : ℕ)) 1 μ) :
    LinearIndependent ℂ
      (fun j : Fin (J + 1) => (hmem j).toLp (fun β : ℝ => (β : ℂ) ^ (j : ℕ))) ∧
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range (fun j : Fin (J + 1) => (hmem j).toLp (fun β : ℝ => (β : ℂ) ^ (j : ℕ))))) =
      J + 1 := by
  let v : Fin (J + 1) → Lp ℂ 1 μ :=
    fun j => (hmem j).toLp (fun β : ℝ => (β : ℂ) ^ (j : ℕ))
  have hlin : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let P : Polynomial ℂ := ∑ j : Fin (J + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)
    have hsum_ae : ∀ᵐ (β : ℝ) ∂μ, (∑ j : Fin (J + 1), c j • v j : Lp ℂ 1 μ) β = P.eval (β : ℂ) := by
      have hae_fin : ∀ j : Fin (J + 1), ∀ᵐ (β : ℝ) ∂μ, (c j • v j) β = c j * (β : ℂ) ^ (j : ℕ) := by
        intro j
        filter_upwards [Lp.coeFn_smul (c j) (v j), (hmem j).coeFn_toLp] with β h1 h2
        rw [h1, Pi.smul_apply, h2, smul_eq_mul]
      have hsum_lp := lp_coeFn_finset_sum (Finset.univ : Finset (Fin (J + 1))) (fun j => c j • v j)
      have hall := ae_all_iff.mpr hae_fin
      filter_upwards [hsum_lp, hall] with β h1 h2
      rw [h1]
      dsimp [P]
      rw [poly_eval_finset_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [h2 j, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have hzero_ae : ∀ᵐ (β : ℝ) ∂μ, P.eval (β : ℂ) = 0 := by
      have h0 : (∑ j : Fin (J + 1), c j • v j : Lp ℂ 1 μ) =ᵐ[μ] 0 := by
        rw [hc]
        exact Lp.coeFn_zero ℂ 1 μ
      filter_upwards [hsum_ae, h0] with β h1 h2
      rw [← h1, h2]
      rfl
    have hP0 : P = 0 := poly_ae_zero_imp_zero_of_infinite_support hinf hzero_ae
    intro j
    have hcoeff := congrArg (fun Q : Polynomial ℂ => Q.coeff (j : ℕ)) hP0
    dsimp [P] at hcoeff
    rw [poly_finset_sum_coeff] at hcoeff
    rw [Finset.sum_eq_single j] at hcoeff
    · simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hcoeff
    · intro k _ hne
      have hne' : (j : ℕ) ≠ (k : ℕ) := fun h => hne (Fin.ext h.symm)
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne']
    · intro hnot; exact absurd (Finset.mem_univ j) hnot
  refine ⟨hlin, ?_⟩
  rw [finrank_span_eq_card hlin, Fintype.card_fin]

/-- **Polynomial-Weight Rank for Density-Weighted Complex Borel Measures:**
Let `μ` be a `SigmaFinite` Borel measure on `ℝ` and `g : ℝ → ℂ` be a measurable density such that
`β ↦ β^j * g β` is `μ`-integrable for all `0 ≤ j ≤ J`. If the total-variation measure
`μ_abs := μ.withDensity (fun x => ‖g x‖ₑ)` has infinite topological support, then the complex
measures `j ↦ μ.withDensityᵥ (fun β => (β : ℂ)^j * g β)` (`0 ≤ j ≤ J`) are `ℂ`-linearly
independent in `VectorMeasure ℝ ℂ` and span a subspace of exact dimension `J + 1`. -/
theorem poly_weight_rank_complexMeasure_infinite_support
    {μ : Measure ℝ} [SigmaFinite μ] {g : ℝ → ℂ} (J : ℕ)
    (hinf : (μ.withDensity (fun x => ‖g x‖ₑ)).support.Infinite)
    (hint : ∀ j : Fin (J + 1), Integrable (fun β : ℝ => (β : ℂ) ^ (j : ℕ) * g β) μ) :
    LinearIndependent ℂ
      (fun j : Fin (J + 1) => μ.withDensityᵥ (fun β : ℝ => (β : ℂ) ^ (j : ℕ) * g β)) ∧
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range (fun j : Fin (J + 1) =>
          μ.withDensityᵥ (fun β : ℝ => (β : ℂ) ^ (j : ℕ) * g β)))) =
      J + 1 := by
  let ν : Fin (J + 1) → VectorMeasure ℝ ℂ :=
    fun j => μ.withDensityᵥ (fun β : ℝ => (β : ℂ) ^ (j : ℕ) * g β)
  have hlin : LinearIndependent ℂ ν := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let P : Polynomial ℂ := ∑ j : Fin (J + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)
    let f : ℝ → ℂ := fun β => P.eval (β : ℂ) * g β
    have hf_eq : f = fun β : ℝ => ∑ j : Fin (J + 1), c j • ((β : ℂ) ^ (j : ℕ) * g β) := by
      funext β
      dsimp [f, P]
      rw [poly_eval_finset_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        mul_assoc]
    have hf_int : Integrable f μ := by
      rw [hf_eq]
      have hgen : ∀ t : Finset (Fin (J + 1)),
          Integrable (fun β : ℝ => ∑ j ∈ t, c j • ((β : ℂ) ^ (j : ℕ) * g β)) μ := by
        intro t
        induction t using Finset.induction_on with
        | empty => simp
        | insert a t ha ih =>
          have hfun : (fun β : ℝ => ∑ j ∈ insert a t, c j • ((β : ℂ) ^ (j : ℕ) * g β)) =
              (fun β : ℝ => c a • ((β : ℂ) ^ (a : ℕ) * g β)) +
              (fun β : ℝ => ∑ j ∈ t, c j • ((β : ℂ) ^ (j : ℕ) * g β)) := by
            funext β; simp [Finset.sum_insert ha]
          rw [hfun]
          exact ((hint a).smul (c a)).add ih
      exact hgen Finset.univ
    have hf_zero_set : ∀ s : Set ℝ, MeasurableSet s → μ s < ⊤ → ∫ β in s, f β ∂μ = 0 := by
      intro s hs _
      have h_eval := congrArg (fun M : VectorMeasure ℝ ℂ => M s) hc
      simp only [FunLike.coe_zero, Pi.zero_apply] at h_eval
      have hsum_apply :
          (∑ j : Fin (J + 1), c j • ν j) s = ∑ j : Fin (J + 1), c j • (ν j s) := by
        have hgen : ∀ (t : Finset (Fin (J + 1))),
            (∑ j ∈ t, c j • ν j) s = ∑ j ∈ t, c j • (ν j s) := by
          intro t
          induction t using Finset.induction_on with
          | empty => simp
          | insert a t ha ih =>
            rw [Finset.sum_insert ha, Finset.sum_insert ha]
            simp [ih]
        exact hgen Finset.univ
      rw [hsum_apply] at h_eval
      have hint_sum :
          ∫ β in s, f β ∂μ =
            ∑ j : Fin (J + 1), ∫ β in s, c j • ((β : ℂ) ^ (j : ℕ) * g β) ∂μ := by
        rw [hf_eq]
        have hgen : ∀ t : Finset (Fin (J + 1)),
            Integrable (fun β : ℝ => ∑ j ∈ t, c j • ((β : ℂ) ^ (j : ℕ) * g β)) (μ.restrict s) ∧
            ∫ β in s, (∑ j ∈ t, c j • ((β : ℂ) ^ (j : ℕ) * g β)) ∂μ =
              ∑ j ∈ t, ∫ β in s, c j • ((β : ℂ) ^ (j : ℕ) * g β) ∂μ := by
          intro t
          induction t using Finset.induction_on with
          | empty =>
            refine ⟨by simp, by simp⟩
          | insert a t ha ih =>
            have ha_int : Integrable (fun β : ℝ => c a • ((β : ℂ) ^ (a : ℕ) * g β))
                (μ.restrict s) := ((hint a).smul (c a)).integrableOn
            have hfun : (fun β : ℝ => ∑ j ∈ insert a t, c j • ((β : ℂ) ^ (j : ℕ) * g β)) =
                (fun β : ℝ => c a • ((β : ℂ) ^ (a : ℕ) * g β) +
                  ∑ j ∈ t, c j • ((β : ℂ) ^ (j : ℕ) * g β)) := by
              funext β; exact Finset.sum_insert ha
            refine ⟨?_, ?_⟩
            · rw [hfun]; exact ha_int.add ih.1
            · rw [hfun, integral_add ha_int ih.1, ih.2, Finset.sum_insert ha]
        exact (hgen Finset.univ).2
      rw [hint_sum]
      have hterm : ∀ j : Fin (J + 1),
          ∫ β in s, c j • ((β : ℂ) ^ (j : ℕ) * g β) ∂μ = c j • (ν j s) := by
        intro j
        rw [integral_smul]
        dsimp [ν]
        rw [withDensityᵥ_apply (hint j) hs]
      simp_rw [hterm]
      exact h_eval
    have hf_ae : f =ᵐ[μ] 0 :=
      ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
        (fun _ _ _ => hf_int.integrableOn) hf_zero_set
    have hP0 : P = 0 := by
      by_contra hP
      let Z : Set ℝ := {β : ℝ | P.eval (β : ℂ) = 0}
      have hZ_fin : Z.Finite := by
        have hroots : ((P.roots.toFinset : Set ℂ)).Finite := Finset.finite_toSet _
        have hsub : Z ⊆ (Complex.ofReal : ℝ → ℂ) ⁻¹' (P.roots.toFinset : Set ℂ) := by
          intro β hβ
          simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset,
            Polynomial.mem_roots hP]
          exact hβ
        exact (hroots.preimage (Complex.ofReal_injective.injOn)).subset hsub
      obtain ⟨x₀, hx₀_supp, hx₀_notZ⟩ := (hinf.sdiff hZ_fin).nonempty
      have hU_open : IsOpen Zᶜ := hZ_fin.isClosed.isOpen_compl
      have hpos : 0 < (μ.withDensity (fun x => ‖g x‖ₑ)) Zᶜ :=
        (Measure.mem_support_iff_forall x₀).mp hx₀_supp Zᶜ (hU_open.mem_nhds hx₀_notZ)
      rw [withDensity_apply _ hU_open.measurableSet] at hpos
      have hzero_on_U : ∀ᵐ (β : ℝ) ∂(μ.restrict Zᶜ), ‖g β‖ₑ = 0 := by
        have hf_rest : ∀ᵐ (β : ℝ) ∂(μ.restrict Zᶜ), f β = 0 := ae_restrict_of_ae hf_ae
        filter_upwards [hf_rest, ae_restrict_mem hU_open.measurableSet] with β hβ hU
        have hPβ : P.eval (β : ℂ) ≠ 0 := hU
        have hg0 : g β = 0 := (mul_eq_zero.mp hβ).resolve_left hPβ
        simp [hg0]
      have hlint0 : ∫⁻ β in Zᶜ, ‖g β‖ₑ ∂μ = 0 := by
        have h := lintegral_congr_ae hzero_on_U
        simpa using h
      exact hpos.ne' hlint0
    intro j
    have hcoeff := congrArg (fun Q : Polynomial ℂ => Q.coeff (j : ℕ)) hP0
    dsimp [P] at hcoeff
    rw [poly_finset_sum_coeff] at hcoeff
    rw [Finset.sum_eq_single j] at hcoeff
    · simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hcoeff
    · intro k _ hne
      have hne' : (j : ℕ) ≠ (k : ℕ) := fun h => hne (Fin.ext h.symm)
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne']
    · intro hnot; exact absurd (Finset.mem_univ j) hnot
  refine ⟨hlin, ?_⟩
  rw [finrank_span_eq_card hlin, Fintype.card_fin]

/-- Finite-support converse: if `μ` is carried by a finite set `S : Finset ℝ`, then the
`ℂ`-span of `{β ↦ β^j : 0 ≤ j ≤ J}` in `Lp ℂ 1 μ` has dimension at most `S.card`. -/
theorem poly_weight_rank_finite_support_le
    {μ : Measure ℝ} {S : Finset ℝ} (hS : μ (S : Set ℝ)ᶜ = 0) (J : ℕ)
    (hmem : ∀ j : Fin (J + 1), MemLp (fun β : ℝ => (β : ℂ) ^ (j : ℕ)) 1 μ) :
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range (fun j : Fin (J + 1) => (hmem j).toLp (fun β : ℝ => (β : ℂ) ^ (j : ℕ))))) ≤
      S.card := by
  let v : Fin (J + 1) → Lp ℂ 1 μ :=
    fun j => (hmem j).toLp (fun β : ℝ => (β : ℂ) ^ (j : ℕ))
  let W : Submodule ℂ (Lp ℂ 1 μ) := Submodule.span ℂ (Set.range v)
  let Φ : (Fin (J + 1) → ℂ) →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun c x => ∑ j : Fin (J + 1), c j * ((x.1 : ℝ) : ℂ) ^ (j : ℕ)
      map_add' := fun c₁ c₂ => by
        funext x; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  let Ψ : (Fin (J + 1) → ℂ) →ₗ[ℂ] Lp ℂ 1 μ :=
    { toFun := fun c => ∑ j : Fin (J + 1), c j • v j
      map_add' := fun c₁ c₂ => by
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hker : LinearMap.ker Φ ≤ LinearMap.ker Ψ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    dsimp [Ψ]
    apply Lp.ext_iff.mpr
    have hsum_lp := lp_coeFn_finset_sum (Finset.univ : Finset (Fin (J + 1))) (fun j => c j • v j)
    have hae_fin : ∀ j : Fin (J + 1), ∀ᵐ (β : ℝ) ∂μ, (c j • v j) β = c j * (β : ℂ) ^ (j : ℕ) := by
      intro j
      filter_upwards [Lp.coeFn_smul (c j) (v j), (hmem j).coeFn_toLp] with β h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    have hall := ae_all_iff.mpr hae_fin
    have hmemS : ∀ᵐ (β : ℝ) ∂μ, β ∈ (S : Set ℝ) := by
      rw [ae_iff]
      exact hS
    filter_upwards [hsum_lp, hall, hmemS, Lp.coeFn_zero ℂ 1 μ] with β h1 h2 hβ h0
    rw [h1, h0]
    have hsum_eq : (∑ j : Fin (J + 1), (c j • v j) β) =
        ∑ j : Fin (J + 1), c j * (β : ℂ) ^ (j : ℕ) :=
      Finset.sum_congr rfl fun j _ => h2 j
    rw [hsum_eq]
    exact congrFun hc ⟨β, hβ⟩
  have hrange : W = LinearMap.range Ψ := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      refine ⟨Pi.single j 1, ?_⟩
      dsimp [Ψ]
      rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hne; simp [Pi.single_eq_of_ne hne]
      · intro hnot; exact absurd (Finset.mem_univ j) hnot
    · rintro _ ⟨c, rfl⟩
      dsimp [Ψ]
      exact Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  change Module.finrank ℂ W ≤ S.card
  rw [hrange]
  have h1 : Module.finrank ℂ (LinearMap.range Ψ) ≤ Module.finrank ℂ (LinearMap.range Φ) := by
    have hΨ := LinearMap.finrank_range_add_finrank_ker Ψ
    have hΦ := LinearMap.finrank_range_add_finrank_ker Φ
    have hkle : Module.finrank ℂ (LinearMap.ker Φ) ≤ Module.finrank ℂ (LinearMap.ker Ψ) :=
      Submodule.finrank_mono hker
    omega
  have h2 : Module.finrank ℂ (LinearMap.range Φ) ≤ Module.finrank ℂ (S → ℂ) :=
    Submodule.finrank_le (LinearMap.range Φ)
  have h3 : Module.finrank ℂ (S → ℂ) = S.card := by
    rw [Module.finrank_pi, Fintype.card_coe]
  exact le_trans (le_trans h1 h2) (le_of_eq h3)

end PolynomialWeightRank

/-! ### 2. Exponent Atoms `F_β(x) = ∑ (β)_n x^n`, Operator `T = x ∂ - 1/x`, and Shift-Band Pushforward -/

section ExponentAtomOperators

/-- Rising factorial `(β)_n = β (β + 1) ... (β + n - 1)` in any commutative ring. -/
def risingFact {K : Type*} [CommRing K] (β : K) : ℕ → K
  | 0 => 1
  | n + 1 => (β + (n : K)) * risingFact β n

/-- `risingFact β n` agrees with `(ascPochhammer K n).eval β`. -/
theorem risingFact_eq_ascPochhammer {K : Type*} [CommRing K] (β : K) (n : ℕ) :
    risingFact β n = (ascPochhammer K n).eval β := by
  induction n with
  | zero => simp [risingFact, ascPochhammer]
  | succ k ih =>
    rw [risingFact, ih, ascPochhammer_succ_right, Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
    ring

/-- Shift identity `(β)_{n + 1} = β * (β + 1)_n` for all `β` and `n`. -/
theorem risingFact_succ_shift {K : Type*} [CommRing K] (β : K) (n : ℕ) :
    risingFact β (n + 1) = β * risingFact (β + 1) n := by
  induction n with
  | zero => simp [risingFact]
  | succ k ih =>
    rw [risingFact, ih, risingFact]
    push_cast
    ring

/-- Falling-to-rising sign identity: `(-1)^n (-v)_n = (descPochhammer K n).eval v`. -/
theorem neg_one_pow_mul_risingFact_neg {K : Type*} [CommRing K] (v : K) (n : ℕ) :
    (-1 : K) ^ n * risingFact (-v) n = (descPochhammer K n).eval v := by
  induction n with
  | zero => simp [risingFact, descPochhammer]
  | succ k ih =>
    rw [pow_succ', risingFact, descPochhammer_succ_right, Polynomial.eval_mul,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast]
    calc
      (-1 : K) * (-1) ^ k * ((-v + (k : K)) * risingFact (-v) k)
          = ((-1 : K) ^ k * risingFact (-v) k) * (v - (k : K)) := by ring
      _ = (descPochhammer K k).eval v * (v - (k : K)) := by rw [ih]

/-- Formal ordinary generating function `F_β(x) = ∑_{n ≥ 0} (β)_n x^n ∈ PowerSeries K`. -/
def expAtomPS {K : Type*} [CommRing K] (β : K) : PowerSeries K :=
  PowerSeries.mk (risingFact β)

/-- **Shift-Band Coefficient Identity (`F_β = 1 + x * β * F_{β + 1}`):**
Exact coefficientwise pushforward shifting the exponent `β` by `+1`. -/
theorem shift_band_coeff_identity {K : Type*} [CommRing K] (β : K) :
    expAtomPS β = 1 + PowerSeries.X * PowerSeries.C β * expAtomPS (β + 1) := by
  ext n
  cases n with
  | zero =>
    simp [expAtomPS, risingFact]
  | succ m =>
    simp only [map_add, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte,
      zero_add, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul]
    simp [expAtomPS, risingFact_succ_shift]

/-- Iterated `m`-step shift-band identity:
`F_β = ∑_{k < m} (β)_k x^k + x^m * (β)_m * F_{β + m}`. -/
theorem shift_band_iter_identity {K : Type*} [CommRing K] (β : K) (m : ℕ) :
    expAtomPS β =
      (∑ k ∈ Finset.range m, PowerSeries.C (risingFact β k) * PowerSeries.X ^ k) +
      PowerSeries.X ^ m * PowerSeries.C (risingFact β m) * expAtomPS (β + m) := by
  induction m with
  | zero =>
    simp [risingFact]
  | succ m ih =>
    rw [ih, Finset.sum_range_succ, shift_band_coeff_identity (β + m)]
    have hcoeff : risingFact β m * (β + (m : K)) = risingFact β (m + 1) := by
      rw [risingFact]; ring
    have hadd : β + (m : K) + 1 = β + ((m + 1 : ℕ) : K) := by push_cast; ring
    rw [hadd]
    have hCmul : PowerSeries.C (risingFact β m) * PowerSeries.C (β + (m : K)) =
        PowerSeries.C (risingFact β (m + 1)) := by
      rw [← map_mul, hcoeff]
    calc
      (∑ k ∈ Finset.range m, PowerSeries.C (risingFact β k) * PowerSeries.X ^ k) +
          PowerSeries.X ^ m * PowerSeries.C (risingFact β m) *
            (1 + PowerSeries.X * PowerSeries.C (β + (m : K)) *
              expAtomPS (β + ((m + 1 : ℕ) : K)))
          = (∑ k ∈ Finset.range m, PowerSeries.C (risingFact β k) * PowerSeries.X ^ k) +
              PowerSeries.C (risingFact β m) * PowerSeries.X ^ m +
              PowerSeries.X ^ (m + 1) *
                (PowerSeries.C (risingFact β m) * PowerSeries.C (β + (m : K))) *
                expAtomPS (β + ((m + 1 : ℕ) : K)) := by ring
      _ = (∑ k ∈ Finset.range m, PowerSeries.C (risingFact β k) * PowerSeries.X ^ k) +
            PowerSeries.C (risingFact β m) * PowerSeries.X ^ m +
            PowerSeries.X ^ (m + 1) * PowerSeries.C (risingFact β (m + 1)) *
              expAtomPS (β + ((m + 1 : ℕ) : K)) := by rw [hCmul]

/-- Measure-integrated shift-band identity (Paper #12 Section 7, eq. `F_μ = μ(ℝ) + x F_ρ`):
for any finite Borel measure `μ` on `ℝ`, the moment OGF satisfies
`∑ (∫ (β)_n dμ) x^n = μ(ℝ) + x ∑ (∫ β (β + 1)_n dμ) x^n`. -/
theorem shift_band_measure_identity (μ : Measure ℝ) :
    PowerSeries.mk (fun n : ℕ => ∫ β : ℝ, risingFact β n ∂μ) =
      PowerSeries.C (∫ _ : ℝ, (1 : ℝ) ∂μ) +
      PowerSeries.X * PowerSeries.mk (fun n : ℕ => ∫ β : ℝ, β * risingFact (β + 1) n ∂μ) := by
  ext n
  cases n with
  | zero =>
    simp [risingFact]
  | succ m =>
    simp only [map_add, PowerSeries.coeff_C, Nat.succ_ne_zero, ↓reduceIte,
      zero_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_mk]
    congr 1
    funext β
    exact risingFact_succ_shift β m

/-- Polynomial-cleared first-order differential equation in `PowerSeries K`:
`(x^2 ∂ + β x - 1) F_β = -1`. -/
theorem expAtomPS_diffEq {K : Type*} [CommRing K] (β : K) :
    PowerSeries.X ^ 2 * PowerSeries.derivative (expAtomPS β) +
      PowerSeries.C β * PowerSeries.X * expAtomPS β - expAtomPS β = -1 := by
  ext n
  cases n with
  | zero =>
    simp [expAtomPS, risingFact, sq, mul_assoc]
  | succ m =>
    simp only [map_sub, map_add, map_neg, PowerSeries.coeff_one, Nat.succ_ne_zero, ↓reduceIte,
      neg_zero]
    have hX2 : PowerSeries.coeff (m + 1) (PowerSeries.X ^ 2 * PowerSeries.derivative (expAtomPS β)) =
        (m : K) * risingFact β m := by
      cases m with
      | zero =>
        rw [sq, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
        simp
      | succ k =>
        rw [sq, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_derivative]
        simp [expAtomPS]
        ring
    have hX1 : PowerSeries.coeff (m + 1) (PowerSeries.C β * PowerSeries.X * expAtomPS β) =
        β * risingFact β m := by
      rw [mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
      simp [expAtomPS]
    rw [hX2, hX1]
    simp [expAtomPS, risingFact]
    ring

/-- Formal Laurent derivative `(laurentDeriv f).coeff n = (n + 1) * f.coeff (n + 1)` on `LaurentSeries K`. -/
def laurentDeriv {K : Type*} [CommRing K] : LaurentSeries K →ₗ[K] LaurentSeries K where
  toFun f :=
    { coeff := fun n => ((n + 1 : ℤ) : K) * f.coeff (n + 1)
      isPWO_support' := by
        have hsub : Function.support (fun n : ℤ => ((n + 1 : ℤ) : K) * f.coeff (n + 1)) ⊆
            (fun m : ℤ => m - 1) '' f.support := by
          intro n hn
          simp only [Function.mem_support, ne_eq] at hn
          refine ⟨n + 1, ?_, by ring⟩
          exact right_ne_zero_of_mul hn
        have hmono : Monotone (fun m : ℤ => m - 1) := fun _ _ h => sub_le_sub_right h 1
        exact (f.isPWO_support'.image_of_monotone hmono).mono hsub }
  map_add' f g := by ext n; simp [mul_add]
  map_smul' c f := by ext n; simp [smul_eq_mul]; ring

/-- Fundamental Stokes differential operator `T = x ∂ - 1/x` on `LaurentSeries K`. -/
def laurentT {K : Type*} [CommRing K] : LaurentSeries K →ₗ[K] LaurentSeries K where
  toFun f := HahnSeries.single 1 (1 : K) * laurentDeriv f - HahnSeries.single (-1) (1 : K) * f
  map_add' f g := by simp [mul_add]; abel
  map_smul' c f := by
    ext n
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_smul, HahnSeries.coeff_single_mul,
      map_smul, smul_eq_mul, one_mul, RingHom.id_apply]
    ring

/-- Exact coefficient formula `(laurentT f).coeff n = n * f.coeff n - f.coeff (n + 1)`. -/
theorem coeff_laurentT {K : Type*} [CommRing K] (f : LaurentSeries K) (n : ℤ) :
    (laurentT f).coeff n = (n : K) * f.coeff n - f.coeff (n + 1) := by
  change (HahnSeries.single 1 (1 : K) * laurentDeriv f - HahnSeries.single (-1) (1 : K) * f).coeff n = _
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single_mul, HahnSeries.coeff_single_mul]
  change (1 : K) * (((n - 1 + 1 : ℤ) : K) * f.coeff (n - 1 + 1)) - 1 * f.coeff (n - -1) = _
  simp only [one_mul, sub_add_cancel, sub_neg_eq_add]

/-- Shifted Stokes operator `T + β = x ∂ - 1/x + β` on `LaurentSeries K`. -/
def laurentTAdd (K : Type*) [CommRing K] (β : K) : LaurentSeries K →ₗ[K] LaurentSeries K :=
  laurentT + β • LinearMap.id

/-- Embedding of `expAtomPS β` into `LaurentSeries K` via `HahnSeries.ofPowerSeries`. -/
def expAtomLaurent {K : Type*} [CommRing K] (β : K) : LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K (expAtomPS β)

/-- Exact first-order inhomogeneous equation `(T + β) F_β = -1/x` in `LaurentSeries K`. -/
theorem laurentT_add_smul_expAtom {K : Type*} [CommRing K] (β : K) :
    laurentTAdd K β (expAtomLaurent β) = -HahnSeries.single (-1 : ℤ) (1 : K) := by
  ext n
  simp only [laurentTAdd, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
    HahnSeries.coeff_add, HahnSeries.coeff_smul, coeff_laurentT, HahnSeries.coeff_neg,
    HahnSeries.coeff_single, smul_eq_mul]
  unfold expAtomLaurent
  cases n with
  | ofNat m =>
    have hne : Int.ofNat m ≠ (-1 : ℤ) := by intro h; cases h
    simp only [hne, ↓reduceIte, neg_zero]
    have hm1 : Int.ofNat m + 1 = ((m + 1 : ℕ) : ℤ) := by rw [Int.ofNat_eq_natCast]; omega
    rw [hm1, Int.ofNat_eq_natCast, HahnSeries.ofPowerSeries_apply_coeff,
      HahnSeries.ofPowerSeries_apply_coeff]
    simp only [expAtomPS, PowerSeries.coeff_mk, risingFact, Int.cast_natCast]
    ring
  | negSucc k =>
    cases k with
    | zero =>
      have hneg1 : Int.negSucc 0 = (-1 : ℤ) := rfl
      simp only [hneg1, ↓reduceIte]
      rw [show (-1 : ℤ) + 1 = (0 : ℕ) by rfl, HahnSeries.ofPowerSeries_apply_coeff]
      have hcoef_neg : (HahnSeries.ofPowerSeries ℤ K (expAtomPS β)).coeff (-1 : ℤ) = 0 := by
        change (HahnSeries.ofPowerSeries ℤ K (expAtomPS β)).coeff (Int.negSucc 0) = 0
        exact HahnSeries.embDomain_of_notMem_range (by
          rintro ⟨m, hm⟩
          dsimp at hm
          omega)
      rw [hcoef_neg]
      simp [expAtomPS, risingFact]
    | succ k' =>
      have hne : Int.negSucc (k' + 1) ≠ (-1 : ℤ) := by omega
      simp only [hne, ↓reduceIte, neg_zero]
      have h1 : (HahnSeries.ofPowerSeries ℤ K (expAtomPS β)).coeff (Int.negSucc (k' + 1)) = 0 :=
        HahnSeries.embDomain_of_notMem_range (by
          rintro ⟨m, hm⟩
          dsimp at hm
          omega)
      have hnext : Int.negSucc (k' + 1) + 1 = Int.negSucc k' := by omega
      have h2 : (HahnSeries.ofPowerSeries ℤ K (expAtomPS β)).coeff (Int.negSucc (k' + 1) + 1) = 0 := by
        rw [hnext]
        exact HahnSeries.embDomain_of_notMem_range (by
          rintro ⟨m, hm⟩
          dsimp at hm
          omega)
      rw [h1, h2]
      ring

/-- Subspace of Laurent polynomials strictly in `1/x` (all nonnegative power coefficients zero). -/
def NegLaurentPoly (K : Type*) [CommRing K] : Submodule K (LaurentSeries K) where
  carrier := {f : LaurentSeries K | ∀ n : ℕ, f.coeff (n : ℤ) = 0}
  add_mem' {f g} hf hg n := by simp [hf n, hg n]
  zero_mem' n := by simp
  smul_mem' c {f} hf n := by simp [hf n]

/-- `-1/x` belongs to `NegLaurentPoly K`. -/
theorem neg_single_neg_one_mem_negLaurentPoly (K : Type*) [CommRing K] :
    -HahnSeries.single (-1 : ℤ) (1 : K) ∈ NegLaurentPoly K := by
  intro n
  simp only [HahnSeries.coeff_neg, HahnSeries.coeff_single]
  have hne : ((n : ℤ) ≠ -1) := by omega
  simp [hne]

/-- The operator `T = x ∂ - 1/x` preserves `NegLaurentPoly K`. -/
theorem laurentT_mem_negLaurentPoly {K : Type*} [CommRing K]
    {f : LaurentSeries K} (hf : f ∈ NegLaurentPoly K) :
    laurentT f ∈ NegLaurentPoly K := by
  intro n
  rw [coeff_laurentT, hf n]
  have h1 : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
  rw [h1, hf (n + 1)]
  ring

/-- Every factor `T + β` preserves `NegLaurentPoly K`. -/
theorem laurentT_add_smul_mem_negLaurentPoly {K : Type*} [CommRing K] (β : K)
    {f : LaurentSeries K} (hf : f ∈ NegLaurentPoly K) :
    laurentTAdd K β f ∈ NegLaurentPoly K :=
  Submodule.add_mem _ (laurentT_mem_negLaurentPoly hf) (Submodule.smul_mem _ β hf)

/-- Factors `(T + β₁)` and `(T + β₂)` commute as `K`-linear endomorphisms of `LaurentSeries K`. -/
theorem laurentT_add_smul_comm {K : Type*} [CommRing K] (β₁ β₂ : K) :
    (laurentTAdd K β₁).comp (laurentTAdd K β₂) =
      (laurentTAdd K β₂).comp (laurentTAdd K β₁) := by
  ext f n
  simp only [laurentTAdd, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, HahnSeries.coeff_add, HahnSeries.coeff_smul, coeff_laurentT, smul_eq_mul]
  ring

/-- Paper #12 jet-weight identity: `T^j F_β = (-β)^j F_β + p_j(1/x)` for some `p_j ∈ NegLaurentPoly K`. -/
theorem laurentT_pow_expAtom {K : Type*} [CommRing K] (β : K) (j : ℕ) :
    ∃ p ∈ NegLaurentPoly K,
      (laurentT (K := K) ^ j) (expAtomLaurent β) = (-β) ^ j • expAtomLaurent β + p := by
  induction j with
  | zero =>
    exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ k ih =>
    obtain ⟨p, hp, hEq⟩ := ih
    have hT_atom : laurentT (expAtomLaurent β) =
        (-β) • expAtomLaurent β + (-HahnSeries.single (-1 : ℤ) (1 : K)) := by
      have h1 := laurentT_add_smul_expAtom β
      simp only [laurentTAdd, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
      calc
        laurentT (expAtomLaurent β)
            = (laurentT (expAtomLaurent β) + β • expAtomLaurent β) - β • expAtomLaurent β := by
              abel
        _ = -HahnSeries.single (-1 : ℤ) (1 : K) - β • expAtomLaurent β := by rw [h1]
        _ = (-β) • expAtomLaurent β + (-HahnSeries.single (-1 : ℤ) (1 : K)) := by
              rw [neg_smul]; abel
    refine ⟨(-β) ^ k • (-HahnSeries.single (-1 : ℤ) (1 : K)) + laurentT p,
      Submodule.add_mem _ (Submodule.smul_mem _ _ (neg_single_neg_one_mem_negLaurentPoly K))
        (laurentT_mem_negLaurentPoly hp), ?_⟩
    rw [pow_succ', mul_apply_eq_comp, hEq, map_add, map_smul, hT_atom, smul_add, smul_smul,
      mul_comm ((-β) ^ k) (-β), ← pow_succ']
    abel

/-- Commuting differential operator `∏_{β ∈ s} (T + β)` on `LaurentSeries K`. -/
def annihOp {K : Type*} [CommRing K] : List K → LaurentSeries K →ₗ[K] LaurentSeries K
  | [] => LinearMap.id
  | β :: bs => (laurentTAdd K β).comp (annihOp bs)

/-- `annihOp bs` preserves `NegLaurentPoly K`. -/
theorem annihOp_mem_negLaurentPoly {K : Type*} [CommRing K] (bs : List K)
    {f : LaurentSeries K} (hf : f ∈ NegLaurentPoly K) :
    annihOp bs f ∈ NegLaurentPoly K := by
  induction bs with
  | nil => exact hf
  | cons β bs ih =>
    exact laurentT_add_smul_mem_negLaurentPoly β ih

/-- `annihOp bs` commutes with `T + α`. -/
theorem annihOp_comm_factor {K : Type*} [CommRing K] (bs : List K) (α : K) :
    (annihOp bs).comp (laurentTAdd K α) =
      (laurentTAdd K α).comp (annihOp bs) := by
  induction bs with
  | nil => simp [annihOp]
  | cons β bs ih =>
    simp only [annihOp]
    rw [LinearMap.comp_assoc, ih, ← LinearMap.comp_assoc, laurentT_add_smul_comm β α,
      LinearMap.comp_assoc]

/-- If `β ∈ bs`, then `annihOp bs (expAtomLaurent β) ∈ NegLaurentPoly K`. -/
theorem annihOp_expAtom_mem_negLaurentPoly {K : Type*} [CommRing K]
    {bs : List K} {β : K} (hmem : β ∈ bs) :
    annihOp bs (expAtomLaurent β) ∈ NegLaurentPoly K := by
  induction bs with
  | nil => cases hmem
  | cons a bs ih =>
    simp only [annihOp, LinearMap.comp_apply]
    rcases List.mem_cons.mp hmem with rfl | htail
    · have hcomm := congrArg (fun L : LaurentSeries K →ₗ[K] LaurentSeries K =>
        L (expAtomLaurent β)) (annihOp_comm_factor bs β).symm
      simp only [LinearMap.comp_apply] at hcomm
      rw [hcomm, laurentT_add_smul_expAtom]
      exact annihOp_mem_negLaurentPoly bs (neg_single_neg_one_mem_negLaurentPoly K)
    · exact laurentT_add_smul_mem_negLaurentPoly a (ih htail)

/-- **D-Finite Annihilator for Finitely Supported Exponent Measures:**
For ANY finite linear combination `F = ∑ i : Fin N, c i • F_{β i}`, the commuting operator
`∏_i (T + β_i)` sends `F` into `NegLaurentPoly K` (all nonnegative power coefficients vanish
identically, i.e., `∏_i (T + β_i) F` is a Laurent polynomial in `1/x`). -/
theorem finite_support_measure_annihilated {K : Type*} [CommRing K]
    {N : ℕ} (β c : Fin N → K) :
    annihOp (List.ofFn β) (∑ i : Fin N, c i • expAtomLaurent (β i)) ∈ NegLaurentPoly K := by
  rw [map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ (c i) ?_
  apply annihOp_expAtom_mem_negLaurentPoly
  rw [List.mem_ofFn]
  exact ⟨i, rfl⟩

end ExponentAtomOperators

/-! ### 3. Komatsu's Poly-Cauchy Numbers — Complete Exact Algebraic Core (Corollary 7.3) -/

section PolyCauchyCore

/-- Poly-Cauchy probability density of the second kind on `(0, 1)`:
`w_k(v) = (-log v)^(k - 1) / (k - 1)!` for `k ≥ 1`. -/
def polyCauchyW (k : ℕ) (v : ℝ) : ℝ :=
  (-Real.log v) ^ (k - 1) / ((k - 1).factorial : ℝ)

/-- Shifted poly-Cauchy density of the first kind on `(0, 1)`:
`ρ_k(v) = (v - 1) * w_k(1 - v)` for `k ≥ 1`. -/
def polyCauchyRho (k : ℕ) (v : ℝ) : ℝ :=
  (v - 1) * polyCauchyW k (1 - v)

/-- Explicit elementary antiderivative of `v ↦ v^m * (-log v)^j / j!` on `(0, 1)`:
`H_{m, j}(v) = v^(m + 1) * ∑_{r=0}^j (-log v)^r / (r! * (m + 1)^(j + 1 - r))`. -/
def polyCauchyAntideriv (m j : ℕ) (v : ℝ) : ℝ :=
  v ^ (m + 1) *
    ∑ r ∈ Finset.range (j + 1),
      (-Real.log v) ^ r / ((r.factorial : ℝ) * ((m + 1 : ℝ) ^ (j + 1 - r)))

/-- For every `a > 0` and `r : ℕ`, `v^a * (-log v)^r → 0` as `v → 0⁺`. -/
theorem tendsto_rpow_mul_neg_log_pow_zero {a : ℝ} (ha : 0 < a) (r : ℕ) :
    Tendsto (fun v : ℝ => v ^ a * (-Real.log v) ^ r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlog : Tendsto (fun v : ℝ => -Real.log v) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hmul : Tendsto (fun v : ℝ => a * (-Real.log v)) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_id.const_mul_atTop ha).comp hlog
  have hbase : Tendsto (fun t : ℝ => t ^ r * Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero r
  have hcomp := (hbase.comp hmul).const_mul (a ^ r)⁻¹
  rw [mul_zero] at hcomp
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  have hv0 : 0 < v := hv
  have hexp : Real.exp (-(a * (-Real.log v))) = v ^ a := by
    rw [Real.rpow_def_of_pos hv0]
    congr 1
    ring
  simp only [Function.comp_apply, hexp, mul_pow]
  have har : a ^ r ≠ 0 := (pow_pos ha r).ne'
  field_simp

/-- Special case `a = 1`: `v * (-log v)^r → 0` as `v → 0⁺`. -/
theorem tendsto_self_mul_neg_log_pow_zero (r : ℕ) :
    Tendsto (fun v : ℝ => v * (-Real.log v) ^ r) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := tendsto_rpow_mul_neg_log_pow_zero zero_lt_one r
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v _
  simp

private lemma hasDerivAt_polyCauchyAntideriv (m j : ℕ) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (polyCauchyAntideriv m j)
      (v ^ m * ((-Real.log v) ^ j / (j.factorial : ℝ))) v := by
  set a : ℝ := (m : ℝ) + 1
  have ha : a ≠ 0 := by positivity
  set S : ℝ → ℝ := fun x =>
    ∑ r ∈ Finset.range (j + 1),
      (-Real.log x) ^ r / ((r.factorial : ℝ) * a ^ (j + 1 - r))
  set S' : ℝ → ℝ := fun x =>
    -(x⁻¹) * ∑ r ∈ Finset.range j,
      (-Real.log x) ^ r / ((r.factorial : ℝ) * a ^ (j - r))
  have hS : HasDerivAt S (S' v) v := by
    have hterm : ∀ r ∈ Finset.range (j + 1),
        HasDerivAt (fun x : ℝ => (-Real.log x) ^ r / ((r.factorial : ℝ) * a ^ (j + 1 - r)))
          (((r : ℝ) * (-Real.log v) ^ (r - 1) * (-v⁻¹)) / ((r.factorial : ℝ) * a ^ (j + 1 - r)))
          v := by
      intro r _
      have h1 : HasDerivAt (fun x : ℝ => -Real.log x) (-v⁻¹) v :=
        (Real.hasDerivAt_log hv.ne').fun_neg
      exact (h1.pow r).div_const _
    have hsum := HasDerivAt.fun_sum hterm
    convert hsum using 1
    dsimp only [S']
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hr_lt : r < j := Finset.mem_range.mp hr
    have hsub : j + 1 - (r + 1) = j - r := Nat.succ_sub_succ_eq_sub j r
    rw [hsub, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hr1 : ((r : ℝ) + 1) ≠ 0 := by positivity
    have hfr : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
    have hap : a ^ (j - r) ≠ 0 := pow_ne_zero _ ha
    field_simp
  have hpow : HasDerivAt (fun x : ℝ => x ^ (m + 1)) (a * v ^ m) v := by
    have h := hasDerivAt_pow (m + 1) v
    simpa [a] using h
  have hprod := hpow.fun_mul hS
  have hfun : polyCauchyAntideriv m j = fun x => x ^ (m + 1) * S x := rfl
  rw [hfun]
  convert hprod using 1
  have hcancel : a * S v + v * S' v = (-Real.log v) ^ j / (j.factorial : ℝ) := by
    dsimp [S, S']
    rw [Finset.mul_sum, Finset.sum_range_succ]
    have hlast : a * ((-Real.log v) ^ j / ((j.factorial : ℝ) * a ^ (j + 1 - j))) =
        (-Real.log v) ^ j / (j.factorial : ℝ) := by
      have hsub : j + 1 - j = 1 := by omega
      rw [hsub, pow_one]
      have hfj : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
      field_simp
    have hfirst :
        (∑ r ∈ Finset.range j, a * ((-Real.log v) ^ r / ((r.factorial : ℝ) * a ^ (j + 1 - r)))) =
          ∑ r ∈ Finset.range j, (-Real.log v) ^ r / ((r.factorial : ℝ) * a ^ (j - r)) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_lt : r < j := Finset.mem_range.mp hr
      have hapow : a ^ (j + 1 - r) = a * a ^ (j - r) := by
        rw [show j + 1 - r = (j - r) + 1 by omega, pow_succ']
      rw [hapow]
      have hfr : (r.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero r)
      have hap : a ^ (j - r) ≠ 0 := pow_ne_zero _ ha
      field_simp
    have hv_cancel : v * (-(v⁻¹) *
        ∑ r ∈ Finset.range j, (-Real.log v) ^ r / ((r.factorial : ℝ) * a ^ (j - r))) =
        -∑ r ∈ Finset.range j, (-Real.log v) ^ r / ((r.factorial : ℝ) * a ^ (j - r)) := by
      have hv_ne : v ≠ 0 := hv.ne'
      field_simp
    rw [hfirst, hlast, hv_cancel]
    ring
  calc
    v ^ m * ((-Real.log v) ^ j / (j.factorial : ℝ))
        = v ^ m * (a * S v + v * S' v) := by rw [hcancel]
    _ = a * v ^ m * S v + v ^ (m + 1) * S' v := by rw [pow_succ]; ring

/-- Integrability of `v ↦ v^m * (-log v)^j / j!` on `(0, 1)` for every `m, j : ℕ`. -/
theorem polyCauchyW_moment_integrable (m j : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ m * ((-Real.log v) ^ j / (j.factorial : ℝ)))
      (Set.Ioo (0 : ℝ) 1) := by
  have hcont : ContinuousOn (fun v : ℝ => v ^ m * ((-Real.log v) ^ j / (j.factorial : ℝ)))
      (Set.Ioo (0 : ℝ) 1) := by
    refine (continuous_pow m).continuousOn.mul ?_
    have hsub : Set.Ioo (0 : ℝ) 1 ⊆ {(0 : ℝ)}ᶜ := fun x hx => ne_of_gt hx.1
    refine (((Real.continuousOn_log.mono hsub).neg).pow j).div_const _
  set C : ℝ := (2 : ℝ) ^ j
  have hdom : IntegrableOn (fun v : ℝ => C * v ^ (-(1 : ℝ) / 2)) (Set.Ioo (0 : ℝ) 1) := by
    have hi : IntervalIntegrable (fun v : ℝ => v ^ (-(1 : ℝ) / 2)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hi
    exact hi.const_mul C
  refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  have hv0 : 0 < v := hv.1
  have hv1 : v < 1 := hv.2
  have hlog_nn : 0 ≤ -Real.log v := neg_nonneg.mpr (Real.log_nonpos hv0.le hv1.le)
  rw [Real.norm_of_nonneg (by positivity)]
  have hvm : v ^ m ≤ 1 := pow_le_one₀ hv0.le hv1.le
  have hterm : ((-Real.log v) / 2) ^ j / (j.factorial : ℝ) ≤ Real.exp ((-Real.log v) / 2) := by
    have hsum := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ (-Real.log v) / 2) (j + 1)
    have hmem : j ∈ Finset.range (j + 1) := Finset.mem_range.mpr (Nat.lt_succ_self j)
    have hnn : ∀ i ∈ Finset.range (j + 1), 0 ≤ ((-Real.log v) / 2) ^ i / (i.factorial : ℝ) :=
      fun _ _ => by positivity
    exact le_trans (Finset.single_le_sum hnn hmem) hsum
  have hexp_rpow : Real.exp ((-Real.log v) / 2) = v ^ (-(1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hv0]
    congr 1
    ring
  rw [hexp_rpow] at hterm
  have hlog_bound : (-Real.log v) ^ j / (j.factorial : ℝ) ≤ C * v ^ (-(1 : ℝ) / 2) := by
    rw [div_pow] at hterm
    have h2j : (0 : ℝ) < C := by positivity
    have hmul := mul_le_mul_of_nonneg_left hterm h2j.le
    have h2j_ne : C ≠ 0 := h2j.ne'
    have hfj_ne : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    calc
      (-Real.log v) ^ j / (j.factorial : ℝ)
          = C * ((-Real.log v) ^ j / C / (j.factorial : ℝ)) := by field_simp
      _ ≤ C * v ^ (-(1 : ℝ) / 2) := hmul
  calc
    v ^ m * ((-Real.log v) ^ j / (j.factorial : ℝ))
        ≤ 1 * ((-Real.log v) ^ j / (j.factorial : ℝ)) :=
          mul_le_mul_of_nonneg_right hvm (by positivity)
    _ = (-Real.log v) ^ j / (j.factorial : ℝ) := one_mul _
    _ ≤ C * v ^ (-(1 : ℝ) / 2) := hlog_bound

/-- **Exact Poly-Cauchy Density Moment Identity (Paper #12 Corollary 7.3):**
For every integer `k ≥ 1` and every `m : ℕ`:
`∫ v in Set.Ioo (0 : ℝ) 1, v^m * ((-Real.log v)^(k - 1) / (k - 1)!) = 1 / (m + 1)^k`. -/
theorem polyCauchy_log_density_moment {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∫ v in Set.Ioo (0 : ℝ) 1,
        v ^ m * ((-Real.log v) ^ (k - 1) / ((k - 1).factorial : ℝ)) =
      (1 : ℝ) / ((m + 1 : ℝ) ^ k) := by
  set j : ℕ := k - 1
  have hjk : j + 1 = k := Nat.sub_add_cancel hk
  have hint_ii : IntervalIntegrable
      (fun v : ℝ => v ^ m * ((-Real.log v) ^ j / (j.factorial : ℝ))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact polyCauchyW_moment_integrable m j
  have hderiv : ∀ v ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (polyCauchyAntideriv m j)
        (v ^ m * ((-Real.log v) ^ j / (j.factorial : ℝ))) v :=
    fun v hv => hasDerivAt_polyCauchyAntideriv m j hv.1
  have htend0 : Tendsto (polyCauchyAntideriv m j) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hterm : ∀ r ∈ Finset.range (j + 1),
        Tendsto (fun v : ℝ =>
            v ^ (m + 1) * ((-Real.log v) ^ r / ((r.factorial : ℝ) * ((m + 1 : ℝ) ^ (j + 1 - r)))))
          (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      intro r _
      set c : ℝ := ((r.factorial : ℝ) * ((m + 1 : ℝ) ^ (j + 1 - r)))⁻¹
      have h1 := (tendsto_rpow_mul_neg_log_pow_zero (by positivity : (0 : ℝ) < (m + 1 : ℕ)) r).const_mul c
      rw [mul_zero] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with v _
      rw [Real.rpow_natCast]
      dsimp [c]
      ring
    have hsum : Tendsto (fun v : ℝ =>
        ∑ r ∈ Finset.range (j + 1),
          v ^ (m + 1) * ((-Real.log v) ^ r / ((r.factorial : ℝ) * ((m + 1 : ℝ) ^ (j + 1 - r)))))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hgen : ∀ (s : Finset ℕ),
          (∀ r ∈ s, Tendsto (fun v : ℝ =>
              v ^ (m + 1) * ((-Real.log v) ^ r / ((r.factorial : ℝ) * ((m + 1 : ℝ) ^ (j + 1 - r)))))
            (𝓝[>] (0 : ℝ)) (𝓝 0)) →
          Tendsto (fun v : ℝ =>
            ∑ r ∈ s,
              v ^ (m + 1) * ((-Real.log v) ^ r / ((r.factorial : ℝ) * ((m + 1 : ℝ) ^ (j + 1 - r)))))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        intro s
        induction s using Finset.induction_on with
        | empty => intro _; simp
        | insert a s ha ih =>
          intro hs
          have h1 := hs a (Finset.mem_insert_self a s)
          have h2 := ih fun r hr => hs r (Finset.mem_insert_of_mem hr)
          have h3 := h1.add h2
          rw [add_zero] at h3
          refine h3.congr fun v => ?_
          rw [Finset.sum_insert ha]
      exact hgen (Finset.range (j + 1)) hterm
    refine hsum.congr fun v => ?_
    unfold polyCauchyAntideriv
    rw [Finset.mul_sum]
  have htend1 : Tendsto (polyCauchyAntideriv m j) (𝓝[<] (1 : ℝ)) (𝓝 (polyCauchyAntideriv m j 1)) := by
    have hcont1 : ContinuousAt (polyCauchyAntideriv m j) 1 :=
      (hasDerivAt_polyCauchyAntideriv m j zero_lt_one).continuousAt
    exact hcont1.tendsto.mono_left nhdsWithin_le_nhds
  have hval1 : polyCauchyAntideriv m j 1 = 1 / ((m + 1 : ℝ) ^ k) := by
    unfold polyCauchyAntideriv
    rw [one_pow, one_mul, Real.log_one, neg_zero]
    rw [Finset.sum_eq_single 0]
    · simp [hjk]
    · intro r _ hr0
      simp [zero_pow hr0]
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos j)) h0
  rw [MeasureTheory.setIntegral_congr_set Ioo_ae_eq_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hderiv hint_ii htend0 htend1,
    hval1, sub_zero]

/-- `n`-th Cauchy number of the first kind `c_{1, n} = ∫_0^1 (-1)^n (-v)_n dv = ∫_0^1 (v)_n↓ dv`. -/
def cauchyFirstCoeff (n : ℕ) : ℝ :=
  ∫ v in (0 : ℝ)..1, (-1 : ℝ) ^ n * risingFact (-v) n

/-- `n`-th Cauchy number of the second kind (signed OGF convention `C_2(x) = F_{μ_0}(-x)`):
`c_{2, n} = ∫_0^1 (-1)^n (v)_n dv`. -/
def cauchySecondCoeff (n : ℕ) : ℝ :=
  ∫ v in (0 : ℝ)..1, (-1 : ℝ) ^ n * risingFact v n

/-- Formal OGF of Cauchy numbers of the first kind `C_1(x)`. -/
def cauchyFirstPS : PowerSeries ℝ :=
  PowerSeries.mk cauchyFirstCoeff

/-- Formal OGF of Cauchy numbers of the second kind `C_2(x) = F_{μ_0}(-x)`. -/
def cauchySecondPS : PowerSeries ℝ :=
  PowerSeries.mk cauchySecondCoeff

private lemma polynomial_analyticAt (p : Polynomial ℝ) (x : ℝ) :
    AnalyticAt ℝ (fun u : ℝ => p.eval u) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hfun : (fun u : ℝ => (p + q).eval u) = fun u => p.eval u + q.eval u := by
      funext u; exact Polynomial.eval_add
    rw [hfun]
    exact hp.add hq
  | monomial n a =>
    have hfun : (fun u : ℝ => (Polynomial.monomial n a).eval u) = fun u => a * u ^ n := by
      funext u; exact Polynomial.eval_monomial
    rw [hfun]
    exact analyticAt_const.mul (analyticAt_id.pow n)

private lemma polynomial_continuous (p : Polynomial ℝ) :
    Continuous (fun u : ℝ => p.eval u) :=
  continuous_iff_continuousAt.mpr fun x => (polynomial_analyticAt p x).continuousAt

/-- Exact coefficientwise recurrence `c_{1, n + 1} = c_{2, n + 1} + (n + 1) * c_{2, n}`. -/
theorem cauchyFirstCoeff_succ (n : ℕ) :
    cauchyFirstCoeff (n + 1) = cauchySecondCoeff (n + 1) + ((n + 1 : ℕ) : ℝ) * cauchySecondCoeff n := by
  unfold cauchyFirstCoeff cauchySecondCoeff
  have hpt : ∀ u : ℝ,
      (-1 : ℝ) ^ (n + 1) * risingFact (-u) (n + 1) =
        (-1 : ℝ) ^ (n + 1) * risingFact (1 - u) (n + 1) +
          ((n + 1 : ℕ) : ℝ) * ((-1 : ℝ) ^ n * risingFact (1 - u) n) := by
    intro u
    have hshift : risingFact (-u) (n + 1) = (-u) * risingFact (1 - u) n := by
      have h := risingFact_succ_shift (-u) n
      have h1 : -u + 1 = 1 - u := by ring
      rwa [h1] at h
    rw [hshift, risingFact]
    push_cast
    ring
  have hcont_rise : ∀ k : ℕ, Continuous (fun v : ℝ => risingFact v k) := by
    intro k
    have h : (fun v : ℝ => risingFact v k) = fun v : ℝ => (ascPochhammer ℝ k).eval v := by
      funext v; exact risingFact_eq_ascPochhammer v k
    rw [h]
    exact polynomial_continuous (ascPochhammer ℝ k)
  have hcomp1 : ∫ u in (0 : ℝ)..1, (-1 : ℝ) ^ (n + 1) * risingFact (1 - u) (n + 1) =
      ∫ v in (0 : ℝ)..1, (-1 : ℝ) ^ (n + 1) * risingFact v (n + 1) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun v : ℝ => (-1 : ℝ) ^ (n + 1) * risingFact v (n + 1)) (1 : ℝ) (a := (0 : ℝ)) (b := 1)
    simpa using h
  have hcomp2 : ∫ u in (0 : ℝ)..1, (-1 : ℝ) ^ n * risingFact (1 - u) n =
      ∫ v in (0 : ℝ)..1, (-1 : ℝ) ^ n * risingFact v n := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun v : ℝ => (-1 : ℝ) ^ n * risingFact v n) (1 : ℝ) (a := (0 : ℝ)) (b := 1)
    simpa using h
  have hint1_sub : IntervalIntegrable
      (fun u : ℝ => (-1 : ℝ) ^ (n + 1) * risingFact (1 - u) (n + 1)) volume 0 1 :=
    (continuous_const.mul ((hcont_rise (n + 1)).comp (continuous_const.sub continuous_id))).intervalIntegrable 0 1
  have hint2_sub : IntervalIntegrable
      (fun u : ℝ => ((n + 1 : ℕ) : ℝ) * ((-1 : ℝ) ^ n * risingFact (1 - u) n)) volume 0 1 :=
    (continuous_const.mul (continuous_const.mul
      ((hcont_rise n).comp (continuous_const.sub continuous_id)))).intervalIntegrable 0 1
  calc
    ∫ u in (0 : ℝ)..1, (-1 : ℝ) ^ (n + 1) * risingFact (-u) (n + 1)
        = ∫ u in (0 : ℝ)..1,
            ((-1 : ℝ) ^ (n + 1) * risingFact (1 - u) (n + 1) +
              ((n + 1 : ℕ) : ℝ) * ((-1 : ℝ) ^ n * risingFact (1 - u) n)) := by
          congr 1; funext u; exact hpt u
    _ = (∫ u in (0 : ℝ)..1, (-1 : ℝ) ^ (n + 1) * risingFact (1 - u) (n + 1)) +
          (∫ u in (0 : ℝ)..1, ((n + 1 : ℕ) : ℝ) * ((-1 : ℝ) ^ n * risingFact (1 - u) n)) :=
          intervalIntegral.integral_add hint1_sub hint2_sub
    _ = (∫ u in (0 : ℝ)..1, (-1 : ℝ) ^ (n + 1) * risingFact (1 - u) (n + 1)) +
          ((n + 1 : ℕ) : ℝ) * (∫ u in (0 : ℝ)..1, (-1 : ℝ) ^ n * risingFact (1 - u) n) := by
          rw [intervalIntegral.integral_const_mul ((n + 1 : ℕ) : ℝ)]
    _ = (∫ v in (0 : ℝ)..1, (-1 : ℝ) ^ (n + 1) * risingFact v (n + 1)) +
          ((n + 1 : ℕ) : ℝ) * (∫ v in (0 : ℝ)..1, (-1 : ℝ) ^ n * risingFact v n) := by
          rw [hcomp1, hcomp2]

/-- **Exact `k = 1` Cauchy Differential Relation (Paper #12 Section 7):**
`C_1 = (1 + x) * C_2 + x^2 * C_2'` in `PowerSeries ℝ`. -/
theorem cauchy_first_second_kind_relation :
    cauchyFirstPS =
      (1 + PowerSeries.X) * cauchySecondPS +
      PowerSeries.X ^ 2 * PowerSeries.derivative cauchySecondPS := by
  ext n
  cases n with
  | zero =>
    simp [cauchyFirstPS, cauchySecondPS, cauchyFirstCoeff, cauchySecondCoeff,
      risingFact, add_mul, sq, mul_assoc]
  | succ m =>
    rw [add_mul, one_mul, map_add, map_add, PowerSeries.coeff_succ_X_mul]
    have hX2 : PowerSeries.coeff (m + 1)
        (PowerSeries.X ^ 2 * PowerSeries.derivative cauchySecondPS) =
        (m : ℝ) * cauchySecondCoeff m := by
      cases m with
      | zero =>
        rw [sq, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul]
        simp
      | succ k =>
        rw [sq, mul_assoc, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_succ_X_mul,
          PowerSeries.coeff_derivative]
        simp [cauchySecondPS]
        ring
    rw [hX2]
    simp only [cauchyFirstPS, cauchySecondPS, PowerSeries.coeff_mk]
    rw [cauchyFirstCoeff_succ m]
    push_cast
    ring

/-! #### Two-Endpoint Analytic Peeling & Exact Poly-Cauchy Density Rank over `ℝ[u]` -/

/-- Core peeling lemma at `u → 0⁺`: if `H` is real-analytic at `0` and
`∑_{m : Fin M} P_m(u) * (-log u)^(m + 1) = H(u)` eventually on `u ∈ (0, ε)`, then
**every polynomial `P_m` vanishes identically**. -/
theorem poly_log_analytic_eq_zero {M : ℕ} {H : ℝ → ℝ} (hH : AnalyticAt ℝ H 0)
    (P : Fin M → Polynomial ℝ)
    (heq : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      ∑ m : Fin M, (P m).eval u * (-Real.log u) ^ (m.val + 1) = H u) :
    ∀ m : Fin M, P m = 0 := by
  have hmain : ∀ D : ℕ, ∀ (H : ℝ → ℝ), AnalyticAt ℝ H 0 →
      ∀ (P : Fin M → Polynomial ℝ),
        (∀ m : Fin M, P m = 0 ∨ (P m).natDegree < D) →
        (∀ᶠ u in 𝓝[>] (0 : ℝ),
          ∑ m : Fin M, (P m).eval u * (-Real.log u) ^ (m.val + 1) = H u) →
        ∀ m : Fin M, P m = 0 := by
    intro D
    induction D with
    | zero =>
      intro _ _ P hdeg _ m
      rcases hdeg m with h0 | hlt
      · exact h0
      · exact absurd hlt (Nat.not_lt_zero _)
    | succ D ih =>
      intro H hH P hdeg heq
      -- Step 1: Prove every constant term `(P m).coeff 0 = 0`.
      have hcoeff0 : ∀ m : Fin M, (P m).coeff 0 = 0 := by
        by_contra hnot
        push Not at hnot
        let nz : Finset (Fin M) := Finset.univ.filter (fun m => (P m).coeff 0 ≠ 0)
        have hnz_ne : nz.Nonempty := by
          obtain ⟨m, hm⟩ := hnot
          exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩⟩
        let m₀ : Fin M := nz.max' hnz_ne
        have hm₀_mem : m₀ ∈ nz := Finset.max'_mem nz hnz_ne
        have hm₀_ne : (P m₀).coeff 0 ≠ 0 := (Finset.mem_filter.mp hm₀_mem).2
        have hm₀_max : ∀ m : Fin M, m₀ < m → (P m).coeff 0 = 0 := by
          intro m hgt
          by_contra hm_ne
          have hle := Finset.le_max' nz m (Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm_ne⟩)
          exact not_lt_of_ge hle hgt
        have hlog_top : Tendsto (fun u : ℝ => -Real.log u) (𝓝[>] (0 : ℝ)) atTop :=
          tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
        have hinv_log : ∀ k : ℕ, 1 ≤ k →
            Tendsto (fun u : ℝ => ((-Real.log u) ^ k)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          intro k hk
          have hpow : Tendsto (fun t : ℝ => t ^ k) atTop atTop :=
            tendsto_pow_atTop (by omega : k ≠ 0)
          exact tendsto_inv_atTop_zero.comp (hpow.comp hlog_top)
        have hterm_lim : ∀ m : Fin M,
            Tendsto (fun u : ℝ =>
                ((P m).eval u * (-Real.log u) ^ (m.val + 1)) / (-Real.log u) ^ (m₀.val + 1))
              (𝓝[>] (0 : ℝ)) (𝓝 (if m = m₀ then (P m₀).coeff 0 else 0)) := by
          intro m
          by_cases heqm : m = m₀
          · subst heqm
            simp only [↓reduceIte]
            have hP0 : Tendsto (fun u : ℝ => (P m₀).eval u) (𝓝[>] (0 : ℝ)) (𝓝 ((P m₀).coeff 0)) := by
              have hc := ((polynomial_continuous (P m₀)).continuousAt (x := (0 : ℝ))).tendsto
              rw [← Polynomial.coeff_zero_eq_eval_zero] at hc
              exact hc.mono_left nhdsWithin_le_nhds
            refine hP0.congr' ?_
            filter_upwards [hlog_top.eventually_gt_atTop 0] with u hu
            have hne : (-Real.log u) ^ (m₀.val + 1) ≠ 0 := (pow_pos hu _).ne'
            field_simp
          · simp only [heqm, ↓reduceIte]
            rcases lt_or_gt_of_ne heqm with hlt | hgt
            · have hP0 : Tendsto (fun u : ℝ => (P m).eval u) (𝓝[>] (0 : ℝ)) (𝓝 ((P m).coeff 0)) := by
                have hc := ((polynomial_continuous (P m)).continuousAt (x := (0 : ℝ))).tendsto
                rw [← Polynomial.coeff_zero_eq_eval_zero] at hc
                exact hc.mono_left nhdsWithin_le_nhds
              have hdiff_pos : 1 ≤ m₀.val - m.val := by
                have : m.val < m₀.val := hlt
                omega
              have hlim := hP0.mul (hinv_log (m₀.val - m.val) hdiff_pos)
              rw [mul_zero] at hlim
              refine hlim.congr' ?_
              filter_upwards [hlog_top.eventually_gt_atTop 0] with u hu
              have hpow_split : (-Real.log u) ^ (m₀.val + 1) =
                  (-Real.log u) ^ (m.val + 1) * (-Real.log u) ^ (m₀.val - m.val) := by
                rw [← pow_add]
                congr 1
                have : m.val < m₀.val := hlt
                omega
              have hne1 : (-Real.log u) ^ (m.val + 1) ≠ 0 := (pow_pos hu _).ne'
              have hne2 : (-Real.log u) ^ (m₀.val - m.val) ≠ 0 := (pow_pos hu _).ne'
              rw [hpow_split]
              field_simp
            · have hc0 : (P m).coeff 0 = 0 := hm₀_max m hgt
              have hdivX : P m = Polynomial.X * (P m).divX := by
                have h := Polynomial.X_mul_divX_add (P m)
                rw [hc0, map_zero, add_zero] at h
                exact h.symm
              have hP_eval : ∀ u : ℝ, (P m).eval u = u * ((P m).divX).eval u := by
                intro u
                conv_lhs => rw [hdivX]
                simp
              have hQ0 : Tendsto (fun u : ℝ => ((P m).divX).eval u) (𝓝[>] (0 : ℝ))
                  (𝓝 (((P m).divX).eval 0)) :=
                (polynomial_continuous (P m).divX).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
              have hlim := hQ0.mul (tendsto_self_mul_neg_log_pow_zero (m.val - m₀.val))
              rw [mul_zero] at hlim
              refine hlim.congr' ?_
              filter_upwards [hlog_top.eventually_gt_atTop 0] with u hu
              have hpow_split : (-Real.log u) ^ (m.val + 1) =
                  (-Real.log u) ^ (m₀.val + 1) * (-Real.log u) ^ (m.val - m₀.val) := by
                rw [← pow_add]
                congr 1
                have : m₀.val < m.val := hgt
                omega
              have hne : (-Real.log u) ^ (m₀.val + 1) ≠ 0 := (pow_pos hu _).ne'
              rw [hP_eval u, hpow_split]
              field_simp
        have hsum_lim : Tendsto (fun u : ℝ =>
            (∑ m : Fin M, (P m).eval u * (-Real.log u) ^ (m.val + 1)) /
              (-Real.log u) ^ (m₀.val + 1))
            (𝓝[>] (0 : ℝ)) (𝓝 ((P m₀).coeff 0)) := by
          have hgen : ∀ (s : Finset (Fin M)),
              Tendsto (fun u : ℝ =>
                ∑ m ∈ s, ((P m).eval u * (-Real.log u) ^ (m.val + 1)) /
                  (-Real.log u) ^ (m₀.val + 1))
                (𝓝[>] (0 : ℝ)) (𝓝 (∑ m ∈ s, if m = m₀ then (P m₀).coeff 0 else 0)) := by
            intro s
            induction s using Finset.induction_on with
            | empty => simp
            | insert a s ha ih =>
              rw [Finset.sum_insert ha]
              have h1 := (hterm_lim a).add ih
              refine h1.congr fun u => ?_
              rw [Finset.sum_insert ha]
          have hsum_univ := hgen Finset.univ
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hsum_univ
          refine hsum_univ.congr fun u => ?_
          rw [Finset.sum_div]
        have hrhs_lim : Tendsto (fun u : ℝ => H u / (-Real.log u) ^ (m₀.val + 1))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have hH0 : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 (H 0)) :=
            hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
          have hmul := hH0.mul (hinv_log (m₀.val + 1) (Nat.succ_pos _))
          rw [mul_zero] at hmul
          refine hmul.congr fun u => ?_
          rw [div_eq_mul_inv]
        have hlhs_eq_rhs :
            (fun u : ℝ =>
              (∑ m : Fin M, (P m).eval u * (-Real.log u) ^ (m.val + 1)) /
                (-Real.log u) ^ (m₀.val + 1)) =ᶠ[𝓝[>] (0 : ℝ)]
              (fun u : ℝ => H u / (-Real.log u) ^ (m₀.val + 1)) := by
          filter_upwards [heq] with u hu
          rw [hu]
        have hzero_c := tendsto_nhds_unique (hsum_lim.congr' hlhs_eq_rhs) hrhs_lim
        exact hm₀_ne hzero_c
      -- Step 2: Factor out `X` from every `P m` and divide `H` by `u` using `dslope H 0`.
      have hdivX : ∀ m : Fin M, P m = Polynomial.X * (P m).divX := by
        intro m
        have h := Polynomial.X_mul_divX_add (P m)
        rw [hcoeff0 m, map_zero, add_zero] at h
        exact h.symm
      have hP_eval : ∀ (m : Fin M) (u : ℝ), (P m).eval u = u * ((P m).divX).eval u := by
        intro m u
        conv_lhs => rw [hdivX m]
        simp
      have hH_zero : H 0 = 0 := by
        have hlhs_zero : Tendsto (fun u : ℝ =>
            ∑ m : Fin M, (P m).eval u * (-Real.log u) ^ (m.val + 1))
            (𝓝[>] (0 : ℝ)) (𝓝 0) := by
          have hterm0 : ∀ m : Fin M,
              Tendsto (fun u : ℝ => (P m).eval u * (-Real.log u) ^ (m.val + 1))
                (𝓝[>] (0 : ℝ)) (𝓝 0) := by
            intro m
            have hQ0 : Tendsto (fun u : ℝ => ((P m).divX).eval u) (𝓝[>] (0 : ℝ))
                (𝓝 (((P m).divX).eval 0)) :=
              (polynomial_continuous (P m).divX).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            have hlim := hQ0.mul (tendsto_self_mul_neg_log_pow_zero (m.val + 1))
            rw [mul_zero] at hlim
            refine hlim.congr fun u => ?_
            rw [hP_eval m u]
            ring
          have hgen : ∀ (s : Finset (Fin M)),
              Tendsto (fun u : ℝ => ∑ m ∈ s, (P m).eval u * (-Real.log u) ^ (m.val + 1))
                (𝓝[>] (0 : ℝ)) (𝓝 0) := by
            intro s
            induction s using Finset.induction_on with
            | empty => simp
            | insert a s ha ih =>
              have h1 := (hterm0 a).add ih
              rw [add_zero] at h1
              refine h1.congr fun u => ?_
              rw [Finset.sum_insert ha]
          exact hgen Finset.univ
        have hrhs0 : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 (H 0)) :=
          hH.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
        exact (tendsto_nhds_unique (hlhs_zero.congr' heq) hrhs0).symm
      let Q : Fin M → Polynomial ℝ := fun m => (P m).divX
      have hQ_deg : ∀ m : Fin M, Q m = 0 ∨ (Q m).natDegree < D := by
        intro m
        by_cases hQm : Q m = 0
        · exact Or.inl hQm
        · right
          rcases hdeg m with hPm0 | hPm_lt
          · exfalso; apply hQm; dsimp [Q]; rw [hPm0]; simp
          · have hdeg_eq : (P m).natDegree = (Q m).natDegree + 1 := by
              rw [hdivX m, Polynomial.natDegree_X_mul hQm]
            omega
      have hQ_eq : ∀ᶠ u in 𝓝[>] (0 : ℝ),
          ∑ m : Fin M, (Q m).eval u * (-Real.log u) ^ (m.val + 1) = dslope H 0 u := by
        filter_upwards [heq, self_mem_nhdsWithin] with u hu hu0
        have hu_ne : u ≠ 0 := ne_of_gt hu0
        rw [dslope_of_ne H hu_ne, slope_def_field, hH_zero, sub_zero, sub_zero, ← hu]
        have hfactor : ∑ m : Fin M, (P m).eval u * (-Real.log u) ^ (m.val + 1) =
            u * ∑ m : Fin M, (Q m).eval u * (-Real.log u) ^ (m.val + 1) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [hP_eval m u]
          dsimp [Q]
          ring
        rw [hfactor]
        field_simp
      have hQ_zero := ih (dslope H 0) (hH.dslope 0) Q hQ_deg hQ_eq
      intro m
      rw [hdivX m]
      exact mul_eq_zero_of_right _ (hQ_zero m)
  set D : ℕ := (Finset.univ : Finset (Fin M)).sup (fun m => (P m).natDegree + 1)
  refine hmain D H hH P (fun m => Or.inr ?_) heq
  exact lt_of_lt_of_le (Nat.lt_succ_self _)
    (Finset.le_sup (f := fun m : Fin M => (P m).natDegree + 1) (Finset.mem_univ m))

/-- **Exact Linear Independence of Poly-Cauchy Densities over `ℝ[u]` (Paper #12 Corollary 7.3):**
For ANY finite sets `S₁, S₂` of positive integer indices (`k ≥ 1`) and polynomials `P, Q : ℕ → ℝ[u]`,
if `∑_{k ∈ S₂} P_k(u) w_k(u) + ∑_{j ∈ S₁} Q_j(u) ρ_j(u) = 0` for all `u ∈ (0, 1)`, then:
1. every second-kind coefficient `P_k = 0` for `k ∈ S₂`, `k ≥ 2`;
2. every first-kind coefficient `Q_j = 0` for `j ∈ S₁`, `j ≥ 2`;
3. the remaining `k = 1` terms satisfy
   `(if 1 ∈ S₂ then P 1 else 0) + (if 1 ∈ S₁ then Q 1 * (X - 1) else 0) = 0`. -/
theorem polyCauchy_densities_poly_indep
    (S₁ S₂ : Finset ℕ) (hS₁ : ∀ j ∈ S₁, 1 ≤ j) (hS₂ : ∀ k ∈ S₂, 1 ≤ k)
    (P Q : ℕ → Polynomial ℝ)
    (hrel : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      (∑ k ∈ S₂, (P k).eval u * polyCauchyW k u) +
      (∑ j ∈ S₁, (Q j).eval u * polyCauchyRho j u) = 0) :
    (∀ k ∈ S₂, 2 ≤ k → P k = 0) ∧
    (∀ j ∈ S₁, 2 ≤ j → Q j = 0) ∧
    ((if 1 ∈ S₂ then P 1 else 0) + (if 1 ∈ S₁ then Q 1 * (Polynomial.X - 1) else 0) = 0) := by
  -- Phase 1: Peel ALL `k ≥ 2` of the 2nd kind at `u → 0⁺`.
  set M₂ : ℕ := S₂.sup id
  let P_scaled : Fin M₂ → Polynomial ℝ := fun m =>
    if m.val + 2 ∈ S₂ then
      Polynomial.C ((((m.val + 1).factorial : ℝ))⁻¹) * P (m.val + 2)
    else 0
  let H₁ : ℝ → ℝ := fun u =>
    -((if 1 ∈ S₂ then (P 1).eval u else 0) + ∑ j ∈ S₁, (Q j).eval u * polyCauchyRho j u)
  have hH₁_an : AnalyticAt ℝ H₁ 0 := by
    apply AnalyticAt.neg
    apply AnalyticAt.add
    · split_ifs
      · exact polynomial_analyticAt (P 1) 0
      · exact analyticAt_const
    · have hgen : ∀ (s : Finset ℕ),
          AnalyticAt ℝ (fun u : ℝ => ∑ j ∈ s, (Q j).eval u * polyCauchyRho j u) 0 := by
        intro s
        induction s using Finset.induction_on with
        | empty => simp; exact analyticAt_const
        | insert a s ha ih =>
          have hfun : (fun u : ℝ => ∑ j ∈ insert a s, (Q j).eval u * polyCauchyRho j u) =
              fun u => (Q a).eval u * polyCauchyRho a u +
                ∑ j ∈ s, (Q j).eval u * polyCauchyRho j u := by
            funext u; exact Finset.sum_insert ha
          rw [hfun]
          refine AnalyticAt.add ?_ ih
          unfold polyCauchyRho polyCauchyW
          have hlog : AnalyticAt ℝ (fun u : ℝ => -Real.log (1 - u)) 0 := by
            have h1 : AnalyticAt ℝ (fun u : ℝ => (1 : ℝ) - u) 0 :=
              analyticAt_const.sub analyticAt_id
            have hpos : (0 : ℝ) < (1 : ℝ) - 0 := by norm_num
            exact (h1.log hpos).neg
          have hsub : AnalyticAt ℝ (fun u : ℝ => u - (1 : ℝ)) 0 :=
            analyticAt_id.sub analyticAt_const
          exact (polynomial_analyticAt (Q a) 0).mul
            (hsub.mul ((hlog.pow (a - 1)).div analyticAt_const (by positivity)))
      exact hgen S₁
  have hPhase1_eq : ∀ᶠ u in 𝓝[>] (0 : ℝ),
      ∑ m : Fin M₂, (P_scaled m).eval u * (-Real.log u) ^ (m.val + 1) = H₁ u := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    have hS2_split :
        ∑ k ∈ S₂, (P k).eval u * polyCauchyW k u =
          (if 1 ∈ S₂ then (P 1).eval u else 0) +
          ∑ m : Fin M₂, (P_scaled m).eval u * (-Real.log u) ^ (m.val + 1) := by
      have h1_val : polyCauchyW 1 u = 1 := by simp [polyCauchyW]
      have herase : ∑ k ∈ S₂, (P k).eval u * polyCauchyW k u =
          (if 1 ∈ S₂ then (P 1).eval u else 0) +
          ∑ k ∈ S₂.erase 1, (P k).eval u * polyCauchyW k u := by
        by_cases h1 : 1 ∈ S₂
        · simp only [h1, ↓reduceIte]
          rw [← Finset.add_sum_erase S₂ _ h1, h1_val, mul_one]
        · simp only [h1, ↓reduceIte, zero_add, Finset.erase_eq_of_notMem h1]
      rw [herase]
      congr 1
      have hfilt : ∑ m : Fin M₂, (P_scaled m).eval u * (-Real.log u) ^ (m.val + 1) =
          ∑ m ∈ (Finset.univ : Finset (Fin M₂)).filter (fun m => m.val + 2 ∈ S₂),
            (P_scaled m).eval u * (-Real.log u) ^ (m.val + 1) := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun m _ hnot => ?_
        have hnot2 : m.val + 2 ∉ S₂ := fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ m, h⟩)
        simp only [P_scaled, hnot2, ↓reduceIte, Polynomial.eval_zero, zero_mul]
      rw [hfilt]
      symm
      refine Finset.sum_bij (fun m _ => m.val + 2) ?_ ?_ ?_ ?_
      · intro m hm
        exact Finset.mem_erase.mpr ⟨by omega, (Finset.mem_filter.mp hm).2⟩
      · intro m₁ _ m₂ _ h
        exact Fin.ext (by omega)
      · intro k hk
        have hk_mem : k ∈ S₂ := Finset.mem_of_mem_erase hk
        have hk_ne1 : k ≠ 1 := (Finset.mem_erase.mp hk).1
        have hk_ge2 : 2 ≤ k := by have := hS₂ k hk_mem; omega
        have hk_le : k ≤ M₂ := Finset.le_sup (f := id) hk_mem
        refine ⟨⟨k - 2, by omega⟩, ?_, by dsimp; omega⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa [Nat.sub_add_cancel hk_ge2] using hk_mem
      · intro m hm
        have hm' : m.val + 2 ∈ S₂ := (Finset.mem_filter.mp hm).2
        simp only [P_scaled, hm', ↓reduceIte, Polynomial.eval_mul, Polynomial.eval_C]
        unfold polyCauchyW
        rw [show m.val + 2 - 1 = m.val + 1 by omega]
        ring
    have h0 := hrel u hu
    rw [hS2_split] at h0
    dsimp [H₁]
    linarith
  have hP2_zero : ∀ k ∈ S₂, 2 ≤ k → P k = 0 := by
    have hzero_scaled := poly_log_analytic_eq_zero hH₁_an P_scaled hPhase1_eq
    intro k hk hk2
    have hk_le : k ≤ M₂ := Finset.le_sup (f := id) hk
    let m : Fin M₂ := ⟨k - 2, by omega⟩
    have hm_eq : m.val + 2 = k := by dsimp [m]; omega
    have h0 := hzero_scaled m
    simp only [P_scaled, hm_eq, hk, ↓reduceIte] at h0
    have hfac_ne : ((((m.val + 1).factorial : ℝ))⁻¹) ≠ 0 :=
      inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
    have hC_ne : Polynomial.C ((((m.val + 1).factorial : ℝ))⁻¹) ≠ 0 := by
      simpa using hfac_ne
    exact (mul_eq_zero.mp h0).resolve_left hC_ne
  -- Phase 2: Substitute `u = 1 - v` and peel ALL `j ≥ 2` of the 1st kind at `v → 0⁺`!
  have hAfter1 : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      (if 1 ∈ S₂ then (P 1).eval u else 0) +
      (∑ j ∈ S₁, (Q j).eval u * polyCauchyRho j u) = 0 := by
    intro u hu
    have h0 := hrel u hu
    have hS2_col : ∑ k ∈ S₂, (P k).eval u * polyCauchyW k u =
        if 1 ∈ S₂ then (P 1).eval u else 0 := by
      by_cases h1 : 1 ∈ S₂
      · simp only [h1, ↓reduceIte]
        rw [Finset.sum_eq_single 1]
        · simp [polyCauchyW]
        · intro k hk hne
          have hk2 : 2 ≤ k := by have := hS₂ k hk; omega
          rw [hP2_zero k hk hk2, Polynomial.eval_zero, zero_mul]
        · intro hnot; exact absurd h1 hnot
      · simp only [h1, ↓reduceIte]
        refine Finset.sum_eq_zero fun k hk => ?_
        have hk2 : 2 ≤ k := by
          have := hS₂ k hk
          have hne : k ≠ 1 := fun h => h1 (h ▸ hk)
          omega
        rw [hP2_zero k hk hk2, Polynomial.eval_zero, zero_mul]
    rwa [hS2_col] at h0
  set M₁ : ℕ := S₁.sup id
  let flipPoly : Polynomial ℝ := 1 - Polynomial.X
  let Q_scaled : Fin M₁ → Polynomial ℝ := fun m =>
    if m.val + 2 ∈ S₁ then
      -Polynomial.C ((((m.val + 1).factorial : ℝ))⁻¹) * Polynomial.X *
        (Q (m.val + 2)).comp flipPoly
    else 0
  let H₂_poly : Polynomial ℝ :=
    -(if 1 ∈ S₂ then (P 1).comp flipPoly else 0) +
      (if 1 ∈ S₁ then Polynomial.X * (Q 1).comp flipPoly else 0)
  have hH₂_an : AnalyticAt ℝ (fun v : ℝ => H₂_poly.eval v) 0 :=
    polynomial_analyticAt H₂_poly 0
  have hPhase2_eq : ∀ᶠ v in 𝓝[>] (0 : ℝ),
      ∑ m : Fin M₁, (Q_scaled m).eval v * (-Real.log v) ^ (m.val + 1) = H₂_poly.eval v := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with v hv
    have hu : 1 - v ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith [hv.2], by linarith [hv.1]⟩
    have h0 := hAfter1 (1 - v) hu
    have hflip : flipPoly.eval v = 1 - v := by simp [flipPoly]
    have h1mv : (1 : ℝ) - (1 - v) = v := by ring
    have hS1_split :
        ∑ j ∈ S₁, (Q j).eval (1 - v) * polyCauchyRho j (1 - v) =
          (if 1 ∈ S₁ then -(v * ((Q 1).comp flipPoly).eval v) else 0) +
          ∑ m : Fin M₁, (Q_scaled m).eval v * (-Real.log v) ^ (m.val + 1) := by
      have herase : ∑ j ∈ S₁, (Q j).eval (1 - v) * polyCauchyRho j (1 - v) =
          (if 1 ∈ S₁ then -(v * ((Q 1).comp flipPoly).eval v) else 0) +
          ∑ j ∈ S₁.erase 1, (Q j).eval (1 - v) * polyCauchyRho j (1 - v) := by
        by_cases h1 : 1 ∈ S₁
        · simp only [h1, ↓reduceIte]
          rw [← Finset.add_sum_erase S₁ _ h1]
          congr 1
          unfold polyCauchyRho polyCauchyW
          rw [Polynomial.eval_comp, hflip]
          simp
          ring
        · simp only [h1, ↓reduceIte, zero_add, Finset.erase_eq_of_notMem h1]
      rw [herase]
      congr 1
      have hfilt : ∑ m : Fin M₁, (Q_scaled m).eval v * (-Real.log v) ^ (m.val + 1) =
          ∑ m ∈ (Finset.univ : Finset (Fin M₁)).filter (fun m => m.val + 2 ∈ S₁),
            (Q_scaled m).eval v * (-Real.log v) ^ (m.val + 1) := by
        symm
        refine Finset.sum_subset (Finset.filter_subset _ _) fun m _ hnot => ?_
        have hnot2 : m.val + 2 ∉ S₁ := fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ m, h⟩)
        simp only [Q_scaled, hnot2, ↓reduceIte, Polynomial.eval_zero, zero_mul]
      rw [hfilt]
      symm
      refine Finset.sum_bij (fun m _ => m.val + 2) ?_ ?_ ?_ ?_
      · intro m hm
        exact Finset.mem_erase.mpr ⟨by omega, (Finset.mem_filter.mp hm).2⟩
      · intro m₁ _ m₂ _ h; exact Fin.ext (by omega)
      · intro j hj
        have hj_mem : j ∈ S₁ := Finset.mem_of_mem_erase hj
        have hj_ne1 : j ≠ 1 := (Finset.mem_erase.mp hj).1
        have hj_ge2 : 2 ≤ j := by have := hS₁ j hj_mem; omega
        have hj_le : j ≤ M₁ := Finset.le_sup (f := id) hj_mem
        refine ⟨⟨j - 2, by omega⟩, ?_, by dsimp; omega⟩
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa [Nat.sub_add_cancel hj_ge2] using hj_mem
      · intro m hm
        have hm' : m.val + 2 ∈ S₁ := (Finset.mem_filter.mp hm).2
        simp only [Q_scaled, hm', ↓reduceIte, Polynomial.eval_mul, Polynomial.eval_neg,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_comp, hflip]
        unfold polyCauchyRho polyCauchyW
        rw [h1mv, show m.val + 2 - 1 = m.val + 1 by omega]
        ring
    rw [hS1_split] at h0
    have hH2_eval : H₂_poly.eval v =
        -(if 1 ∈ S₂ then (P 1).eval (1 - v) else 0) +
          (if 1 ∈ S₁ then v * ((Q 1).comp flipPoly).eval v else 0) := by
      dsimp [H₂_poly]
      rw [Polynomial.eval_add, Polynomial.eval_neg]
      congr 1
      · split_ifs <;> simp [Polynomial.eval_comp, hflip]
      · split_ifs <;> simp [Polynomial.eval_comp, hflip]
    rw [hH2_eval]
    split_ifs at h0 ⊢ <;> linarith
  have hQ2_zero : ∀ j ∈ S₁, 2 ≤ j → Q j = 0 := by
    have hzero_scaled := poly_log_analytic_eq_zero hH₂_an Q_scaled hPhase2_eq
    intro j hj hj2
    have hj_le : j ≤ M₁ := Finset.le_sup (f := id) hj
    let m : Fin M₁ := ⟨j - 2, by omega⟩
    have hm_eq : m.val + 2 = j := by dsimp [m]; omega
    have h0 := hzero_scaled m
    simp only [Q_scaled, hm_eq, hj, ↓reduceIte] at h0
    have hC_ne : -Polynomial.C ((((m.val + 1).factorial : ℝ))⁻¹) ≠ 0 := by
      intro hc
      have h1 := congrArg (fun p : Polynomial ℝ => p.coeff 0) hc
      simp at h1
      exact Nat.factorial_ne_zero (m.val + 1) h1
    have hX_ne : (Polynomial.X : Polynomial ℝ) ≠ 0 := Polynomial.X_ne_zero
    have hcomp0 : (Q j).comp flipPoly = 0 :=
      (mul_eq_zero.mp h0).resolve_left (mul_ne_zero hC_ne hX_ne)
    have hinv_flip : flipPoly.comp flipPoly = Polynomial.X := by
      dsimp [flipPoly]
      simp [Polynomial.sub_comp]
    have hQ0 : Q j = ((Q j).comp flipPoly).comp flipPoly := by
      rw [Polynomial.comp_assoc, hinv_flip, Polynomial.comp_X]
    rw [hQ0, hcomp0, Polynomial.zero_comp]
  -- Phase 3: Remaining `k = 1` polynomial identity on the infinite set `(0, 1)`.
  have hk1_rel : (if 1 ∈ S₂ then P 1 else 0) +
      (if 1 ∈ S₁ then Q 1 * (Polynomial.X - 1) else 0) = 0 := by
    let R : Polynomial ℝ := (if 1 ∈ S₂ then P 1 else 0) +
      (if 1 ∈ S₁ then Q 1 * (Polynomial.X - 1) else 0)
    have hR_zero_on : ∀ u ∈ Set.Ioo (0 : ℝ) 1, R.eval u = 0 := by
      intro u hu
      have h0 := hAfter1 u hu
      have hS1_col : ∑ j ∈ S₁, (Q j).eval u * polyCauchyRho j u =
          if 1 ∈ S₁ then (Q 1).eval u * (u - 1) else 0 := by
        by_cases h1 : 1 ∈ S₁
        · simp only [h1, ↓reduceIte]
          rw [Finset.sum_eq_single 1]
          · simp [polyCauchyRho, polyCauchyW]
          · intro j hj hne
            have hj2 : 2 ≤ j := by have := hS₁ j hj; omega
            rw [hQ2_zero j hj hj2, Polynomial.eval_zero, zero_mul]
          · intro hnot; exact absurd h1 hnot
        · simp only [h1, ↓reduceIte]
          refine Finset.sum_eq_zero fun j hj => ?_
          have hj2 : 2 ≤ j := by
            have := hS₁ j hj
            have hne : j ≠ 1 := fun h => h1 (h ▸ hj)
            omega
          rw [hQ2_zero j hj hj2, Polynomial.eval_zero, zero_mul]
      rw [hS1_col] at h0
      dsimp [R]
      rw [Polynomial.eval_add]
      have hp : (if 1 ∈ S₂ then P 1 else 0).eval u = if 1 ∈ S₂ then (P 1).eval u else 0 := by
        split_ifs <;> simp
      have hq : (if 1 ∈ S₁ then Q 1 * (Polynomial.X - 1) else 0).eval u =
          if 1 ∈ S₁ then (Q 1).eval u * (u - 1) else 0 := by
        split_ifs <;> simp
      rw [hp, hq]
      exact h0
    by_contra hRne
    have hroots_fin : (R.roots.toFinset : Set ℝ).Finite := Finset.finite_toSet _
    have hsub : Set.Ioo (0 : ℝ) 1 ⊆ (R.roots.toFinset : Set ℝ) := by
      intro u hu
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hRne]
      exact hR_zero_on u hu
    exact (Set.Ioo_infinite (zero_lt_one : (0 : ℝ) < 1)) (hroots_fin.subset hsub)
  exact ⟨hP2_zero, hQ2_zero, hk1_rel⟩

/-- Corollary (No `k = 1` collision): if `¬ (1 ∈ S₁ ∧ 1 ∈ S₂)`, every polynomial dependence among
the selected poly-Cauchy densities is identically zero. -/
theorem polyCauchy_densities_poly_indep_of_not_both_one
    (S₁ S₂ : Finset ℕ) (hS₁ : ∀ j ∈ S₁, 1 ≤ j) (hS₂ : ∀ k ∈ S₂, 1 ≤ k)
    (hnot : ¬ (1 ∈ S₁ ∧ 1 ∈ S₂))
    (P Q : ℕ → Polynomial ℝ)
    (hrel : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      (∑ k ∈ S₂, (P k).eval u * polyCauchyW k u) +
      (∑ j ∈ S₁, (Q j).eval u * polyCauchyRho j u) = 0) :
    (∀ k ∈ S₂, P k = 0) ∧ (∀ j ∈ S₁, Q j = 0) := by
  obtain ⟨hP2, hQ2, hk1⟩ := polyCauchy_densities_poly_indep S₁ S₂ hS₁ hS₂ P Q hrel
  have hX1_ne : (Polynomial.X - 1 : Polynomial ℝ) ≠ 0 := by
    intro h
    have := congrArg (fun p : Polynomial ℝ => p.eval 0) h
    simp at this
  constructor
  · intro k hk
    by_cases hk1_eq : k = 1
    · subst hk1_eq
      have h1_not : 1 ∉ S₁ := fun h => hnot ⟨h, hk⟩
      simp only [hk, h1_not, ↓reduceIte, add_zero] at hk1
      exact hk1
    · exact hP2 k hk (by have := hS₂ k hk; omega)
  · intro j hj
    by_cases hj1_eq : j = 1
    · subst hj1_eq
      have h1_not : 1 ∉ S₂ := fun h => hnot ⟨hj, h⟩
      simp only [h1_not, hj, ↓reduceIte, zero_add] at hk1
      exact (mul_eq_zero.mp hk1).resolve_right hX1_ne
    · exact hQ2 j hj (by have := hS₁ j hj; omega)

/-- Corollary (`k = 1` collision): if BOTH `1 ∈ S₁` and `1 ∈ S₂`, every `k ≥ 2` coefficient
vanishes and the unique polynomial relation is `P 1 = (1 - X) * Q 1`. -/
theorem polyCauchy_densities_both_one_relation
    (S₁ S₂ : Finset ℕ) (hS₁ : ∀ j ∈ S₁, 1 ≤ j) (hS₂ : ∀ k ∈ S₂, 1 ≤ k)
    (h1 : 1 ∈ S₁) (h2 : 1 ∈ S₂)
    (P Q : ℕ → Polynomial ℝ)
    (hrel : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      (∑ k ∈ S₂, (P k).eval u * polyCauchyW k u) +
      (∑ j ∈ S₁, (Q j).eval u * polyCauchyRho j u) = 0) :
    (∀ k ∈ S₂, 2 ≤ k → P k = 0) ∧
    (∀ j ∈ S₁, 2 ≤ j → Q j = 0) ∧
    P 1 = (1 - Polynomial.X) * Q 1 := by
  obtain ⟨hP2, hQ2, hk1⟩ := polyCauchy_densities_poly_indep S₁ S₂ hS₁ hS₂ P Q hrel
  simp only [h2, h1, ↓reduceIte] at hk1
  refine ⟨hP2, hQ2, ?_⟩
  have h : P 1 = -(Q 1 * (Polynomial.X - 1)) := eq_neg_of_add_eq_zero_left hk1
  rw [h]; ring

/-- **Exact Jet-Span Rank Formula for Poly-Cauchy Densities (Paper #12 Corollary 7.3):**
For any finite selections `S₁, S₂` of positive indices and jet order `J : ℕ`, let `V` be the
`ℝ`-linear span on `(0, 1)` of all polynomial-weighted densities
`{u ↦ u^r w_k(u) : k ∈ S₂, 0 ≤ r ≤ J} ∪ {u ↦ u^r ρ_j(u) : j ∈ S₁, 0 ≤ r ≤ J}`.
Then:
- if `¬ (1 ∈ S₁ ∧ 1 ∈ S₂)`, `Module.finrank ℝ V = (S₁.card + S₂.card) * (J + 1)`;
- if `1 ∈ S₁ ∧ 1 ∈ S₂`, `Module.finrank ℝ V = (S₁.card + S₂.card - 1) * (J + 1) + 1`
  (losing **exact 1 differential transcendence degree**!). -/
theorem polyCauchy_jet_span_finrank
    (S₁ S₂ : Finset ℕ) (hS₁ : ∀ j ∈ S₁, 1 ≤ j) (hS₂ : ∀ k ∈ S₂, 1 ≤ k) (J : ℕ) :
    let gen : ((S₂ × Fin (J + 1)) ⊕ (S₁ × Fin (J + 1))) → (Set.Ioo (0 : ℝ) 1 → ℝ) :=
      Sum.elim (fun p u => (u.1 : ℝ) ^ (p.2 : ℕ) * polyCauchyW p.1.1 u.1)
               (fun p u => (u.1 : ℝ) ^ (p.2 : ℕ) * polyCauchyRho p.1.1 u.1)
    Module.finrank ℝ (Submodule.span ℝ (Set.range gen)) =
      if 1 ∈ S₁ ∧ 1 ∈ S₂ then (S₁.card + S₂.card - 1) * (J + 1) + 1
      else (S₁.card + S₂.card) * (J + 1) := by
  intro gen
  split_ifs with hboth
  · rcases hboth with ⟨h1, h2⟩
    let I' := ((S₂ × Fin (J + 1)) ⊕ ((S₁.erase 1) × Fin (J + 1))) ⊕ Unit
    let gen' : I' → (Set.Ioo (0 : ℝ) 1 → ℝ) :=
      Sum.elim
        (Sum.elim (fun p u => (u.1 : ℝ) ^ (p.2 : ℕ) * polyCauchyW p.1.1 u.1)
                  (fun p u => (u.1 : ℝ) ^ (p.2 : ℕ) * polyCauchyRho p.1.1 u.1))
        (fun _ u => (u.1 : ℝ) ^ J * polyCauchyRho 1 u.1)
    have hspan_eq : Submodule.span ℝ (Set.range gen) = Submodule.span ℝ (Set.range gen') := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨idx, rfl⟩
        cases idx with
        | inl p =>
          exact Submodule.subset_span ⟨Sum.inl (Sum.inl p), rfl⟩
        | inr p =>
          by_cases hp1 : p.1.1 = 1
          · by_cases hrJ : p.2.val = J
            · have hEq : gen (Sum.inr p) = gen' (Sum.inr ()) := by
                funext u; simp [gen, gen', hp1, hrJ]
              rw [hEq]
              exact Submodule.subset_span ⟨Sum.inr (), rfl⟩
            · have hr_lt : p.2.val < J := by omega
              let p_succ : S₂ × Fin (J + 1) := (⟨1, h2⟩, ⟨p.2.val + 1, by omega⟩)
              let p_curr : S₂ × Fin (J + 1) := (⟨1, h2⟩, p.2)
              have hEq : gen (Sum.inr p) =
                  gen' (Sum.inl (Sum.inl p_succ)) - gen' (Sum.inl (Sum.inl p_curr)) := by
                funext u
                simp only [gen, gen', Sum.elim_inr, Sum.elim_inl, Pi.sub_apply, hp1,
                  polyCauchyRho, polyCauchyW, p_succ, p_curr]
                simp [pow_succ]
                ring
              rw [hEq]
              exact Submodule.sub_mem _
                (Submodule.subset_span ⟨Sum.inl (Sum.inl p_succ), rfl⟩)
                (Submodule.subset_span ⟨Sum.inl (Sum.inl p_curr), rfl⟩)
          · exact Submodule.subset_span
              ⟨Sum.inl (Sum.inr (⟨p.1.1, Finset.mem_erase.mpr ⟨hp1, p.1.2⟩⟩, p.2)), rfl⟩
      · rw [Submodule.span_le]
        rintro _ ⟨idx, rfl⟩
        cases idx with
        | inl p =>
          cases p with
          | inl q => exact Submodule.subset_span ⟨Sum.inl q, rfl⟩
          | inr q =>
            exact Submodule.subset_span
              ⟨Sum.inr (⟨q.1.1, Finset.mem_of_mem_erase q.1.2⟩, q.2), rfl⟩
        | inr _ =>
          exact Submodule.subset_span ⟨Sum.inr (⟨1, h1⟩, ⟨J, Nat.lt_succ_self J⟩), rfl⟩
    have hlin' : LinearIndependent ℝ gen' := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      let P : ℕ → Polynomial ℝ := fun k =>
        if hk : k ∈ S₂ then
          ∑ r : Fin (J + 1), Polynomial.C (c (Sum.inl (Sum.inl (⟨k, hk⟩, r)))) * Polynomial.X ^ (r : ℕ)
        else 0
      let Q : ℕ → Polynomial ℝ := fun j =>
        if hj1 : j = 1 then
          Polynomial.C (c (Sum.inr ())) * Polynomial.X ^ J
        else if hj : j ∈ S₁.erase 1 then
          ∑ r : Fin (J + 1), Polynomial.C (c (Sum.inl (Sum.inr (⟨j, hj⟩, r)))) * Polynomial.X ^ (r : ℕ)
        else 0
      have hrel : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
          (∑ k ∈ S₂, (P k).eval u * polyCauchyW k u) +
          (∑ j ∈ S₁, (Q j).eval u * polyCauchyRho j u) = 0 := by
        intro u hu
        have hev := congrFun hc ⟨u, hu⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type,
          Fintype.sum_prod_type] at hev
        have hunit : (∑ a : Unit, c (Sum.inr a) * gen' (Sum.inr a) ⟨u, hu⟩) =
            c (Sum.inr ()) * gen' (Sum.inr ()) ⟨u, hu⟩ := Fintype.sum_unique _
        rw [hunit] at hev
        have hS2_eq : ∑ k ∈ S₂, (P k).eval u * polyCauchyW k u =
            ∑ k : S₂, ∑ r : Fin (J + 1),
              c (Sum.inl (Sum.inl (k, r))) * gen' (Sum.inl (Sum.inl (k, r))) ⟨u, hu⟩ := by
          rw [← Finset.sum_attach S₂]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [P, k.2, ↓reduceDIte, gen', Sum.elim_inl, poly_eval_finset_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
            mul_assoc]
        have hS1_eq : ∑ j ∈ S₁, (Q j).eval u * polyCauchyRho j u =
            (∑ j : S₁.erase 1, ∑ r : Fin (J + 1),
              c (Sum.inl (Sum.inr (j, r))) * gen' (Sum.inl (Sum.inr (j, r))) ⟨u, hu⟩) +
            c (Sum.inr ()) * gen' (Sum.inr ()) ⟨u, hu⟩ := by
          rw [← Finset.add_sum_erase S₁ _ h1, add_comm]
          congr 1
          · rw [← Finset.sum_attach (S₁.erase 1)]
            refine Finset.sum_congr rfl fun j _ => ?_
            have hne1 : j.1 ≠ 1 := (Finset.mem_erase.mp j.2).1
            simp only [Q, hne1, j.2, ↓reduceDIte, gen', Sum.elim_inl, Sum.elim_inr,
              poly_eval_finset_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun r _ => ?_
            simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
              mul_assoc]
          · simp only [Q, ↓reduceDIte, gen', Sum.elim_inr]
            simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
              mul_assoc]
        rw [hS2_eq, hS1_eq]
        linarith
      obtain ⟨hP2, hQ2, hP1_eq⟩ := polyCauchy_densities_both_one_relation S₁ S₂ hS₁ hS₂ h1 h2 P Q hrel
      have hP1_deg : (P 1).coeff (J + 1) = 0 := by
        simp only [P, h2, ↓reduceDIte, poly_finset_sum_coeff]
        refine Finset.sum_eq_zero fun r _ => ?_
        have hne : J + 1 ≠ r.val := by omega
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne]
      have hQ1_eq : Q 1 = Polynomial.C (c (Sum.inr ())) * Polynomial.X ^ J := by
        simp [Q]
      have hTop : ((1 - Polynomial.X) * Q 1).coeff (J + 1) = -c (Sum.inr ()) := by
        rw [hQ1_eq]
        have hsub : (1 - Polynomial.X) * (Polynomial.C (c (Sum.inr ())) * Polynomial.X ^ J) =
            Polynomial.C (c (Sum.inr ())) * Polynomial.X ^ J -
            Polynomial.C (c (Sum.inr ())) * Polynomial.X ^ (J + 1) := by
          rw [pow_succ]; ring
        rw [hsub, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        have hne : J + 1 ≠ J := by omega
        simp only [hne, ↓reduceIte]
        ring
      have hc_top : c (Sum.inr ()) = 0 := by
        have h := congrArg (fun p : Polynomial ℝ => p.coeff (J + 1)) hP1_eq
        rw [hP1_deg, hTop] at h
        linarith
      have hP1_zero : P 1 = 0 := by
        rw [hP1_eq, hQ1_eq, hc_top, map_zero, zero_mul, mul_zero]
      intro idx
      cases idx with
      | inr u =>
        cases u; exact hc_top
      | inl p =>
        cases p with
        | inl q =>
          have hPq0 : P q.1.1 = 0 := by
            by_cases hq1 : q.1.1 = 1
            · rw [hq1]; exact hP1_zero
            · exact hP2 q.1.1 q.1.2 (by have := hS₂ q.1.1 q.1.2; omega)
          have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff q.2.val) hPq0
          simp only [P, q.1.2, ↓reduceDIte, poly_finset_sum_coeff, Polynomial.coeff_zero] at hcoeff
          rw [Finset.sum_eq_single q.2] at hcoeff
          · simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hcoeff
          · intro r _ hne
            have hne' : q.2.val ≠ r.val := fun h => hne (Fin.ext h.symm)
            simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne']
          · intro hnot; exact absurd (Finset.mem_univ q.2) hnot
        | inr q =>
          have hne1 : q.1.1 ≠ 1 := (Finset.mem_erase.mp q.1.2).1
          have hmem1 : q.1.1 ∈ S₁ := Finset.mem_of_mem_erase q.1.2
          have hQq0 : Q q.1.1 = 0 := hQ2 q.1.1 hmem1 (by have := hS₁ q.1.1 hmem1; omega)
          have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff q.2.val) hQq0
          simp only [Q, hne1, q.1.2, ↓reduceDIte, poly_finset_sum_coeff,
            Polynomial.coeff_zero] at hcoeff
          rw [Finset.sum_eq_single q.2] at hcoeff
          · simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hcoeff
          · intro r _ hne
            have hne' : q.2.val ≠ r.val := fun h => hne (Fin.ext h.symm)
            simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne']
          · intro hnot; exact absurd (Finset.mem_univ q.2) hnot
    rw [hspan_eq, finrank_span_eq_card hlin']
    have hcard_S1 : 1 ≤ S₁.card := Finset.card_pos.mpr ⟨1, h1⟩
    simp only [I', Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
      Fintype.card_unit, Finset.card_erase_of_mem h1]
    have hmul_sum : S₂.card * (J + 1) + (S₁.card - 1) * (J + 1) =
        (S₁.card + S₂.card - 1) * (J + 1) := by
      rw [← add_mul]
      congr 1
      omega
    omega
  · have hlin : LinearIndependent ℝ gen := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      let P : ℕ → Polynomial ℝ := fun k =>
        if hk : k ∈ S₂ then
          ∑ r : Fin (J + 1), Polynomial.C (c (Sum.inl (⟨k, hk⟩, r))) * Polynomial.X ^ (r : ℕ)
        else 0
      let Q : ℕ → Polynomial ℝ := fun j =>
        if hj : j ∈ S₁ then
          ∑ r : Fin (J + 1), Polynomial.C (c (Sum.inr (⟨j, hj⟩, r))) * Polynomial.X ^ (r : ℕ)
        else 0
      have hrel : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
          (∑ k ∈ S₂, (P k).eval u * polyCauchyW k u) +
          (∑ j ∈ S₁, (Q j).eval u * polyCauchyRho j u) = 0 := by
        intro u hu
        have hev := congrFun hc ⟨u, hu⟩
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hev
        rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hev
        have hS2_eq : ∑ k ∈ S₂, (P k).eval u * polyCauchyW k u =
            ∑ k : S₂, ∑ r : Fin (J + 1),
              c (Sum.inl (k, r)) * gen (Sum.inl (k, r)) ⟨u, hu⟩ := by
          rw [← Finset.sum_attach S₂]
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [P, k.2, ↓reduceDIte, gen, Sum.elim_inl, poly_eval_finset_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
            mul_assoc]
        have hS1_eq : ∑ j ∈ S₁, (Q j).eval u * polyCauchyRho j u =
            ∑ j : S₁, ∑ r : Fin (J + 1),
              c (Sum.inr (j, r)) * gen (Sum.inr (j, r)) ⟨u, hu⟩ := by
          rw [← Finset.sum_attach S₁]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [Q, j.2, ↓reduceDIte, gen, Sum.elim_inr, poly_eval_finset_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun r _ => ?_
          simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
            mul_assoc]
        rw [hS2_eq, hS1_eq]
        exact hev
      obtain ⟨hP0, hQ0⟩ := polyCauchy_densities_poly_indep_of_not_both_one S₁ S₂ hS₁ hS₂ hboth P Q hrel
      intro idx
      cases idx with
      | inl q =>
        have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff q.2.val) (hP0 q.1.1 q.1.2)
        simp only [P, q.1.2, ↓reduceDIte, poly_finset_sum_coeff, Polynomial.coeff_zero] at hcoeff
        rw [Finset.sum_eq_single q.2] at hcoeff
        · simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hcoeff
        · intro r _ hne
          have hne' : q.2.val ≠ r.val := fun h => hne (Fin.ext h.symm)
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne']
        · intro hnot; exact absurd (Finset.mem_univ q.2) hnot
      | inr q =>
        have hcoeff := congrArg (fun p : Polynomial ℝ => p.coeff q.2.val) (hQ0 q.1.1 q.1.2)
        simp only [Q, q.1.2, ↓reduceDIte, poly_finset_sum_coeff, Polynomial.coeff_zero] at hcoeff
        rw [Finset.sum_eq_single q.2] at hcoeff
        · simpa [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow] using hcoeff
        · intro r _ hne
          have hne' : q.2.val ≠ r.val := fun h => hne (Fin.ext h.symm)
          simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, hne']
        · intro hnot; exact absurd (Finset.mem_univ q.2) hnot
    rw [finrank_span_eq_card hlin]
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
    ring

/-! #### Nonpositive-Index Poly-Cauchy D-Finiteness (`L_{-ℓ}(v) = (1 + v ∂_v)^ℓ e^v = P_ℓ(v) e^v`) -/

/-- Explicit Euler-Bell polynomials `P_ℓ(v)` satisfying `(1 + v ∂_v)^ℓ e^v = P_ℓ(v) e^v`:
`P_0 = 1`, `P_{ℓ+1} = (1 + X) P_ℓ + X P_ℓ'`. -/
def polyCauchyEulerPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | ℓ + 1 =>
    (1 + Polynomial.X) * polyCauchyEulerPoly ℓ +
      Polynomial.X * Polynomial.derivative (polyCauchyEulerPoly ℓ)

/-- First-order Euler differential operator `(eulerDiffOp f)(v) = f(v) + v f'(v)`. -/
def eulerDiffOp (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  f v + v * deriv f v

/-- Every `polyCauchyEulerPoly ℓ` is monic of exact degree `ℓ`. -/
theorem polyCauchyEulerPoly_monic_and_natDegree (ℓ : ℕ) :
    (polyCauchyEulerPoly ℓ).Monic ∧ (polyCauchyEulerPoly ℓ).natDegree = ℓ := by
  induction ℓ with
  | zero =>
    simp [polyCauchyEulerPoly]
  | succ k ih =>
    rcases ih with ⟨hmon, hdeg⟩
    have hPne : polyCauchyEulerPoly k ≠ 0 := hmon.ne_zero
    have h1X_mon : (1 + Polynomial.X : Polynomial ℝ).Monic := by
      rw [add_comm]
      exact Polynomial.monic_X_add_C 1
    have h1X_deg : (1 + Polynomial.X : Polynomial ℝ).natDegree = 1 := by
      rw [add_comm]
      exact Polynomial.natDegree_X_add_C 1
    have hmul_mon : ((1 + Polynomial.X) * polyCauchyEulerPoly k).Monic := h1X_mon.mul hmon
    have hmul_deg : ((1 + Polynomial.X) * polyCauchyEulerPoly k).natDegree = k + 1 := by
      rw [Polynomial.natDegree_mul h1X_mon.ne_zero hPne, h1X_deg, hdeg]
      omega
    have hrem_deg : (Polynomial.X * Polynomial.derivative (polyCauchyEulerPoly k)).natDegree < k + 1 := by
      by_cases hd0 : Polynomial.derivative (polyCauchyEulerPoly k) = 0
      · simp [hd0]
      · rw [Polynomial.natDegree_X_mul hd0]
        have hlt := Polynomial.natDegree_derivative_lt (p := polyCauchyEulerPoly k) (by
          intro h0
          rw [h0] at hdeg
          cases k with
          | zero => simp [polyCauchyEulerPoly] at hd0
          | succ _ => omega)
        omega
    have hlt_deg : (Polynomial.X * Polynomial.derivative (polyCauchyEulerPoly k)).degree <
        ((1 + Polynomial.X) * polyCauchyEulerPoly k).degree := by
      rw [Polynomial.degree_eq_natDegree hmul_mon.ne_zero, hmul_deg]
      by_cases h0 : Polynomial.X * Polynomial.derivative (polyCauchyEulerPoly k) = 0
      · rw [h0, Polynomial.degree_zero]
        exact WithBot.bot_lt_coe _
      · rw [Polynomial.degree_eq_natDegree h0]
        exact WithBot.coe_lt_coe.mpr hrem_deg
    have hstep : polyCauchyEulerPoly (k + 1) =
        (1 + Polynomial.X) * polyCauchyEulerPoly k +
        Polynomial.X * Polynomial.derivative (polyCauchyEulerPoly k) := rfl
    constructor
    · rw [hstep]
      exact hmul_mon.add_of_left hlt_deg
    · rw [hstep, Polynomial.natDegree_add_eq_left_of_degree_lt hlt_deg, hmul_deg]

/-- Iterated Euler operator identity `(1 + v ∂_v)^ℓ e^v = P_ℓ(v) e^v` for all `ℓ : ℕ`, `v : ℝ`. -/
theorem iterated_eulerDiffOp_exp (ℓ : ℕ) :
    (eulerDiffOp^[ℓ] Real.exp) = fun v : ℝ => (polyCauchyEulerPoly ℓ).eval v * Real.exp v := by
  induction ℓ with
  | zero =>
    funext v
    simp [polyCauchyEulerPoly]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    funext v
    have hstep : polyCauchyEulerPoly (k + 1) =
        (1 + Polynomial.X) * polyCauchyEulerPoly k +
        Polynomial.X * Polynomial.derivative (polyCauchyEulerPoly k) := rfl
    have hderiv : HasDerivAt (fun x : ℝ => (polyCauchyEulerPoly k).eval x * Real.exp x)
        ((Polynomial.derivative (polyCauchyEulerPoly k)).eval v * Real.exp v +
          (polyCauchyEulerPoly k).eval v * Real.exp v) v := by
      have h1 : HasDerivAt (fun x : ℝ => (polyCauchyEulerPoly k).eval x)
          ((Polynomial.derivative (polyCauchyEulerPoly k)).eval v) v :=
        Polynomial.hasDerivAt (polyCauchyEulerPoly k) v
      exact h1.fun_mul (Real.hasDerivAt_exp v)
    dsimp only [eulerDiffOp]
    rw [hderiv.deriv, hstep]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_X]
    ring

/-- Formal power series Euler-operator identity:
`∑_{m ≥ 0} (m + 1)^ℓ v^m / m! = P_ℓ(v) * exp(v)` in `PowerSeries ℝ`. -/
theorem polyCauchy_nonpos_powerSeries (ℓ : ℕ) :
    PowerSeries.mk (fun m : ℕ => ((m + 1 : ℝ) ^ ℓ) / (m.factorial : ℝ)) =
      ((polyCauchyEulerPoly ℓ : Polynomial ℝ) : PowerSeries ℝ) * PowerSeries.exp ℝ := by
  induction ℓ with
  | zero =>
    ext m
    simp [polyCauchyEulerPoly, PowerSeries.coeff_exp]
  | succ k ih =>
    have hlhs :
        PowerSeries.mk (fun m : ℕ => ((m + 1 : ℝ) ^ (k + 1)) / (m.factorial : ℝ)) =
          PowerSeries.mk (fun m : ℕ => ((m + 1 : ℝ) ^ k) / (m.factorial : ℝ)) +
          PowerSeries.X *
            PowerSeries.derivative
              (PowerSeries.mk (fun m : ℕ => ((m + 1 : ℝ) ^ k) / (m.factorial : ℝ))) := by
      ext m
      cases m with
      | zero => simp
      | succ n =>
        rw [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
        simp only [PowerSeries.coeff_mk, Nat.cast_add, Nat.cast_one]
        have hfac : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
        have hfn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
        rw [hfac, pow_succ]
        field_simp
        ring
    have hexp_deriv : PowerSeries.derivative (PowerSeries.exp ℝ) = PowerSeries.exp ℝ := by
      ext m
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_exp, PowerSeries.coeff_exp]
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        map_div₀, map_one, map_mul, map_add, map_natCast]
      have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have hfm : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
      field_simp
    have hpoly_deriv : ∀ p : Polynomial ℝ,
        PowerSeries.derivative (p : PowerSeries ℝ) =
          ((Polynomial.derivative p : Polynomial ℝ) : PowerSeries ℝ) := by
      intro p
      ext m
      rw [PowerSeries.coeff_derivative, Polynomial.coeff_coe, Polynomial.coeff_coe,
        Polynomial.coeff_derivative]
    have hstep : polyCauchyEulerPoly (k + 1) =
        (1 + Polynomial.X) * polyCauchyEulerPoly k +
        Polynomial.X * Polynomial.derivative (polyCauchyEulerPoly k) := rfl
    rw [hlhs, ih, Derivation.leibniz, hexp_deriv, hpoly_deriv, hstep]
    push_cast
    simp only [smul_eq_mul]
    ring

/-- **Master Nonpositive-Index Poly-Cauchy D-Finiteness Theorem (Paper #12 Corollary 7.3):**
For every `ℓ : ℕ`, there exists an explicit monic polynomial `P_ℓ = polyCauchyEulerPoly ℓ` of
degree `ℓ` such that:
1. `(1 + v ∂_v)^ℓ e^v = P_ℓ(v) * e^v` for all `v : ℝ`;
2. `PowerSeries.mk (fun m => (m + 1)^ℓ / m!) = P_ℓ * PowerSeries.exp ℝ`;
3. For every `v : ℝ`, the series `∑' m : ℕ, (m + 1)^ℓ * v^m / m!` converges absolutely to
   `P_ℓ(v) * Real.exp v`;
4. At `v = log(1 + s)` and `v = -log(1 + s)` (`s > -1`), the poly-Cauchy EGFs collapse to
   `(1 + s) * P_ℓ(log(1 + s))` and `(1 + s)⁻¹ * P_ℓ(-log(1 + s))` (rational functions times
   polynomials in `log(1 + s)`). -/
theorem polyCauchy_nonpos_dfinite_poly (ℓ : ℕ) :
    ((polyCauchyEulerPoly ℓ).Monic ∧ (polyCauchyEulerPoly ℓ).natDegree = ℓ) ∧
    (∀ v : ℝ, (eulerDiffOp^[ℓ] Real.exp) v = (polyCauchyEulerPoly ℓ).eval v * Real.exp v) ∧
    (PowerSeries.mk (fun m : ℕ => ((m + 1 : ℝ) ^ ℓ) / (m.factorial : ℝ)) =
      ((polyCauchyEulerPoly ℓ : Polynomial ℝ) : PowerSeries ℝ) * PowerSeries.exp ℝ) ∧
    (∀ v : ℝ,
      Summable (fun m : ℕ => ((m + 1 : ℝ) ^ ℓ) * v ^ m / (m.factorial : ℝ)) ∧
      (∑' m : ℕ, ((m + 1 : ℝ) ^ ℓ) * v ^ m / (m.factorial : ℝ)) =
        (polyCauchyEulerPoly ℓ).eval v * Real.exp v) ∧
    (∀ s : ℝ, -1 < s →
      (∑' m : ℕ, ((m + 1 : ℝ) ^ ℓ) * (Real.log (1 + s)) ^ m / (m.factorial : ℝ)) =
        (1 + s) * (polyCauchyEulerPoly ℓ).eval (Real.log (1 + s)) ∧
      (∑' m : ℕ, ((m + 1 : ℝ) ^ ℓ) * (-Real.log (1 + s)) ^ m / (m.factorial : ℝ)) =
        (1 + s)⁻¹ * (polyCauchyEulerPoly ℓ).eval (-Real.log (1 + s))) := by
  have hsum_poly : ∀ (p : Polynomial ℝ) (v : ℝ),
      Summable (fun m : ℕ =>
        (PowerSeries.coeff m ((p : PowerSeries ℝ) * PowerSeries.exp ℝ)) * v ^ m) ∧
      (∑' m : ℕ,
        (PowerSeries.coeff m ((p : PowerSeries ℝ) * PowerSeries.exp ℝ)) * v ^ m) =
        p.eval v * Real.exp v := by
    intro p v
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      have hfun : (fun m : ℕ =>
          PowerSeries.coeff m ((((p + q : Polynomial ℝ) : PowerSeries ℝ) * PowerSeries.exp ℝ)) * v ^ m) =
          fun m : ℕ =>
            PowerSeries.coeff m (((p : PowerSeries ℝ) * PowerSeries.exp ℝ)) * v ^ m +
            PowerSeries.coeff m (((q : PowerSeries ℝ) * PowerSeries.exp ℝ)) * v ^ m := by
        funext m
        rw [Polynomial.coe_add, add_mul, map_add, add_mul]
      rw [hfun]
      refine ⟨hp.1.add hq.1, ?_⟩
      rw [hp.1.tsum_add hq.1, hp.2, hq.2, Polynomial.eval_add, add_mul]
    | monomial d a =>
      have hbase_sum : Summable (fun n : ℕ => a * v ^ d * (v ^ n / (n.factorial : ℝ))) := by
        have h := (NormedSpace.expSeries_div_summable (𝔸 := ℝ) v).mul_left (a * v ^ d)
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
      have hshift_sum :
          Summable (fun m : ℕ => if d ≤ m then a * v ^ d * (v ^ (m - d) / ((m - d).factorial : ℝ)) else 0) := by
        rw [← summable_nat_add_iff d]
        simpa [Nat.le_add_left, Nat.add_sub_cancel_left] using hbase_sum
      have htsum_eq :
          (∑' m : ℕ, if d ≤ m then a * v ^ d * (v ^ (m - d) / ((m - d).factorial : ℝ)) else 0) =
            a * v ^ d * Real.exp v := by
        rw [← hshift_sum.sum_add_tsum_nat_add d]
        have hhead : (∑ m ∈ Finset.range d,
            if d ≤ m then a * v ^ d * (v ^ (m - d) / ((m - d).factorial : ℝ)) else 0) = 0 := by
          refine Finset.sum_eq_zero fun m hm => ?_
          have hnot : ¬ d ≤ m := not_le_of_gt (Finset.mem_range.mp hm)
          simp only [hnot, ↓reduceIte]
        rw [hhead, zero_add]
        have htail : (fun n : ℕ =>
            if d ≤ n + d then a * v ^ d * (v ^ (n + d - d) / ((n + d - d).factorial : ℝ)) else 0) =
            fun n : ℕ => a * v ^ d * (v ^ n / (n.factorial : ℝ)) := by
          funext n
          simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel]
        rw [htail, tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      have hcongr : (fun m : ℕ =>
          PowerSeries.coeff m
            ((((Polynomial.monomial d a : Polynomial ℝ) : PowerSeries ℝ) * PowerSeries.exp ℝ)) *
            v ^ m) =
          fun m : ℕ => if d ≤ m then a * v ^ d * (v ^ (m - d) / ((m - d).factorial : ℝ)) else 0 := by
        funext m
        by_cases hdm : d ≤ m
        · simp only [hdm, ↓reduceIte]
          rw [PowerSeries.coeff_mul, Finset.sum_eq_single (d, m - d)]
          · rw [Polynomial.coeff_coe, Polynomial.coeff_monomial, Finsupp.single_eq_same,
              PowerSeries.coeff_exp]
            have hv_pow : v ^ m = v ^ d * v ^ (m - d) := by
              rw [← pow_add, Nat.add_sub_of_le hdm]
            simp only [map_div₀, map_one, map_natCast]
            rw [hv_pow]; ring
          · intro x hx hne
            rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
            have hxd : x.1 ≠ d := by
              intro h
              exact hne (Prod.ext h (by omega))
            rw [Polynomial.coeff_coe, Polynomial.coeff_monomial, Finsupp.single_eq_of_ne hxd,
              zero_mul]
          · intro hnot
            exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_sub_of_le hdm)) hnot
        · simp only [hdm, ↓reduceIte]
          rw [PowerSeries.coeff_mul]
          have hz : (∑ x ∈ Finset.HasAntidiagonal.antidiagonal m,
              PowerSeries.coeff x.1 ((Polynomial.monomial d a : Polynomial ℝ) : PowerSeries ℝ) *
              PowerSeries.coeff x.2 (PowerSeries.exp ℝ)) = 0 := by
            refine Finset.sum_eq_zero fun x hx => ?_
            rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
            have hne : x.1 ≠ d := by omega
            rw [Polynomial.coeff_coe, Polynomial.coeff_monomial, Finsupp.single_eq_of_ne hne,
              zero_mul]
          rw [hz, zero_mul]
      rw [hcongr]
      refine ⟨hshift_sum, ?_⟩
      rw [htsum_eq, Polynomial.eval_monomial]
  have htsum : ∀ v : ℝ,
      Summable (fun m : ℕ => ((m + 1 : ℝ) ^ ℓ) * v ^ m / (m.factorial : ℝ)) ∧
      (∑' m : ℕ, ((m + 1 : ℝ) ^ ℓ) * v ^ m / (m.factorial : ℝ)) =
        (polyCauchyEulerPoly ℓ).eval v * Real.exp v := by
    intro v
    have hspec := hsum_poly (polyCauchyEulerPoly ℓ) v
    have hps := polyCauchy_nonpos_powerSeries ℓ
    have hfun_eq : (fun m : ℕ =>
        PowerSeries.coeff m (((polyCauchyEulerPoly ℓ : Polynomial ℝ) : PowerSeries ℝ) *
          PowerSeries.exp ℝ) * v ^ m) =
        fun m : ℕ => ((m + 1 : ℝ) ^ ℓ) * v ^ m / (m.factorial : ℝ) := by
      funext m
      rw [← hps, PowerSeries.coeff_mk]
      ring
    rwa [hfun_eq] at hspec
  refine ⟨polyCauchyEulerPoly_monic_and_natDegree ℓ,
    fun v => congrFun (iterated_eulerDiffOp_exp ℓ) v,
    polyCauchy_nonpos_powerSeries ℓ,
    htsum, ?_⟩
  intro s hs
  have h1s : 0 < 1 + s := by linarith
  have hpos := (htsum (Real.log (1 + s))).2
  have hneg := (htsum (-Real.log (1 + s))).2
  rw [Real.exp_log h1s] at hpos
  rw [Real.exp_neg, Real.exp_log h1s] at hneg
  exact ⟨by linarith, by linarith⟩

end PolyCauchyCore

end

end CubicTheta.AllD
