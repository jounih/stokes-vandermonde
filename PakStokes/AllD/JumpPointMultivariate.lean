module

public import PakStokes.AllD.BesicovitchCore
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import all PakStokes.AllD.BesicovitchCore

/-! # Wave 10: The Jump-Point Derivation Engine for Multivariate Non-Quadratic Forms

100% unconditional Lean 4 formalization of **Probe 268 Theorem 2.1** (the Jump-Point
Derivation Engine and Constructive Positive-Hessian Multiplicity for arbitrary
multivariate non-quadratic forms of degree `d ≥ 3`, with zero rationality assumption
and zero off-ray `s ≥ 2` collision hypothesis):

1. **Abstract Jump-Point Existence (`JumpSet`, `span_jumpSet_eq_span`, `jumpPoints_exist`):**
   For any well-ordered subset `A ⊆ ℝ` (`A.IsWF`, automatically satisfied by every locally
   finite discrete positive spectrum `∀ B, (A ∩ Set.Iic B).Finite`), its dimension-jump
   subset `JumpSet A := {a ∈ A | a ∉ Submodule.span ℚ (A ∩ Set.Iio a)}` spans the exact
   same `ℚ`-subspace as `A`, is `ℚ`-linearly independent, admits zero `s ≥ 2` additive
   collisions when `A ⊆ (0, ∞)`, and when `¬ Module.Finite ℚ (Submodule.span ℚ A)` yields
   strictly increasing jump tuples `a₀ < a₁ < ⋯ < a_{J-1}` of arbitrary length `J`
   together with separating `ℚ`-linear functionals `φᵢ : ℝ →ₗ[ℚ] ℚ` (`φᵢ(aᵢ) = 1`,
   `φᵢ(A ∩ (-∞, aᵢ)) = {0}`).
2. **Exact Monoid & Hahn-Series Derivations (`monoidDeriv`, `hahnDeriv`,
   `jumpPoint_zero_offray_collisions`, `jumpPoint_algebraicIndependent`,
   `jumpPoint_minimal_relation_vandermonde`):**
   For any additive map `φ : ℝ →+ R`, `monoidDeriv φ` on `AddMonoidAlgebra R ℝ` and
   `hahnDeriv φ` on `HahnSeries ℝ R` satisfy the exact Leibniz product rule and
   multivariate polynomial chain rule. Applying `hahnDeriv` for `J` jump points to a
   minimal-degree polynomial relation `P(Y₀, …, Y_{J-1}) = 0` isolates the `J × J`
   jump-point coefficient matrix at `μ₀ + aᵢ` in 10 lines — eliminating all off-ray
   `s ≥ 2` additive collisions without Galois theory.
3. **Full Formal Transseries with Arbitrary Asymptotic Prefactors (`AsympCoeff`,
   `TransSeries`, `transDerivX`, `jumpPoint_transseries_algebraicIndependent`,
   `jumpPoint_transseries_no_poly_ade`):**
   Extends the Vandermonde isolation to `HahnSeries ℝ (HahnSeries ℝ ℂ)` with arbitrary
   leading asymptotic prefactors `c_a X^{β_a}`, proving algebraic independence over the
   entire asymptotic coefficient ring `HahnSeries ℝ ℂ` (and hence over `ℂ[X]`).
4. **Universal Wulff-Ray Infinite `ℚ`-Rank, Constructive Positive-Hessian Multiplicity,
   Master Theorems & Concrete Non-Vacuity Witness (`wulffRay_infinite_qrank`,
   `constructive_shell_amplitude_ne_zero`, `multivariate_evenForm_algebraic_dtrans`,
   `multivariate_jumpPoint_non_ade`, `diagForm_transseries_non_ade`,
   `diagQuartic2D_non_ade`):**
   Connects directly to `BesicovitchCore` (`d ≥ 3`, arbitrary real `c₀ > 0`) and exhibits
   an explicit `m`-dimensional diagonal quartic/degree-`d` witness (complete with real
   `s = 2` off-ray collisions `1 + 1 = 2` and `s = 1` shell multiplicity) proved
   unconditionally non-ADE in the Lean kernel. -/
public section
namespace CubicTheta.AllD
open Set Filter MvPolynomial Matrix
open scoped BigOperators Pointwise
noncomputable section

/-! ### 1. Abstract Jump-Point Existence in Infinite-`ℚ`-Rank Well-Ordered Sets -/

/-- The dimension-jump points of a real action set `A ⊆ ℝ`: those `a ∈ A` that do not
lie in the `ℚ`-linear span of the strictly smaller elements `A ∩ (-∞, a)`. -/
def JumpSet (A : Set ℝ) : Set ℝ :=
  {a ∈ A | a ∉ Submodule.span ℚ (A ∩ Set.Iio a)}

/-- Every locally finite subset `A ⊆ ℝ` (`∀ B, (A ∩ (-∞, B]).Finite`) is well-founded
(and hence partially well-ordered). -/
theorem isWF_of_locallyFinite {A : Set ℝ} (hloc : ∀ B : ℝ, (A ∩ Set.Iic B).Finite) :
    A.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  intro f hf_anti hf_mem
  have hsub : Set.range f ⊆ A ∩ Set.Iic (f 0) := by
    rintro _ ⟨n, rfl⟩
    exact ⟨hf_mem n, hf_anti.antitone (Nat.zero_le n)⟩
  have hfin : (Set.range f).Finite := (hloc (f 0)).subset hsub
  exact Set.infinite_range_of_injective hf_anti.injective hfin

theorem isPWO_of_locallyFinite {A : Set ℝ} (hloc : ∀ B : ℝ, (A ∩ Set.Iic B).Finite) :
    A.IsPWO :=
  (isWF_of_locallyFinite hloc).isPWO

/-- For any positive action set `A ⊆ (0, ∞)`, `A ∩ (-∞, a) = A ∩ (0, a)`. -/
theorem inter_Iio_eq_inter_Ioo {A : Set ℝ} (hpos : ∀ a ∈ A, 0 < a) (a : ℝ) :
    A ∩ Set.Iio a = A ∩ Set.Ioo 0 a := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
  exact ⟨fun ⟨hxA, hxa⟩ ↦ ⟨hxA, hpos x hxA, hxa⟩, fun ⟨hxA, _, hxa⟩ ↦ ⟨hxA, hxa⟩⟩

/-- **Fundamental Spanning Theorem for Jump Points**: for ANY well-ordered set `A ⊆ ℝ`,
the `ℚ`-span of `JumpSet A` equals the full `ℚ`-span of `A`. -/
theorem span_jumpSet_eq_span {A : Set ℝ} (hA : A.IsWF) :
    Submodule.span ℚ (JumpSet A) = Submodule.span ℚ A := by
  apply le_antisymm
  · exact Submodule.span_mono (fun _ hx ↦ hx.1)
  · rw [Submodule.span_le]
    intro a ha
    by_contra hnot
    let S : Set ℝ := {x ∈ A | x ∉ Submodule.span ℚ (JumpSet A)}
    have hSne : S.Nonempty := ⟨a, ha, hnot⟩
    have hSwf : S.IsWF := hA.mono (fun _ hx ↦ hx.1)
    let a₀ : ℝ := hSwf.min hSne
    have ha₀_mem : a₀ ∈ S := hSwf.min_mem hSne
    have hlt_in : A ∩ Set.Iio a₀ ⊆ (Submodule.span ℚ (JumpSet A) : Set ℝ) := by
      intro b ⟨hbA, hba⟩
      by_contra hbnot
      exact hSwf.not_lt_min hSne (show b ∈ S from ⟨hbA, hbnot⟩) hba
    have hspan_le : Submodule.span ℚ (A ∩ Set.Iio a₀) ≤ Submodule.span ℚ (JumpSet A) :=
      Submodule.span_le.mpr hlt_in
    have ha₀_jump : a₀ ∈ JumpSet A :=
      ⟨ha₀_mem.1, fun hmem ↦ ha₀_mem.2 (hspan_le hmem)⟩
    exact ha₀_mem.2 (Submodule.subset_span ha₀_jump)

/-- Every well-ordered set `A ⊆ ℝ` of infinite `ℚ`-rank has infinitely many jump points. -/
theorem jumpSet_infinite {A : Set ℝ} (hA : A.IsWF)
    (hinf : ¬ Module.Finite ℚ (Submodule.span ℚ A)) :
    (JumpSet A).Infinite := by
  intro hfin
  have hmod : Module.Finite ℚ (Submodule.span ℚ (JumpSet A)) :=
    Module.Finite.span_of_finite ℚ hfin
  rw [span_jumpSet_eq_span hA] at hmod
  exact hinf hmod

/-- The entire jump-point set `JumpSet A` is unconditionally `ℚ`-linearly independent. -/
theorem jumpSet_linearIndependent (A : Set ℝ) :
    LinearIndependent ℚ (fun x : JumpSet A ↦ (x : ℝ)) := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci
  let s' : Finset (JumpSet A) := s.filter fun x ↦ c x ≠ 0
  have hs'_ne : s'.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  let vals : Finset ℝ := s'.image Subtype.val
  have hvals_ne : vals.Nonempty := hs'_ne.image _
  let m : ℝ := vals.max' hvals_ne
  have hm_mem : m ∈ vals := Finset.max'_mem vals hvals_ne
  obtain ⟨x₀, hx₀_s', hx₀_val⟩ := Finset.mem_image.mp hm_mem
  have hx₀_c : c x₀ ≠ 0 := (Finset.mem_filter.mp hx₀_s').2
  have hsum_s' : ∑ x ∈ s', c x • (x : ℝ) = 0 := by
    rw [← hsum]
    apply Finset.sum_subset (Finset.filter_subset _ s)
    intro x hx hxn
    have : c x = 0 := by
      by_contra hne
      exact hxn (Finset.mem_filter.mpr ⟨hx, hne⟩)
    simp [this]
  have hsplit : c x₀ • (x₀ : ℝ) + ∑ x ∈ s'.erase x₀, c x • (x : ℝ) = 0 := by
    rwa [Finset.add_sum_erase s' (fun x ↦ c x • (x : ℝ)) hx₀_s']
  have hexpr : (x₀ : ℝ) = ∑ x ∈ s'.erase x₀, (-(c x₀)⁻¹ * c x) • (x : ℝ) := by
    have hneg : c x₀ • (x₀ : ℝ) = -(∑ x ∈ s'.erase x₀, c x • (x : ℝ)) :=
      eq_neg_of_add_eq_zero_left hsplit
    have hmul := congrArg (fun r : ℝ ↦ (c x₀)⁻¹ • r) hneg
    simp only [smul_smul, inv_mul_cancel₀ hx₀_c, one_smul, smul_neg, Finset.smul_sum,
      ← Finset.sum_neg_distrib] at hmul
    rw [hmul]
    apply Finset.sum_congr rfl
    intro x _
    rw [neg_mul, neg_smul]
  have hin_span : (x₀ : ℝ) ∈ Submodule.span ℚ (A ∩ Set.Iio (x₀ : ℝ)) := by
    have hmem : ∑ x ∈ s'.erase x₀, (-(c x₀)⁻¹ * c x) • (x : ℝ) ∈
        Submodule.span ℚ (A ∩ Set.Iio (x₀ : ℝ)) := by
      refine Submodule.sum_mem _ fun x hx ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
      have hx_s' : x ∈ s' := Finset.mem_of_mem_erase hx
      have hx_ne : x ≠ x₀ := Finset.ne_of_mem_erase hx
      have hx_le : (x : ℝ) ≤ (x₀ : ℝ) := by
        rw [hx₀_val]
        exact Finset.le_max' vals (x : ℝ) (Finset.mem_image_of_mem _ hx_s')
      have hx_lt : (x : ℝ) < (x₀ : ℝ) :=
        lt_of_le_of_ne hx_le (fun heq ↦ hx_ne (Subtype.ext heq))
      exact ⟨x.property.1, hx_lt⟩
    rwa [← hexpr] at hmem
  exact x₀.property.2 hin_span

/-- **Part 1 — Abstract Jump-Point Existence Theorem**: For any well-ordered positive action
set `A ⊆ (0, ∞)` of infinite `ℚ`-rank and every `J : ℕ`, there exist strictly increasing
dimension-jump points `0 < a₀ < a₁ < ⋯ < a_{J-1}` in `A` that are `ℚ`-linearly independent
and satisfy `aᵢ ∉ span_ℚ(A ∩ (0, aᵢ))` for all `i : Fin J`. -/
theorem jumpPoints_exist {A : Set ℝ} (hpos : ∀ a ∈ A, 0 < a) (hA : A.IsWF)
    (hinf : ¬ Module.Finite ℚ (Submodule.span ℚ A)) (J : ℕ) :
    ∃ a : Fin J → ℝ,
      StrictMono a ∧
      (∀ i : Fin J, 0 < a i) ∧
      (∀ i : Fin J, a i ∈ A) ∧
      (∀ i : Fin J, a i ∉ Submodule.span ℚ (A ∩ Set.Ioo 0 (a i))) ∧
      LinearIndependent ℚ a := by
  classical
  obtain ⟨S, hSsub, hScard⟩ := (jumpSet_infinite hA hinf).exists_subset_card_eq J
  let emb : Fin J ↪o ℝ := S.orderEmbOfFin hScard
  refine ⟨emb, emb.strictMono, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hpos _ (hSsub (Finset.orderEmbOfFin_mem S hScard i)).1
  · intro i
    exact (hSsub (Finset.orderEmbOfFin_mem S hScard i)).1
  · intro i
    rw [← inter_Iio_eq_inter_Ioo hpos (emb i)]
    exact (hSsub (Finset.orderEmbOfFin_mem S hScard i)).2
  · let f : Fin J → JumpSet A := fun i ↦ ⟨emb i, hSsub (Finset.orderEmbOfFin_mem S hScard i)⟩
    have hf_inj : Function.Injective f := fun i j hij ↦
      emb.injective (by simpa [f] using congrArg Subtype.val hij)
    exact (jumpSet_linearIndependent A).comp f hf_inj

/-- Version of `jumpPoints_exist` for arbitrary well-ordered sets (not requiring positivity)
producing `J` strictly increasing elements of `JumpSet A`. -/
theorem jumpPoints_exist_of_isWF {A : Set ℝ} (hA : A.IsWF)
    (hinf : ¬ Module.Finite ℚ (Submodule.span ℚ A)) (J : ℕ) :
    ∃ a : Fin J → ℝ, StrictMono a ∧ (∀ i : Fin J, a i ∈ JumpSet A) ∧ LinearIndependent ℚ a := by
  classical
  obtain ⟨S, hSsub, hScard⟩ := (jumpSet_infinite hA hinf).exists_subset_card_eq J
  let emb : Fin J ↪o ℝ := S.orderEmbOfFin hScard
  refine ⟨emb, emb.strictMono, fun i ↦ hSsub (Finset.orderEmbOfFin_mem S hScard i), ?_⟩
  let f : Fin J → JumpSet A := fun i ↦ ⟨emb i, hSsub (Finset.orderEmbOfFin_mem S hScard i)⟩
  exact (jumpSet_linearIndependent A).comp f
    (fun _ _ h ↦ emb.injective (by simpa [f] using congrArg Subtype.val h))

/-- For any locally finite set `A ⊆ ℝ` of infinite `ℚ`-rank, every threshold `B : ℝ`,
and every `J : ℕ`, there exist `J` strictly increasing jump points strictly above `B`. -/
theorem jumpPoints_exist_above {A : Set ℝ} (hloc : ∀ B : ℝ, (A ∩ Set.Iic B).Finite)
    (hinf : ¬ Module.Finite ℚ (Submodule.span ℚ A)) (B : ℝ) (J : ℕ) :
    ∃ a : Fin J → ℝ,
      StrictMono a ∧
      (∀ i : Fin J, B < a i) ∧
      (∀ i : Fin J, a i ∈ JumpSet A) ∧
      LinearIndependent ℚ a := by
  classical
  have hJinf : (JumpSet A).Infinite := jumpSet_infinite (isWF_of_locallyFinite hloc) hinf
  have hbelow_fin : (JumpSet A ∩ Set.Iic B).Finite :=
    (hloc B).subset (fun x ⟨hxJ, hxB⟩ ↦ ⟨hxJ.1, hxB⟩)
  have habove_inf : (JumpSet A ∩ Set.Ioi B).Infinite := by
    have hdiff : JumpSet A \ (JumpSet A ∩ Set.Iic B) ⊆ JumpSet A ∩ Set.Ioi B := by
      intro x ⟨hxJ, hxn⟩
      refine ⟨hxJ, ?_⟩
      by_contra hle
      exact hxn ⟨hxJ, not_lt.mp hle⟩
    exact (hJinf.sdiff hbelow_fin).mono hdiff
  obtain ⟨S, hSsub, hScard⟩ := habove_inf.exists_subset_card_eq J
  let emb : Fin J ↪o ℝ := S.orderEmbOfFin hScard
  refine ⟨emb, emb.strictMono,
    fun i ↦ (hSsub (Finset.orderEmbOfFin_mem S hScard i)).2,
    fun i ↦ (hSsub (Finset.orderEmbOfFin_mem S hScard i)).1, ?_⟩
  let f : Fin J → JumpSet A := fun i ↦ ⟨emb i, (hSsub (Finset.orderEmbOfFin_mem S hScard i)).1⟩
  exact (jumpSet_linearIndependent A).comp f
    (fun _ _ h ↦ emb.injective (by simpa [f] using congrArg Subtype.val h))

/-- **Separating `ℚ`-Linear Functional at Every Jump Point**: for each `a ∈ JumpSet A`,
there exists `φ : ℝ →ₗ[ℚ] ℚ` with `φ a = 1` and `φ = 0` on `span_ℚ(A ∩ (-∞, a))`. -/
theorem exists_jump_functional {A : Set ℝ} {a : ℝ} (ha : a ∈ JumpSet A) :
    ∃ φ : ℝ →ₗ[ℚ] ℚ, φ a = 1 ∧ ∀ x ∈ Submodule.span ℚ (A ∩ Set.Iio a), φ x = 0 := by
  let U : Submodule ℚ ℝ := Submodule.span ℚ (A ∩ Set.Iio a)
  obtain ⟨φ, hφU, hφa⟩ := LinearMap.exists_extend_of_notMem (0 : U →ₗ[ℚ] ℚ) ha.2 (1 : ℚ)
  refine ⟨φ, hφa, fun x hx ↦ ?_⟩
  have := LinearMap.congr_fun hφU ⟨x, hx⟩
  simpa using this

/-- **Zero `s ≥ 2` Additive Collisions at Every Jump Point**: in any positive action
set `A ⊆ (0, ∞)`, a jump point `a ∈ JumpSet A` can NEVER equal a sum of `s ≥ 2`
elements of `A`! -/
theorem jumpPoint_no_multi_pos_sum {A : Set ℝ} (hpos : ∀ x ∈ A, 0 < x)
    {a : ℝ} (ha : a ∈ JumpSet A) {s : ℕ} (hs : 2 ≤ s) (b : Fin s → ℝ)
    (hb : ∀ r : Fin s, b r ∈ A) :
    ∑ r : Fin s, b r ≠ a := by
  intro hsum
  have hlt : ∀ r : Fin s, b r < a := by
    intro r
    have hother_pos : 0 < ∑ t ∈ Finset.univ.erase r, b t := by
      have hne : (Finset.univ.erase r).Nonempty := by
        obtain ⟨r', hr'⟩ : ∃ r' : Fin s, r' ≠ r := by
          by_cases hr0 : r.val = 0
          · exact ⟨⟨1, by omega⟩, fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega⟩
          · exact ⟨⟨0, by omega⟩, fun h ↦ by have := congrArg Fin.val h; dsimp at this; omega⟩
        exact ⟨r', Finset.mem_erase.mpr ⟨hr', Finset.mem_univ _⟩⟩
      exact Finset.sum_pos (fun t _ ↦ hpos (b t) (hb t)) hne
    have hdecomp : b r + ∑ t ∈ Finset.univ.erase r, b t = a := by
      rw [Finset.add_sum_erase Finset.univ b (Finset.mem_univ r), hsum]
    linarith
  have hin : a ∈ Submodule.span ℚ (A ∩ Set.Iio a) := by
    have hmem : ∑ r : Fin s, b r ∈ Submodule.span ℚ (A ∩ Set.Iio a) :=
      Submodule.sum_mem _ fun r _ ↦ Submodule.subset_span ⟨hb r, hlt r⟩
    rwa [hsum] at hmem
  exact ha.2 hin

/-! ### 2. Exact Monoid Derivations (`AddMonoidAlgebra` & `HahnSeries`) and the 10-Line Elimination -/

section MonoidDeriv

variable {K R : Type*} [CommRing R]

/-- The exact action-monoid derivation `∂_φ(∑ c_a e^a) = ∑ φ(a) c_a e^a` on
`AddMonoidAlgebra R ℝ` induced by any additive map `φ : ℝ →+ R`. -/
def monoidDeriv (φ : ℝ →+ R) (f : AddMonoidAlgebra R ℝ) : AddMonoidAlgebra R ℝ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.onFinset f.coeff.support (fun a ↦ φ a * f.coeff a)
      (fun _ ha ↦ Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul ha)))

@[simp]
theorem monoidDeriv_coeff (φ : ℝ →+ R) (f : AddMonoidAlgebra R ℝ) (a : ℝ) :
    (monoidDeriv φ f).coeff a = φ a * f.coeff a := by
  simp [monoidDeriv]

@[simp]
theorem monoidDeriv_zero (φ : ℝ →+ R) : monoidDeriv φ 0 = 0 := by
  ext a; simp

@[simp]
theorem monoidDeriv_single (φ : ℝ →+ R) (a : ℝ) (r : R) :
    monoidDeriv φ (AddMonoidAlgebra.single a r) = AddMonoidAlgebra.single a (φ a * r) := by
  classical
  ext b
  simp only [monoidDeriv_coeff, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem monoidDeriv_add (φ : ℝ →+ R) (f g : AddMonoidAlgebra R ℝ) :
    monoidDeriv φ (f + g) = monoidDeriv φ f + monoidDeriv φ g := by
  ext a
  simp only [monoidDeriv_coeff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  ring

theorem monoidDeriv_smul [CommRing K] [Algebra K R] (φ : ℝ →+ R) (c : K)
    (f : AddMonoidAlgebra R ℝ) :
    monoidDeriv φ (c • f) = c • monoidDeriv φ f := by
  ext a
  rw [monoidDeriv_coeff, AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.coeff_smul,
      Finsupp.smul_apply, Finsupp.smul_apply, monoidDeriv_coeff,
      Algebra.smul_def, Algebra.smul_def]
  ring

@[simp]
theorem monoidDeriv_algebraMap [CommRing K] [Algebra K R] (φ : ℝ →+ R) (c : K) :
    monoidDeriv φ (algebraMap K (AddMonoidAlgebra R ℝ) c) = 0 := by
  classical
  ext a
  rw [Algebra.algebraMap_eq_smul_one, monoidDeriv_smul, AddMonoidAlgebra.one_def,
      monoidDeriv_single, map_zero, zero_mul, AddMonoidAlgebra.single_zero, smul_zero]

/-- **Exact Leibniz Product Rule** for `monoidDeriv` on `AddMonoidAlgebra R ℝ`. -/
theorem monoidDeriv_mul (φ : ℝ →+ R) (f g : AddMonoidAlgebra R ℝ) :
    monoidDeriv φ (f * g) = monoidDeriv φ f * g + f * monoidDeriv φ g := by
  classical
  ext z
  simp only [monoidDeriv_coeff, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  have hmul_eq (u v : AddMonoidAlgebra R ℝ) :
      (u * v).coeff z = ∑ a ∈ u.coeff.support, ∑ b ∈ v.coeff.support,
        if a + b = z then u.coeff a * v.coeff b else 0 :=
    AddMonoidAlgebra.coeff_mul u v z
  have hsub_left : (monoidDeriv φ f).coeff.support ⊆ f.coeff.support := by
    intro a ha
    rw [Finsupp.mem_support_iff, monoidDeriv_coeff] at ha
    exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul ha)
  have hsub_right : (monoidDeriv φ g).coeff.support ⊆ g.coeff.support := by
    intro b hb
    rw [Finsupp.mem_support_iff, monoidDeriv_coeff] at hb
    exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hb)
  have h1 : (monoidDeriv φ f * g).coeff z =
      ∑ a ∈ f.coeff.support, ∑ b ∈ g.coeff.support,
        if a + b = z then (φ a * f.coeff a) * g.coeff b else 0 := by
    rw [hmul_eq]
    refine (Finset.sum_subset hsub_left fun a _ ha ↦ ?_).trans (Finset.sum_congr rfl fun a _ ↦
      Finset.sum_congr rfl fun b _ ↦ by rw [monoidDeriv_coeff])
    apply Finset.sum_eq_zero
    intro b _
    have h0 : (monoidDeriv φ f).coeff a = 0 := Finsupp.notMem_support_iff.mp ha
    simp [h0]
  have h2 : (f * monoidDeriv φ g).coeff z =
      ∑ a ∈ f.coeff.support, ∑ b ∈ g.coeff.support,
        if a + b = z then f.coeff a * (φ b * g.coeff b) else 0 := by
    rw [hmul_eq]
    refine Finset.sum_congr rfl fun a _ ↦
      (Finset.sum_subset hsub_right fun b _ hb ↦ ?_).trans (Finset.sum_congr rfl fun b _ ↦ by
        rw [monoidDeriv_coeff])
    have h0 : (monoidDeriv φ g).coeff b = 0 := Finsupp.notMem_support_iff.mp hb
    simp [h0]
  rw [hmul_eq, h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs with hab
  · subst hab
    rw [map_add]
    ring
  · simp

/-- **Exact Multivariate Polynomial Chain Rule** for `monoidDeriv` on `AddMonoidAlgebra R ℝ`. -/
theorem monoidDeriv_aeval [CommRing K] [Algebra K R] {ι : Type*} [Fintype ι]
    (φ : ℝ →+ R) (Y : ι → AddMonoidAlgebra R ℝ) (P : MvPolynomial ι K) :
    monoidDeriv φ (MvPolynomial.aeval Y P) =
      ∑ j : ι, MvPolynomial.aeval Y (MvPolynomial.pderiv j P) * monoidDeriv φ (Y j) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp
  | add p q hp hq =>
    simp only [map_add, monoidDeriv_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, monoidDeriv_mul, hp, MvPolynomial.aeval_X,
      Derivation.leibniz, smul_eq_mul, map_add, MvPolynomial.pderiv_X, Pi.single_apply,
      apply_ite (MvPolynomial.aeval Y), map_one, map_zero]
    simp only [Finset.sum_mul, add_mul, Finset.sum_add_distrib]
    have hdiag : (∑ j : ι, (MvPolynomial.aeval Y p * (if k = j then (1 : AddMonoidAlgebra R ℝ) else 0)) *
        monoidDeriv φ (Y j)) = MvPolynomial.aeval Y p * monoidDeriv φ (Y k) := by
      have hterm : ∀ j : ι, (MvPolynomial.aeval Y p * (if k = j then (1 : AddMonoidAlgebra R ℝ) else 0)) *
          monoidDeriv φ (Y j) = if k = j then MvPolynomial.aeval Y p * monoidDeriv φ (Y k) else 0 := by
        intro j; split_ifs with h <;> simp [h]
      simp_rw [hterm]
      simp
    rw [hdiag, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- **Zero-Collision Action Isolation on `AddMonoidAlgebra`**: if `φ : ℝ →+ R` vanishes on
`A ∩ (-∞, a)` and `b₁, …, bₛ ∈ A` are strictly smaller than `a` (as happens for EVERY
`s ≥ 2` positive off-ray sum `b₁ + ⋯ + bₛ = a`), then `monoidDeriv φ` completely
annihilates their product `∏ r, single (b r) (c r)`. -/
theorem jumpPoint_zero_offray_collisions {A : Set ℝ} {a : ℝ} (φ : ℝ →+ R)
    (hvan : ∀ x ∈ A, x < a → φ x = 0) {s : ℕ} (b : Fin s → ℝ) (c : Fin s → R)
    (hbA : ∀ r : Fin s, b r ∈ A) (hblt : ∀ r : Fin s, b r < a) :
    monoidDeriv φ (∏ r : Fin s, AddMonoidAlgebra.single (b r) (c r)) = 0 := by
  have hprod : (∏ r : Fin s, AddMonoidAlgebra.single (b r) (c r)) =
      AddMonoidAlgebra.single (∑ r : Fin s, b r) (∏ r : Fin s, c r) := by
    clear hvan hbA hblt
    induction s with
    | zero => simp [AddMonoidAlgebra.one_def]
    | succ n ih =>
      rw [Fin.prod_univ_castSucc, Fin.sum_univ_castSucc, Fin.prod_univ_castSucc,
          ih (fun r ↦ b r.castSucc) (fun r ↦ c r.castSucc),
          AddMonoidAlgebra.single_mul_single]
  rw [hprod, monoidDeriv_single, map_sum]
  have hzero : ∑ r : Fin s, φ (b r) = 0 :=
    Finset.sum_eq_zero fun r _ ↦ hvan (b r) (hbA r) (hblt r)
  rw [hzero, zero_mul, AddMonoidAlgebra.single_zero]

end MonoidDeriv

section HahnDeriv

variable {K R : Type*} [CommRing R]

/-- The exact action-monoid derivation `∂_φ(∑ c_a e^{-a X}) = ∑ φ(a) c_a e^{-a X}` on
the full formal Hahn series ring `HahnSeries ℝ R` (allowing infinite well-ordered support!). -/
def hahnDeriv (φ : ℝ →+ R) (x : HahnSeries ℝ R) : HahnSeries ℝ R where
  coeff a := φ a * x.coeff a
  isPWO_support' := x.isPWO_support.mono fun _ ha ↦ right_ne_zero_of_mul ha

@[simp]
theorem hahnDeriv_coeff (φ : ℝ →+ R) (x : HahnSeries ℝ R) (a : ℝ) :
    (hahnDeriv φ x).coeff a = φ a * x.coeff a := by
  rfl

theorem hahnDeriv_support_subset (φ : ℝ →+ R) (x : HahnSeries ℝ R) :
    (hahnDeriv φ x).support ⊆ x.support :=
  fun _ ha ↦ right_ne_zero_of_mul ha

@[simp]
theorem hahnDeriv_zero (φ : ℝ →+ R) : hahnDeriv φ 0 = 0 := by
  ext a; simp

@[simp]
theorem hahnDeriv_single (φ : ℝ →+ R) (a : ℝ) (r : R) :
    hahnDeriv φ (HahnSeries.single a r) = HahnSeries.single a (φ a * r) := by
  classical
  ext b
  simp only [hahnDeriv_coeff, HahnSeries.coeff_single]
  split_ifs with h
  · subst h; rfl
  · simp

@[simp]
theorem hahnDeriv_C (φ : ℝ →+ R) (r : R) :
    hahnDeriv φ (HahnSeries.C r) = 0 := by
  rw [HahnSeries.C_apply, hahnDeriv_single, map_zero, zero_mul, HahnSeries.single_eq_zero]

theorem hahnDeriv_add (φ : ℝ →+ R) (x y : HahnSeries ℝ R) :
    hahnDeriv φ (x + y) = hahnDeriv φ x + hahnDeriv φ y := by
  ext a
  simp only [hahnDeriv_coeff, HahnSeries.coeff_add]
  ring

theorem hahnDeriv_smul [CommRing K] [Algebra K R] (φ : ℝ →+ R) (c : K) (x : HahnSeries ℝ R) :
    hahnDeriv φ (c • x) = c • hahnDeriv φ x := by
  ext a
  rw [hahnDeriv_coeff, HahnSeries.coeff_smul, HahnSeries.coeff_smul, hahnDeriv_coeff,
      Algebra.smul_def, Algebra.smul_def]
  ring

/-- **Exact Leibniz Product Rule** for `hahnDeriv` on `HahnSeries ℝ R`. -/
theorem hahnDeriv_mul (φ : ℝ →+ R) (x y : HahnSeries ℝ R) :
    hahnDeriv φ (x * y) = hahnDeriv φ x * y + x * hahnDeriv φ y := by
  ext a
  rw [HahnSeries.coeff_add, hahnDeriv_coeff, HahnSeries.coeff_mul,
      HahnSeries.coeff_mul_left' x.isPWO_support (hahnDeriv_support_subset φ x),
      HahnSeries.coeff_mul_right' y.isPWO_support (hahnDeriv_support_subset φ y),
      Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  have hsum : ij.1 + ij.2 = a := (Finset.mem_antidiagonal.mp hij).2.2
  rw [← hsum, map_add, hahnDeriv_coeff, hahnDeriv_coeff]
  ring

/-- **Exact Multivariate Polynomial Chain Rule** for `hahnDeriv` on `HahnSeries ℝ R`. -/
theorem hahnDeriv_aeval [CommRing K] [Algebra K R] {ι : Type*} [Fintype ι]
    (φ : ℝ →+ R) (Y : ι → HahnSeries ℝ R) (P : MvPolynomial ι K) :
    hahnDeriv φ (MvPolynomial.aeval Y P) =
      ∑ j : ι, MvPolynomial.aeval Y (MvPolynomial.pderiv j P) * hahnDeriv φ (Y j) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c =>
    have hC : MvPolynomial.aeval Y (MvPolynomial.C c) = HahnSeries.C (algebraMap K R c) := by
      simp [HahnSeries.algebraMap_apply]
    rw [hC, hahnDeriv_C]
    simp
  | add p q hp hq =>
    simp only [map_add, hahnDeriv_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, hahnDeriv_mul, hp, MvPolynomial.aeval_X,
      Derivation.leibniz, smul_eq_mul, map_add, MvPolynomial.pderiv_X, Pi.single_apply,
      apply_ite (MvPolynomial.aeval Y), map_one, map_zero]
    simp only [Finset.sum_mul, add_mul, Finset.sum_add_distrib]
    have hdiag : (∑ j : ι, (MvPolynomial.aeval Y p * (if k = j then (1 : HahnSeries ℝ R) else 0)) *
        hahnDeriv φ (Y j)) = MvPolynomial.aeval Y p * hahnDeriv φ (Y k) := by
      have hterm : ∀ j : ι, (MvPolynomial.aeval Y p * (if k = j then (1 : HahnSeries ℝ R) else 0)) *
          hahnDeriv φ (Y j) = if k = j then MvPolynomial.aeval Y p * hahnDeriv φ (Y k) else 0 := by
        intro j; split_ifs with h <;> simp [h]
      simp_rw [hterm]
      simp
    rw [hdiag, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Canonical `R`-algebra embedding `AddMonoidAlgebra R ℝ →ₐ[R] HahnSeries ℝ R`
identifying finitely supported exponential sums with Hahn series. -/
def addMonoidAlgebraToHahn : AddMonoidAlgebra R ℝ →ₐ[R] HahnSeries ℝ R :=
  AddMonoidAlgebra.lift R (HahnSeries ℝ R) ℝ
    { toFun := fun a ↦ HahnSeries.single (Multiplicative.toAdd a) (1 : R)
      map_one' := by simp [HahnSeries.single_zero_one]
      map_mul' := fun a b ↦ by simp [HahnSeries.single_mul_single] }

theorem addMonoidAlgebraToHahn_single (a : ℝ) (r : R) :
    addMonoidAlgebraToHahn (AddMonoidAlgebra.single a r) = HahnSeries.single a r := by
  ext b
  rw [addMonoidAlgebraToHahn, AddMonoidAlgebra.lift_single]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
    HahnSeries.coeff_smul, HahnSeries.coeff_single, smul_eq_mul, mul_ite, mul_one, mul_zero]

/-- `monoidDeriv` and `hahnDeriv` agree identically under `addMonoidAlgebraToHahn`. -/
theorem hahnDeriv_addMonoidAlgebraToHahn (φ : ℝ →+ R) (f : AddMonoidAlgebra R ℝ) :
    hahnDeriv φ (addMonoidAlgebraToHahn f) = addMonoidAlgebraToHahn (monoidDeriv φ f) := by
  induction f using AddMonoidAlgebra.induction_on with
  | of a =>
    change hahnDeriv φ (addMonoidAlgebraToHahn (AddMonoidAlgebra.single a (1 : R))) =
      addMonoidAlgebraToHahn (monoidDeriv φ (AddMonoidAlgebra.single a (1 : R)))
    rw [addMonoidAlgebraToHahn_single, monoidDeriv_single,
        hahnDeriv_single, addMonoidAlgebraToHahn_single]
  | add f g hf hg =>
    rw [map_add, hahnDeriv_add, hf, hg, monoidDeriv_add, map_add]
  | smul r f hf =>
    rw [map_smul, hahnDeriv_smul, hf, monoidDeriv_smul, map_smul]

/-! #### The 10-Line Jump-Point Elimination Engine (Probe 268 Theorem 2.1) -/

private theorem lower_totalDegree_domain {K ι : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (j : ι) (P : MvPolynomial ι K) (h : 0 < P.totalDegree) :
    (MvPolynomial.pderiv j P).totalDegree < P.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree_eq]
  apply lt_of_le_of_lt (Finset.sup_le fun m hm ↦ ?_) (Nat.pred_lt h.ne')
  have hn := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hn
  have hs := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn))
  change ((m + Finsupp.single j 1).sum fun _ ↦ id) ≤ _ at hs
  rw [← Finsupp.card_toMultiset, Finsupp.toMultiset_add, Finsupp.toMultiset_single] at hs
  simp at hs
  rw [Finsupp.card_toMultiset, Nat.pred_eq_sub_one]
  omega

private theorem eq_C_of_all_pderiv_zero {K ι : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (P : MvPolynomial ι K) (h : ∀ j, MvPolynomial.pderiv j P = 0) :
    P = MvPolynomial.C (P.coeff 0) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [MvPolynomial.coeff_C]
  by_cases hm : m = 0
  · subst hm; exact (ite_eq_left rfl).symm
  · rw [ite_eq_right (Ne.symm hm)]
    obtain ⟨j, hj⟩ : ∃ j, m j ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hm (Finsupp.ext hall)
    have h0 := congrArg (fun f : MvPolynomial ι K ↦ f.coeff (m - Finsupp.single j 1)) (h j)
    simp only [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel hj] at h0
    have hnat : (((m - Finsupp.single j (1 : ℕ)) j : K) + 1) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero ((m - Finsupp.single j (1 : ℕ)) j)
    exact (mul_eq_zero.mp h0).resolve_right hnat

private theorem isWF_iUnion_fin {n : ℕ} (S : Fin n → Set ℝ) (hS : ∀ i, (S i).IsWF) :
    (⋃ i : Fin n, S i).IsWF := by
  induction n with
  | zero =>
    simp [Set.isWF_empty]
  | succ k ih =>
    have heq : (⋃ i : Fin (k + 1), S i) = S 0 ∪ ⋃ j : Fin k, S j.succ := by
      ext x
      simp only [Set.mem_iUnion, Set.mem_union, Fin.exists_fin_succ]
    rw [heq]
    exact (hS 0).union (ih (fun j ↦ S j.succ) (fun j ↦ hS j.succ))

/-- **Probe 268 Theorem 2.1 (Abstract Jump-Point Derivation Engine)**:
Let `K` be any `CharZero` integral domain, `R` any commutative `K`-algebra with injective
`algebraMap K R` and a ring hom `ratHom : ℚ →+* R`, `A ⊆ ℝ` any action set, and
`Y : Fin J → HahnSeries ℝ R` formal series supported on `A`. If there exist `J` jump points
`a : Fin J → ℝ` in `JumpSet A` such that the jump-point leading coefficient matrix
`M_{i,j} = (Y j).coeff (a i)` has `M.det ∈ nonZeroDivisors R`, then `Y₀, …, Y_{J-1}` are
**algebraically independent over `K`**. -/
theorem jumpPoint_algebraicIndependent {K R : Type*}
    [CommRing K] [IsDomain K] [CharZero K] [CommRing R] [Algebra K R]
    (hinj : Function.Injective (algebraMap K R)) (ratHom : ℚ →+* R)
    {A : Set ℝ} {J : ℕ} (a : Fin J → ℝ) (ha : ∀ i : Fin J, a i ∈ JumpSet A)
    (Y : Fin J → HahnSeries ℝ R) (hsupp : ∀ j : Fin J, (Y j).support ⊆ A)
    (hdet : (Matrix.of fun i j : Fin J ↦ (Y j).coeff (a i)).det ∈ nonZeroDivisors R) :
    AlgebraicIndependent K Y := by
  classical
  let M : Matrix (Fin J) (Fin J) R := Matrix.of fun i j ↦ (Y j).coeff (a i)
  let ev := MvPolynomial.aeval (R := K) Y
  -- Core step: any vanishing polynomial relation `ev P = 0` forces every partial `ev (pderiv j P) = 0`.
  have hstable : ∀ {P : MvPolynomial (Fin J) K}, ev P = 0 → ∀ j : Fin J, ev (pderiv j P) = 0 := by
    intro P hP
    by_contra hnot
    push Not at hnot
    obtain ⟨j₀, hj₀⟩ := hnot
    let G : Fin J → HahnSeries ℝ R := fun j ↦ ev (pderiv j P)
    let S : Set ℝ := ⋃ j : Fin J, (G j).support
    have hSne : S.Nonempty := by
      obtain ⟨μ, hμ⟩ := HahnSeries.support_nonempty_iff.mpr hj₀
      exact ⟨μ, Set.mem_iUnion.mpr ⟨j₀, hμ⟩⟩
    have hSwf : S.IsWF := isWF_iUnion_fin (fun j ↦ (G j).support) (fun j ↦ (G j).isWF_support)
    let μ₀ : ℝ := hSwf.min hSne
    have hμ₀_mem : μ₀ ∈ S := hSwf.min_mem hSne
    have hμ₀_le : ∀ (j : Fin J) (x : ℝ), x ∈ (G j).support → μ₀ ≤ x := by
      intro j x hx
      by_contra hlt
      exact hSwf.not_lt_min hSne (Set.mem_iUnion.mpr ⟨j, hx⟩) (not_le.mp hlt)
    let r : Fin J → R := fun j ↦ (G j).coeff μ₀
    have hr_ne : r ≠ 0 := by
      obtain ⟨j₁, hj₁⟩ := Set.mem_iUnion.mp hμ₀_mem
      intro hr0
      exact hj₁ (congrFun hr0 j₁)
    -- For each jump point `a i`, apply `hahnDeriv ψ_i` and extract `[e^{-(μ₀ + a i)}]`.
    have hMr : M *ᵥ r = 0 := by
      funext i
      obtain ⟨φ, hφa, hφU⟩ := exists_jump_functional (ha i)
      let ψ : ℝ →+ R := ratHom.toAddMonoidHom.comp φ.toAddMonoidHom
      have hψa : ψ (a i) = 1 := by simp [ψ, hφa]
      have hψ_lt : ∀ b ∈ A, b < a i → ψ b = 0 := fun b hb hlt ↦ by
        simp [ψ, hφU b (Submodule.subset_span ⟨hb, hlt⟩)]
      have hchain : (∑ j : Fin J, G j * hahnDeriv ψ (Y j)) = 0 := by
        have h0 := hahnDeriv_aeval ψ Y P
        rw [hP, hahnDeriv_zero] at h0
        exact h0.symm
      have hcoeff_sum : ∑ j : Fin J, (G j * hahnDeriv ψ (Y j)).coeff (μ₀ + a i) = 0 := by
        have hc := congrArg (fun f : HahnSeries ℝ R ↦ f.coeff (μ₀ + a i)) hchain
        simpa [HahnSeries.coeff_sum] using hc
      -- At exponent `μ₀ + a i`, EVERY summand collapses to `r j * M i j` with ZERO collisions!
      have hterm (j : Fin J) :
          (G j * hahnDeriv ψ (Y j)).coeff (μ₀ + a i) = M i j * r j := by
        rw [HahnSeries.coeff_mul]
        have honly : ∀ pq ∈ Finset.antidiagonal (G j).isPWO_support
            (hahnDeriv ψ (Y j)).isPWO_support (μ₀ + a i), pq = (μ₀, a i) := by
          rintro ⟨x, y⟩ hpq
          have ⟨hx, hy, hxy⟩ := Finset.mem_antidiagonal.mp hpq
          have hx_ge : μ₀ ≤ x := hμ₀_le j x hx
          have hy_ge : a i ≤ y := by
            by_contra hlt
            have hy_lt : y < a i := not_le.mp hlt
            have hyA : y ∈ A := hsupp j (hahnDeriv_support_subset ψ (Y j) hy)
            have h0 : (hahnDeriv ψ (Y j)).coeff y = 0 := by
              rw [hahnDeriv_coeff, hψ_lt y hyA hy_lt, zero_mul]
            exact hy h0
          exact Prod.ext (by linarith) (by linarith)
        by_cases hmem : (μ₀, a i) ∈ Finset.antidiagonal (G j).isPWO_support
            (hahnDeriv ψ (Y j)).isPWO_support (μ₀ + a i)
        · rw [Finset.sum_eq_single (μ₀, a i)
            (fun pq hpq hne ↦ absurd (honly pq hpq) hne)
            (fun hnot ↦ absurd hmem hnot)]
          rw [hahnDeriv_coeff, hψa, one_mul, mul_comm]
          rfl
        · have hemp : Finset.antidiagonal (G j).isPWO_support
              (hahnDeriv ψ (Y j)).isPWO_support (μ₀ + a i) = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro pq hpq
            exact hmem (honly pq hpq ▸ hpq)
          rw [hemp, Finset.sum_empty]
          rw [Finset.mem_antidiagonal] at hmem
          push Not at hmem
          by_cases hG0 : (G j).coeff μ₀ = 0
          · simp [r, hG0]
          · have hY0 : (hahnDeriv ψ (Y j)).coeff (a i) = 0 := by
              by_contra hne
              exact hmem hG0 hne rfl
            rw [hahnDeriv_coeff, hψa, one_mul] at hY0
            simp [M, hY0]
      simp_rw [hterm] at hcoeff_sum
      simpa [Matrix.mulVec, dotProduct] using hcoeff_sum
    exact hr_ne (M.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hdet hMr)
  -- Finish by strong induction on `P.totalDegree`.
  apply algebraicIndependent_iff.mpr
  intro P
  induction P using (measure fun P : MvPolynomial (Fin J) K ↦ P.totalDegree).wf.induction with
  | h P ih =>
    intro hP
    have fromConst (hc : P = MvPolynomial.C (P.coeff 0)) : P = 0 := by
      have hh : HahnSeries.C (algebraMap K R (P.coeff 0)) = (0 : HahnSeries ℝ R) := by
        have h1 : ev (MvPolynomial.C (P.coeff 0)) = 0 := hc ▸ hP
        simpa [ev, MvPolynomial.aeval_C, HahnSeries.algebraMap_apply] using h1
      have h0 : algebraMap K R (P.coeff 0) = 0 := by
        have := congrArg (fun f : HahnSeries ℝ R ↦ f.coeff 0) hh
        simpa using this
      have hc0 : P.coeff 0 = 0 := hinj (h0.trans (map_zero _).symm)
      rw [hc, hc0, MvPolynomial.C_0]
    rcases Nat.eq_zero_or_pos P.totalDegree with he | he
    · exact fromConst (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp he)
    · exact fromConst (eq_C_of_all_pderiv_zero P fun j ↦
        ih _ (lower_totalDegree_domain j P he) (hstable hP j))

/-! #### Formal `-X`-Derivative & Vandermonde Elimination on Pure Exponential Series -/

/-- The formal `-X`-derivative `∂_X (∑ c_a e^{-a X}) = ∑ (-a) c_a e^{-a X}` on
`HahnSeries ℝ R` for any commutative `ℝ`-algebra `R`, realized directly as `hahnDeriv`. -/
def expDeriv [Algebra ℝ R] (Y : HahnSeries ℝ R) : HahnSeries ℝ R :=
  hahnDeriv (-(algebraMap ℝ R).toAddMonoidHom) Y

@[simp]
theorem expDeriv_coeff [Algebra ℝ R] (Y : HahnSeries ℝ R) (a : ℝ) :
    (expDeriv Y).coeff a = -(algebraMap ℝ R a) * Y.coeff a := by
  rfl

theorem expDeriv_iterate_coeff [Algebra ℝ R] (Y : HahnSeries ℝ R) (j : ℕ) (a : ℝ) :
    (expDeriv^[j] Y).coeff a = (-(algebraMap ℝ R a)) ^ j * Y.coeff a := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', expDeriv_coeff, ih, pow_succ']
    ring

theorem expDeriv_iterate_support_subset [Algebra ℝ R] (Y : HahnSeries ℝ R) (j : ℕ) :
    (expDeriv^[j] Y).support ⊆ Y.support := by
  intro a ha
  rw [HahnSeries.mem_support, expDeriv_iterate_coeff] at ha
  exact right_ne_zero_of_mul ha

/-- Exact determinant factorization of the jump-point jet matrix
`M_{i,j} = (expDeriv^[j] Y).coeff (a i)` as diagonal amplitudes times Vandermonde. -/
theorem expDeriv_jumpMatrix_det [Algebra ℝ R] {J : ℕ} (a : Fin J → ℝ) (Y : HahnSeries ℝ R) :
    (Matrix.of fun i j : Fin J ↦ (expDeriv^[j.val] Y).coeff (a i)).det =
      (∏ i : Fin J, Y.coeff (a i)) *
        (Matrix.vandermonde fun i : Fin J ↦ -(algebraMap ℝ R (a i))).det := by
  have hmat : (Matrix.of fun i j : Fin J ↦ (expDeriv^[j.val] Y).coeff (a i)) =
      Matrix.diagonal (fun i : Fin J ↦ Y.coeff (a i)) *
        Matrix.vandermonde (fun i : Fin J ↦ -(algebraMap ℝ R (a i))) := by
    ext i j
    simp only [Matrix.of_apply, expDeriv_iterate_coeff, Matrix.diagonal_mul,
      Matrix.vandermonde_apply, mul_comm]
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal]

/-- **Vandermonde Elimination for Pure Exponential Series (`jumpPoint_minimal_relation_vandermonde`)**:
Given any well-ordered action set `A ⊆ ℝ` of infinite `ℚ`-rank, any commutative `ℝ`-algebra `R`
which is a `K`-algebra over a `CharZero` field `K` (with injective `algebraMap K R` and
`algebraMap ℝ R` sending nonzero reals to `nonZeroDivisors R`), and any formal exponential
series `Y : HahnSeries ℝ R` supported on `A` whose jump-point amplitudes are non-zero-divisors
in `R`, the derivative jet `(Y, ∂_X Y, …, ∂_X^{J-1} Y)` is **algebraically independent over `K`**
for EVERY order `J : ℕ`! -/
theorem jumpPoint_minimal_relation_vandermonde {K R : Type*}
    [Field K] [CharZero K] [CommRing R] [Algebra K R] [Algebra ℝ R]
    (hinjK : Function.Injective (algebraMap K R))
    (hRnzd : ∀ x : ℝ, x ≠ 0 → algebraMap ℝ R x ∈ nonZeroDivisors R)
    {A : Set ℝ} (hA : A.IsWF) (hinf : ¬ Module.Finite ℚ (Submodule.span ℚ A))
    (Y : HahnSeries ℝ R) (hsupp : Y.support ⊆ A)
    (hamp : ∀ a ∈ JumpSet A, Y.coeff a ∈ nonZeroDivisors R) (J : ℕ) :
    AlgebraicIndependent K (fun j : Fin J ↦ expDeriv^[j.val] Y) := by
  obtain ⟨a, ha_mono, ha_jump, _⟩ := jumpPoints_exist_of_isWF hA hinf J
  have hdet : (Matrix.of fun i j : Fin J ↦ (expDeriv^[j.val] Y).coeff (a i)).det ∈
      nonZeroDivisors R := by
    rw [expDeriv_jumpMatrix_det, Matrix.det_vandermonde]
    refine Submonoid.mul_mem (nonZeroDivisors R) ?_ ?_
    · exact Submonoid.prod_mem (nonZeroDivisors R) fun i _ ↦ hamp (a i) (ha_jump i)
    · refine Submonoid.prod_mem (nonZeroDivisors R) fun i _ ↦
        Submonoid.prod_mem (nonZeroDivisors R) fun j hj ↦ ?_
      have hij : a i < a j := ha_mono (Finset.mem_Ioi.mp hj)
      have hdiff : -(algebraMap ℝ R (a j)) - -(algebraMap ℝ R (a i)) =
          algebraMap ℝ R (a i - a j) := by
        rw [map_sub]; ring
      rw [hdiff]
      exact hRnzd (a i - a j) (sub_ne_zero.mpr hij.ne)
  exact jumpPoint_algebraicIndependent hinjK ((algebraMap K R).comp (Rat.castHom K))
    a ha_jump (fun j : Fin J ↦ expDeriv^[j.val] Y)
    (fun j ↦ (expDeriv_iterate_support_subset Y j.val).trans hsupp) hdet

end HahnDeriv

/-! ### 3. Full Formal Transseries with Arbitrary Asymptotic Prefactors `c_a X^{β_a}` -/

/-- Formal asymptotic coefficient series in `X⁻¹` with arbitrary real exponents:
`HahnSeries.single (-β) c` represents `c · X^β`. -/
abbrev AsympCoeff := HahnSeries ℝ ℂ

/-- Formal exponential transseries `∑_{a} c_a(X) e^{-a X}` with well-ordered action
support and full real-power asymptotic amplitudes `c_a(X) ∈ AsympCoeff`. -/
abbrev TransSeries := HahnSeries ℝ AsympCoeff

/-- Formal `X`-derivative on `AsympCoeff`: since `single (-β) c` represents `c X^β`,
its `X`-derivative is `single (-β + 1) (β c)`, so at exponent `γ` the coefficient is
`-(γ - 1) * f.coeff (γ - 1)`. -/
def asympDerivX (f : AsympCoeff) : AsympCoeff where
  coeff γ := -(((γ - 1 : ℝ) : ℂ)) * f.coeff (γ - 1)
  isPWO_support' := by
    have hshift : (Set.image (fun x : ℝ ↦ x + 1) f.support).IsPWO := by
      have h1 : ({(1 : ℝ)} : Set ℝ).IsPWO := Set.isPWO_singleton (1 : ℝ)
      have heq : Set.image (fun x : ℝ ↦ x + 1) f.support = f.support + ({(1 : ℝ)} : Set ℝ) := by
        ext γ; simp
      rw [heq]
      exact f.isPWO_support.add h1
    refine hshift.mono fun γ hγ ↦ ?_
    exact ⟨γ - 1, right_ne_zero_of_mul hγ, sub_add_cancel γ 1⟩

@[simp]
theorem asympDerivX_coeff (f : AsympCoeff) (γ : ℝ) :
    (asympDerivX f).coeff γ = -(((γ - 1 : ℝ) : ℂ)) * f.coeff (γ - 1) := by
  rfl

theorem asympDerivX_add (f g : AsympCoeff) :
    asympDerivX (f + g) = asympDerivX f + asympDerivX g := by
  ext γ; simp [HahnSeries.coeff_add]; ring

theorem asympDerivX_smul (c : ℂ) (f : AsympCoeff) :
    asympDerivX (c • f) = c • asympDerivX f := by
  ext γ; simp; ring

/-- Differentiating an asymptotic power series in `X` strictly increases its `X⁻¹`-order
by at least `1`! -/
theorem asympDerivX_orderTop_gt {f : AsympCoeff} (hf : f ≠ 0) :
    f.orderTop < (asympDerivX f).orderTop := by
  by_cases hd : asympDerivX f = 0
  · rw [hd, HahnSeries.orderTop_zero]
    exact lt_top_iff_ne_top.mpr (HahnSeries.orderTop_ne_top.mpr hf)
  · rw [HahnSeries.orderTop_of_ne_zero hf, HahnSeries.orderTop_of_ne_zero hd,
        WithTop.coe_lt_coe]
    have hmin_mem : Set.IsWF.min (asympDerivX f).isWF_support
        (HahnSeries.support_nonempty_iff.mpr hd) ∈ (asympDerivX f).support :=
      Set.IsWF.min_mem _ _
    set γ₀ := Set.IsWF.min (asympDerivX f).isWF_support
      (HahnSeries.support_nonempty_iff.mpr hd)
    have hprev : γ₀ - 1 ∈ f.support := right_ne_zero_of_mul hmin_mem
    have hle : Set.IsWF.min f.isWF_support (HahnSeries.support_nonempty_iff.mpr hf) ≤ γ₀ - 1 :=
      Set.IsWF.min_le f.isWF_support (HahnSeries.support_nonempty_iff.mpr hf) hprev
    linarith

/-- Total formal `X`-derivative on `TransSeries = HahnSeries ℝ AsympCoeff`:
`D_X (∑ c_a(X) e^{-a X}) = ∑ (c_a'(X) - a c_a(X)) e^{-a X}`. -/
def transDerivX (Y : TransSeries) : TransSeries where
  coeff a := asympDerivX (Y.coeff a) + (-(a : ℂ)) • Y.coeff a
  isPWO_support' := Y.isPWO_support.mono fun a ha ↦ by
    intro h0
    apply ha
    have hdz : asympDerivX (0 : AsympCoeff) = 0 := by ext γ; simp
    simp [h0, hdz]

@[simp]
theorem transDerivX_coeff (Y : TransSeries) (a : ℝ) :
    (transDerivX Y).coeff a = asympDerivX (Y.coeff a) + (-(a : ℂ)) • Y.coeff a := by
  rfl

theorem transDerivX_support_subset (Y : TransSeries) :
    (transDerivX Y).support ⊆ Y.support := by
  intro a ha h0
  apply ha
  have hdz : asympDerivX (0 : AsympCoeff) = 0 := by ext γ; simp
  simp [h0, hdz]

theorem transDerivX_iterate_support_subset (Y : TransSeries) (j : ℕ) :
    (transDerivX^[j] Y).support ⊆ Y.support := by
  induction j with
  | zero => exact Set.Subset.rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact (transDerivX_support_subset _).trans ih

/-- **Exact Leading Asymptotics of `transDerivX^[j]`**: for any nonzero action `a ≠ 0`
and any mode with nonzero asymptotic amplitude `Y.coeff a ≠ 0`, differentiating `j` times
preserves the exact `X⁻¹`-order and multiplies the leading coefficient by `(-a)^j`! -/
theorem transDerivX_iterate_leading {Y : TransSeries} {a : ℝ} (ha : a ≠ 0)
    (hYa : Y.coeff a ≠ 0) (j : ℕ) :
    ((transDerivX^[j] Y).coeff a).orderTop = (Y.coeff a).orderTop ∧
    ((transDerivX^[j] Y).coeff a).leadingCoeff = (-(a : ℂ)) ^ j * (Y.coeff a).leadingCoeff := by
  induction j with
  | zero => simp
  | succ n ih =>
    obtain ⟨hord, hlead⟩ := ih
    rw [Function.iterate_succ_apply', transDerivX_coeff]
    set g : AsympCoeff := (transDerivX^[n] Y).coeff a
    have hg0 : g ≠ 0 := by
      intro h
      rw [h, HahnSeries.orderTop_zero] at hord
      exact HahnSeries.orderTop_ne_top.mpr hYa hord.symm
    have haC : (-(a : ℂ)) ≠ 0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr ha)
    have hsmul_ne : (-(a : ℂ)) • g ≠ 0 := by
      intro h
      have := congrArg (fun x : AsympCoeff ↦ x.leadingCoeff) h
      rw [HahnSeries.leadingCoeff_zero] at this
      have hgle : g.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hg0
      have hsc : ((-(a : ℂ)) • g).coeff g.order ≠ 0 := by
        rw [HahnSeries.coeff_smul, smul_eq_mul, ← HahnSeries.leadingCoeff_eq]
        exact mul_ne_zero haC hgle
      exact hsc (by simp [h])
    have hsmul_ord : ((-(a : ℂ)) • g).orderTop = g.orderTop := by
      apply le_antisymm
      · rw [← HahnSeries.order_eq_orderTop_of_ne_zero hg0]
        apply HahnSeries.orderTop_le_of_coeff_ne_zero
        rw [HahnSeries.coeff_smul, smul_eq_mul, ← HahnSeries.leadingCoeff_eq]
        exact mul_ne_zero haC (HahnSeries.leadingCoeff_ne_zero.mpr hg0)
      · exact HahnSeries.orderTop_le_orderTop_smul (-(a : ℂ)) g
    have hsmul_lead : ((-(a : ℂ)) • g).leadingCoeff = (-(a : ℂ)) * g.leadingCoeff := by
      have hord_eq : ((-(a : ℂ)) • g).order = g.order := by
        have h1 := hsmul_ord
        rw [← HahnSeries.order_eq_orderTop_of_ne_zero hsmul_ne,
            ← HahnSeries.order_eq_orderTop_of_ne_zero hg0, WithTop.coe_eq_coe] at h1
        exact h1
      rw [HahnSeries.leadingCoeff_eq, hord_eq, HahnSeries.coeff_smul, smul_eq_mul,
          ← HahnSeries.leadingCoeff_eq]
    have hlt : ((-(a : ℂ)) • g).orderTop < (asympDerivX g).orderTop := by
      rw [hsmul_ord]
      exact asympDerivX_orderTop_gt hg0
    refine ⟨?_, ?_⟩
    · rw [HahnSeries.orderTop_add_eq_right hlt, hsmul_ord, hord]
    · rw [HahnSeries.leadingCoeff_add_eq_right hlt, hsmul_lead, hlead, pow_succ']
      ring

/-- Nonnegative-order evaluation: on products of `AsympCoeff` series with `orderTop ≥ 0`,
extracting `.coeff 0` is multiplicative. -/
private theorem coeff_zero_mul_of_nonneg {f g : AsympCoeff}
    (hf : (0 : WithTop ℝ) ≤ f.orderTop) (hg : (0 : WithTop ℝ) ≤ g.orderTop) :
    (f * g).coeff 0 = f.coeff 0 * g.coeff 0 := by
  rw [HahnSeries.coeff_mul]
  have honly : ∀ pq ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support (0 : ℝ),
      pq = (0, 0) := by
    rintro ⟨x, y⟩ hpq
    have ⟨hx, hy, hxy⟩ := Finset.mem_antidiagonal.mp hpq
    have hx0 : 0 ≤ x := by
      by_contra hlt
      exact hx (HahnSeries.coeff_eq_zero_of_lt_orderTop
        (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (not_le.mp hlt)) hf))
    have hy0 : 0 ≤ y := by
      by_contra hlt
      exact hy (HahnSeries.coeff_eq_zero_of_lt_orderTop
        (lt_of_lt_of_le (WithTop.coe_lt_coe.mpr (not_le.mp hlt)) hg))
    exact Prod.ext (by linarith) (by linarith)
  by_cases hmem : ((0 : ℝ), (0 : ℝ)) ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support (0 : ℝ)
  · exact Finset.sum_eq_single (0, 0) (fun pq hpq hne ↦ absurd (honly pq hpq) hne)
      (fun hnot ↦ absurd hmem hnot)
  · have hemp : Finset.antidiagonal f.isPWO_support g.isPWO_support (0 : ℝ) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro pq hpq
      exact hmem (honly pq hpq ▸ hpq)
    rw [hemp, Finset.sum_empty]
    rw [Finset.mem_antidiagonal] at hmem
    push Not at hmem
    by_cases hf0 : f.coeff 0 = 0
    · simp [hf0]
    · have hg0 : g.coeff 0 = 0 := by
        by_contra hne
        exact hmem hf0 hne (add_zero 0)
      simp [hg0]

private theorem coeff_zero_finset_prod_of_nonneg {ι : Type*} (s : Finset ι)
    (f : ι → AsympCoeff) (hf : ∀ i ∈ s, (0 : WithTop ℝ) ≤ (f i).orderTop) :
    (0 : WithTop ℝ) ≤ (∏ i ∈ s, f i).orderTop ∧
      (∏ i ∈ s, f i).coeff 0 = ∏ i ∈ s, (f i).coeff 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    obtain ⟨hord_s, hcoeff_s⟩ := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
    have hord_i : (0 : WithTop ℝ) ≤ (f i).orderTop := hf i (Finset.mem_insert_self i s)
    refine ⟨?_, ?_⟩
    · rw [HahnSeries.orderTop_mul]
      exact add_nonneg hord_i hord_s
    · rw [coeff_zero_mul_of_nonneg hord_i hord_s, hcoeff_s]

/-- **Transseries Vandermonde Determinant Non-Vanishing**: for any strictly increasing
nonzero jump actions `a : Fin J → ℝ` and any `Y : TransSeries` with nonzero asymptotic
amplitudes `Y.coeff (a i) ≠ 0`, the `J × J` jet matrix `M_{i,j} = (transDerivX^[j] Y).coeff (a i)`
has **nonzero determinant** in `AsympCoeff`! -/
theorem transseries_vandermonde_det_ne_zero {J : ℕ} (a : Fin J → ℝ)
    (ha_mono : StrictMono a) (ha_nz : ∀ i : Fin J, a i ≠ 0)
    (Y : TransSeries) (hY : ∀ i : Fin J, Y.coeff (a i) ≠ 0) :
    (Matrix.of fun i j : Fin J ↦ (transDerivX^[j.val] Y).coeff (a i)).det ≠ 0 := by
  let o : Fin J → ℝ := fun i ↦ (Y.coeff (a i)).order
  let D : Matrix (Fin J) (Fin J) AsympCoeff :=
    Matrix.diagonal fun i ↦ HahnSeries.single (-o i) (1 : ℂ)
  let M : Matrix (Fin J) (Fin J) AsympCoeff :=
    Matrix.of fun i j ↦ (transDerivX^[j.val] Y).coeff (a i)
  let M' : Matrix (Fin J) (Fin J) AsympCoeff := D * M
  -- Every entry of `M'` has nonnegative `X⁻¹`-order and constant term `(-a i)^j * leadingCoeff`.
  have hM'_entry (i j : Fin J) :
      M' i j = HahnSeries.single (-o i) (1 : ℂ) * (transDerivX^[j.val] Y).coeff (a i) := by
    simp [M', D, M, Matrix.diagonal_mul]
  have hM'_nonneg (i j : Fin J) : (0 : WithTop ℝ) ≤ (M' i j).orderTop := by
    rw [hM'_entry, HahnSeries.orderTop_mul, HahnSeries.orderTop_single one_ne_zero,
        (transDerivX_iterate_leading (ha_nz i) (hY i) j.val).1,
        ← HahnSeries.order_eq_orderTop_of_ne_zero (hY i)]
    change (0 : WithTop ℝ) ≤ ((-o i + o i : ℝ) : WithTop ℝ)
    simp
  have hM'_c0 (i j : Fin J) :
      (M' i j).coeff 0 = (-(a i : ℂ)) ^ j.val * (Y.coeff (a i)).leadingCoeff := by
    rw [hM'_entry, HahnSeries.coeff_single_mul, zero_sub, neg_neg, one_mul]
    have hlead := transDerivX_iterate_leading (ha_nz i) (hY i) j.val
    have hne : (transDerivX^[j.val] Y).coeff (a i) ≠ 0 := by
      intro h0
      have h1 := hlead.1
      rw [h0, HahnSeries.orderTop_zero] at h1
      exact HahnSeries.orderTop_ne_top.mpr (hY i) h1.symm
    have hord_eq : ((transDerivX^[j.val] Y).coeff (a i)).order = o i := by
      have h1 := hlead.1
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero hne,
          ← HahnSeries.order_eq_orderTop_of_ne_zero (hY i), WithTop.coe_eq_coe] at h1
      exact h1
    rw [← hord_eq, ← HahnSeries.leadingCoeff_eq]
    exact hlead.2
  -- Compute `(M'.det).coeff 0` via the Leibniz determinant expansion.
  have hdet_c0 : (M'.det).coeff 0 =
      (Matrix.of fun i j : Fin J ↦ (-(a i : ℂ)) ^ j.val * (Y.coeff (a i)).leadingCoeff).det := by
    rw [Matrix.det_apply, Matrix.det_apply, HahnSeries.coeff_sum]
    apply Finset.sum_congr rfl
    intro σ _
    have hsign_int : ∀ (z : ℤ) (x : AsympCoeff), (z • x).coeff 0 = z • x.coeff 0 := fun z x ↦ by
      induction z using Int.induction_on with
      | zero => simp
      | succ n ih =>
        rw [add_zsmul, one_zsmul, HahnSeries.coeff_add, ih, add_zsmul, one_zsmul]
      | pred n ih =>
        rw [sub_zsmul, one_zsmul, sub_eq_add_neg, HahnSeries.coeff_add, HahnSeries.coeff_neg,
            ih, add_zsmul, neg_one_zsmul]
    rw [Units.smul_def, Units.smul_def, hsign_int]
    congr 1
    have hprod := coeff_zero_finset_prod_of_nonneg Finset.univ
      (fun i : Fin J ↦ M' (σ i) i) (fun i _ ↦ hM'_nonneg (σ i) i)
    rw [hprod.2]
    exact Finset.prod_congr rfl fun i _ ↦ hM'_c0 (σ i) i
  have hdetC_ne : (M'.det).coeff 0 ≠ 0 := by
    rw [hdet_c0]
    have hfac : (Matrix.of fun i j : Fin J ↦ (-(a i : ℂ)) ^ j.val * (Y.coeff (a i)).leadingCoeff) =
        Matrix.diagonal (fun i : Fin J ↦ (Y.coeff (a i)).leadingCoeff) *
          Matrix.vandermonde (fun i : Fin J ↦ -(a i : ℂ)) := by
      ext i j
      simp [Matrix.diagonal_mul, Matrix.vandermonde_apply, mul_comm]
    rw [hfac, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_vandermonde]
    refine mul_ne_zero ?_ ?_
    · exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ HahnSeries.leadingCoeff_ne_zero.mpr (hY i)
    · refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ Finset.prod_ne_zero_iff.mpr fun j hj ↦ ?_
      have hij : a i < a j := ha_mono (Finset.mem_Ioi.mp hj)
      have hsub : -(a j : ℂ) - -(a i : ℂ) = ((a i - a j : ℝ) : ℂ) := by push_cast; ring
      rw [hsub]
      exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hij.ne)
  have hM'_det_ne : M'.det ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero hdetC_ne
  intro hM0
  apply hM'_det_ne
  rw [show M' = D * M from rfl, Matrix.det_mul, hM0, mul_zero]

/-- **Full Transseries Jump-Point Algebraic Independence Theorem**:
For ANY well-ordered positive action set `A ⊆ (0, ∞)` of infinite `ℚ`-rank and ANY formal
transseries `Y : TransSeries` supported on `A` whose jump-point asymptotic coefficients are
nonzero (`∀ a ∈ JumpSet A, Y.coeff a ≠ 0`), for EVERY order `J : ℕ`, the `X`-derivative jet
`(Y, D_X Y, …, D_X^{J-1} Y)` is **algebraically independent over the full asymptotic ring
`AsympCoeff = HahnSeries ℝ ℂ`**! -/
theorem jumpPoint_transseries_algebraicIndependent {A : Set ℝ} (hpos : ∀ a ∈ A, 0 < a)
    (hA : A.IsWF) (hinf : ¬ Module.Finite ℚ (Submodule.span ℚ A))
    (Y : TransSeries) (hsupp : Y.support ⊆ A)
    (hamp : ∀ a ∈ JumpSet A, Y.coeff a ≠ 0) (J : ℕ) :
    AlgebraicIndependent AsympCoeff (fun j : Fin J ↦ transDerivX^[j.val] Y) := by
  have : CharZero AsympCoeff := charZero_of_injective_algebraMap
    (R := ℂ) (HahnSeries.C_injective (Γ := ℝ) (R := ℂ))
  obtain ⟨a, ha_mono, ha_jump, _⟩ := jumpPoints_exist_of_isWF hA hinf J
  have hdet_ne : (Matrix.of fun i j : Fin J ↦ (transDerivX^[j.val] Y).coeff (a i)).det ≠ 0 :=
    transseries_vandermonde_det_ne_zero a ha_mono
      (fun i ↦ (hpos (a i) (ha_jump i).1).ne') Y (fun i ↦ hamp (a i) (ha_jump i))
  exact jumpPoint_algebraicIndependent Function.injective_id
    (HahnSeries.C.comp (Rat.castHom ℂ)) a ha_jump
    (fun j : Fin J ↦ transDerivX^[j.val] Y)
    (fun j ↦ (transDerivX_iterate_support_subset Y j.val).trans hsupp)
    (mem_nonZeroDivisors_of_ne_zero hdet_ne)

/-- Canonical injective ring homomorphism `ℂ[X] →+* AsympCoeff` sending `X ↦ single (-1) 1`
(the formal asymptotic variable `X = (X⁻¹)⁻¹`). -/
def polyToAsymp : Polynomial ℂ →+* AsympCoeff :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1 : ℝ) (1 : ℂ))

theorem polyToAsymp_coeff_neg_nat (p : Polynomial ℂ) (n : ℕ) :
    (polyToAsymp p).coeff (-(n : ℝ)) = p.coeff n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp [map_add, HahnSeries.coeff_add, hp, hq]
  | monomial k c =>
    rw [polyToAsymp, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
        HahnSeries.single_pow, HahnSeries.C_apply, HahnSeries.single_mul_single,
        zero_add, one_pow, mul_one, HahnSeries.coeff_single, Polynomial.coeff_monomial]
    by_cases hkn : k = n
    · simp [hkn]
    · simp [Ne.symm hkn]

theorem polyToAsymp_injective : Function.Injective polyToAsymp := by
  intro p q hpq
  ext n
  have := congrArg (fun f : AsympCoeff ↦ f.coeff (-(n : ℝ))) hpq
  simpa [polyToAsymp_coeff_neg_nat] using this

/-- **No Non-Autonomous Polynomial ADE Over `ℂ[X]`**: under the hypotheses of
`jumpPoint_transseries_algebraicIndependent`, NO nonzero polynomial
`P(X, T₀, …, T_{J-1}) ∈ ℂ[X][T₀, …, T_{J-1}]` vanishes on `(Y, D_X Y, …, D_X^{J-1} Y)`. -/
theorem jumpPoint_transseries_no_poly_ade {A : Set ℝ} (hpos : ∀ a ∈ A, 0 < a)
    (hA : A.IsWF) (hinf : ¬ Module.Finite ℚ (Submodule.span ℚ A))
    (Y : TransSeries) (hsupp : Y.support ⊆ A)
    (hamp : ∀ a ∈ JumpSet A, Y.coeff a ≠ 0) (J : ℕ)
    (P : MvPolynomial (Fin J) (Polynomial ℂ))
    (hP : MvPolynomial.aeval (fun j : Fin J ↦ transDerivX^[j.val] Y)
      (MvPolynomial.map polyToAsymp P) = 0) :
    P = 0 := by
  have hind := jumpPoint_transseries_algebraicIndependent hpos hA hinf Y hsupp hamp J
  have hmap0 : MvPolynomial.map polyToAsymp P = 0 :=
    algebraicIndependent_iff.mp hind (MvPolynomial.map polyToAsymp P) hP
  exact MvPolynomial.map_injective polyToAsymp polyToAsymp_injective
    (hmap0.trans (map_zero _).symm)

/-! ### 4. Universal Wulff-Ray Infinite `ℚ`-Rank, Constructive Multiplicity & Master Theorems -/

/-- The shortest dual Wulff ray action spectrum `{c₀ · n^{d/(d-1)} : n ≥ 1}` for any
degree `d ≥ 3` and ANY positive real scale `c₀ > 0` (zero rationality assumption!). -/
def wulffRayActions (d : ℕ) (c₀ : ℝ) : Set ℝ :=
  {x : ℝ | ∃ n : ℕ, 1 ≤ n ∧ x = c₀ * rAction d n}

theorem rAction_pos {d n : ℕ} (hn : 1 ≤ n) : 0 < rAction d n := by
  unfold rAction
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact Real.rpow_pos_of_pos hn_pos _

theorem nat_le_rAction {d : ℕ} (hd : 3 ≤ d) (n : ℕ) : (n : ℝ) ≤ rAction d n := by
  by_cases hn : n = 0
  · subst hn
    have hpos : (0 : ℝ) < (d : ℝ) / ((d - 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
      have : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
      positivity
    simp [rAction, Real.zero_rpow hpos.ne']
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
    have hexp : (1 : ℝ) ≤ (d : ℝ) / ((d - 1 : ℕ) : ℝ) := by
      have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
      rw [le_div_iff₀ hr_pos, one_mul]
      exact_mod_cast (show d - 1 ≤ d by omega)
    simpa [rAction] using Real.rpow_le_rpow_of_exponent_le hn1 hexp

theorem wulffRay_pos {d : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∀ a ∈ wulffRayActions d c₀, 0 < a := by
  rintro _ ⟨n, hn, rfl⟩
  exact mul_pos hc₀ (rAction_pos hn)

theorem wulffRay_locallyFinite {d : ℕ} (hd : 3 ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∀ B : ℝ, (wulffRayActions d c₀ ∩ Set.Iic B).Finite := by
  intro B
  let N : ℕ := Nat.ceil (max 0 (B / c₀))
  have hsub : wulffRayActions d c₀ ∩ Set.Iic B ⊆
      (fun n : ℕ ↦ c₀ * rAction d n) '' (Finset.Iic N : Set ℕ) := by
    rintro x ⟨⟨n, _, rfl⟩, hxB⟩
    refine ⟨n, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_Iic]
    have hxB' : c₀ * rAction d n ≤ B := Set.mem_Iic.mp hxB
    have h1 : (n : ℝ) ≤ rAction d n := nat_le_rAction hd n
    have h2 : rAction d n ≤ B / c₀ := (le_div_iff₀ hc₀).mpr (by linarith)
    have h3 : (n : ℝ) ≤ max 0 (B / c₀) := (h1.trans h2).trans (le_max_right _ _)
    exact_mod_cast h3.trans (Nat.le_ceil _)
  exact ((Finset.finite_toSet (Finset.Iic N)).image _).subset hsub

theorem wulffRay_isWF {d : ℕ} (hd : 3 ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    (wulffRayActions d c₀).IsWF :=
  isWF_of_locallyFinite (wulffRay_locallyFinite hd hc₀)

/-- **Unconditional Infinite `ℚ`-Rank of Any Dual Wulff Ray (`wulffRay_infinite_qrank`)**:
For EVERY integer `d ≥ 3` (in particular every even degree `d ≥ 4`) and EVERY positive real
Wulff scale `c₀ > 0` (no rationality assumption!), `{c₀ · n^{d/(d-1)} : n ≥ 1}` spans an
infinite-dimensional `ℚ`-subspace of `ℝ`, proved directly from `BesicovitchCore`. -/
theorem wulffRay_infinite_qrank {d : ℕ} (hd : 3 ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ¬ Module.Finite ℚ (Submodule.span ℚ (wulffRayActions d c₀)) := by
  intro hfin
  -- Embed every prime `p_k = Nat.nth Nat.Prime k` into `Core (d - 1)`.
  let pCore : ℕ → Core (d - 1) := fun k ↦
    ⟨Nat.nth Nat.Prime k,
      rfree_of_prime (by omega) (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime k)⟩
  have hpCore_inj : Function.Injective pCore := fun i j h ↦
    (Nat.nth_injective Nat.infinite_setOfPred_prime) (congrArg Subtype.val h)
  -- The scaled prime actions `c₀ · p_k^{d/(d-1)}` are `ℚ`-linearly independent in `ℝ`.
  have hbase : LinearIndependent ℚ (fun b : Core (d - 1) ↦ c₀ * rAction d b.val) := by
    have h0 := rAction_linearIndependent d hd
    rw [linearIndependent_iff'] at h0 ⊢
    intro s c hsum b hb
    have hsum' : ∑ i ∈ s, c i • rAction d i.val = 0 := by
      have hmul : c₀ * (∑ i ∈ s, c i • rAction d i.val) = 0 := by
        rw [Finset.mul_sum]
        refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans hsum
        rw [Rat.smul_def, Rat.smul_def]
        ring
      exact (mul_eq_zero.mp hmul).resolve_left hc₀.ne'
    exact h0 s c hsum' b hb
  have hprime_lin : LinearIndependent ℚ (fun k : ℕ ↦ c₀ * rAction d (pCore k).val) :=
    hbase.comp pCore hpCore_inj
  -- Lift into the allegedly finite-dimensional subspace `Submodule.span ℚ (wulffRayActions d c₀)`.
  let liftVal : ℕ → Submodule.span ℚ (wulffRayActions d c₀) := fun k ↦
    ⟨c₀ * rAction d (pCore k).val, Submodule.subset_span
      ⟨(pCore k).val, rfree_pos (pCore k).property, rfl⟩⟩
  have hlift_lin : LinearIndependent ℚ liftVal :=
    LinearIndependent.of_comp (Submodule.span ℚ (wulffRayActions d c₀)).subtype hprime_lin
  have : Finite ℕ := hlift_lin.finite
  exact not_finite ℕ

/-- Any discrete superspectrum `A ⊇ wulffRayActions d c₀` automatically has infinite `ℚ`-rank! -/
theorem superspectrum_infinite_qrank {d : ℕ} (hd : 3 ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀)
    {A : Set ℝ} (hsub : wulffRayActions d c₀ ⊆ A) :
    ¬ Module.Finite ℚ (Submodule.span ℚ A) := by
  intro hfin
  have hle : Submodule.span ℚ (wulffRayActions d c₀) ≤ Submodule.span ℚ A :=
    Submodule.span_mono hsub
  have : Module.Finite ℚ (Submodule.span ℚ A) := hfin
  have : Module.Finite ℚ (Submodule.span ℚ (wulffRayActions d c₀)) :=
    Module.Finite.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  exact wulffRay_infinite_qrank hd hc₀ inferInstance

/-- **Constructive Positive-Hessian Shell Multiplicity**: whenever a finite nonempty Wulff
shell `S` has strictly positive Hessian weights `w k > 0` and a common saddle phase
`exp(i θ)` (such as `θ = -m (d - 2) π / (4 (d - 1))` for uniformly strictly convex forms),
the total `s = 1` shell amplitude is strictly nonzero — even under arbitrary shell symmetry! -/
theorem constructive_shell_amplitude_ne_zero {α : Type*} (S : Finset α) (hS : S.Nonempty)
    (w : α → ℝ) (hw : ∀ k ∈ S, 0 < w k) (θ : ℝ) :
    (∑ k ∈ S, ((w k : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ≠ 0 := by
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Finset.sum_pos hw hS).ne')
    (Complex.exp_ne_zero _)

/-- **Master Exponential Theorem (`multivariate_evenForm_algebraic_dtrans`)**:
For ANY degree `d ≥ 3` (in particular every even `d ≥ 4`), ANY positive real Wulff scale
`c₀ > 0`, ANY well-ordered action superspectrum `A ⊇ wulffRayActions d c₀`, and ANY formal
exponential series `Y : HahnSeries ℝ ℂ` supported on `A` with nonzero jump-point amplitudes,
for EVERY order `J : ℕ`, the jet `(Y, ∂_X Y, …, ∂_X^{J-1} Y)` is **algebraically independent
over `ℂ`** (no nontrivial autonomous polynomial ADE of any order or degree). -/
theorem multivariate_evenForm_algebraic_dtrans {d : ℕ} (hd : 3 ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀)
    {A : Set ℝ} (hA : A.IsWF) (hsub : wulffRayActions d c₀ ⊆ A)
    (Y : HahnSeries ℝ ℂ) (hsupp : Y.support ⊆ A)
    (hamp : ∀ a ∈ JumpSet A, Y.coeff a ≠ 0) (J : ℕ) :
    AlgebraicIndependent ℂ (fun j : Fin J ↦ expDeriv^[j.val] Y) :=
  jumpPoint_minimal_relation_vandermonde Function.injective_id
    (fun _ hx ↦ mem_nonZeroDivisors_of_ne_zero (Complex.ofReal_ne_zero.mpr hx))
    hA (superspectrum_infinite_qrank hd hc₀ hsub) Y hsupp
    (fun a ha ↦ mem_nonZeroDivisors_of_ne_zero (hamp a ha)) J

/-- **Master Transseries Theorem (`multivariate_jumpPoint_non_ade`)**:
For ANY degree `d ≥ 3` (in particular every even `d ≥ 4`), ANY positive real Wulff scale
`c₀ > 0` (arbitrary real coefficients — zero rationality assumption!), ANY well-ordered
positive action superspectrum `A ⊇ wulffRayActions d c₀`, and ANY formal transseries
`Y : TransSeries` supported on `A` with nonzero jump-point asymptotic amplitudes
`c_a(X) ≠ 0`, for EVERY order `J : ℕ`, the `X`-derivative jet `(Y, D_X Y, …, D_X^{J-1} Y)`
is **algebraically independent over the full asymptotic coefficient ring `AsympCoeff`**! -/
theorem multivariate_jumpPoint_non_ade {d : ℕ} (hd : 3 ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀)
    {A : Set ℝ} (hpos : ∀ a ∈ A, 0 < a) (hA : A.IsWF) (hsub : wulffRayActions d c₀ ⊆ A)
    (Y : TransSeries) (hsupp : Y.support ⊆ A)
    (hamp : ∀ a ∈ JumpSet A, Y.coeff a ≠ 0) (J : ℕ) :
    AlgebraicIndependent AsympCoeff (fun j : Fin J ↦ transDerivX^[j.val] Y) :=
  jumpPoint_transseries_algebraicIndependent hpos hA
    (superspectrum_infinite_qrank hd hc₀ hsub) Y hsupp hamp J

/-- **Master Non-Autonomous Polynomial-ADE Corollary**: under the exact hypotheses of
`multivariate_jumpPoint_non_ade`, `Y` satisfies NO nontrivial polynomial ADE
`P(X, Y, D_X Y, …, D_X^{J-1} Y) = 0` over `ℂ[X]` of any order or degree! -/
theorem multivariate_jumpPoint_non_ade_over_poly {d : ℕ} (hd : 3 ≤ d) {c₀ : ℝ} (hc₀ : 0 < c₀)
    {A : Set ℝ} (hpos : ∀ a ∈ A, 0 < a) (hA : A.IsWF) (hsub : wulffRayActions d c₀ ⊆ A)
    (Y : TransSeries) (hsupp : Y.support ⊆ A)
    (hamp : ∀ a ∈ JumpSet A, Y.coeff a ≠ 0) (J : ℕ)
    (P : MvPolynomial (Fin J) (Polynomial ℂ))
    (hP : MvPolynomial.aeval (fun j : Fin J ↦ transDerivX^[j.val] Y)
      (MvPolynomial.map polyToAsymp P) = 0) :
    P = 0 :=
  jumpPoint_transseries_no_poly_ade hpos hA
    (superspectrum_infinite_qrank hd hc₀ hsub) Y hsupp hamp J P hP

/-! ### 5. Concrete Unconditional Non-Vacuity Witness: `m`-Dimensional Diagonal Forms (`d ≥ 3`) -/

/-- Exact dual action of a lattice vector `k ∈ ℤ^m` for the `m`-dimensional diagonal form
`F(x) = ∑_{r=1}^m x_r^d`: `∑_{r=1}^m |k_r|^{d/(d-1)}`. -/
def diagFormAction (m d : ℕ) (k : Fin m → ℤ) : ℝ :=
  ∑ r : Fin m, rAction d (k r).natAbs

/-- Full discrete positive dual action spectrum `𝒜_{m,d} = {∑ |k_r|^{d/(d-1)} : k ∈ ℤ^m \ {0}}`. -/
def diagFormSpectrum (m d : ℕ) : Set ℝ :=
  {x : ℝ | ∃ k : Fin m → ℤ, k ≠ 0 ∧ x = diagFormAction m d k}

theorem diagFormSpectrum_pos {m d : ℕ} :
    ∀ a ∈ diagFormSpectrum m d, 0 < a := by
  rintro _ ⟨k, hk, rfl⟩
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : Fin m, k r₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hk (funext hall)
  have hr₀_pos : 0 < rAction d (k r₀).natAbs :=
    rAction_pos (Int.natAbs_pos.mpr hr₀)
  have hnonneg : ∀ r : Fin m, 0 ≤ rAction d (k r).natAbs := fun r ↦ by
    unfold rAction
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hle : rAction d (k r₀).natAbs ≤ ∑ r : Fin m, rAction d (k r).natAbs :=
    Finset.single_le_sum (fun r _ ↦ hnonneg r) (Finset.mem_univ r₀)
  exact lt_of_lt_of_le hr₀_pos hle

theorem diagFormSpectrum_locallyFinite {m d : ℕ} (hd : 3 ≤ d) :
    ∀ B : ℝ, (diagFormSpectrum m d ∩ Set.Iic B).Finite := by
  intro B
  let N : ℕ := Nat.ceil (max 0 B)
  let box : Finset (Fin m → ℤ) := Fintype.piFinset fun _ : Fin m ↦ Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hsub : diagFormSpectrum m d ∩ Set.Iic B ⊆
      (diagFormAction m d) '' (box : Set (Fin m → ℤ)) := by
    rintro x ⟨⟨k, _, rfl⟩, hxB⟩
    refine ⟨k, ?_, rfl⟩
    simp only [Finset.mem_coe, box, Fintype.mem_piFinset, Finset.mem_Icc]
    intro r
    have hnonneg : ∀ t : Fin m, 0 ≤ rAction d (k t).natAbs := fun t ↦ by
      unfold rAction; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hcoord : ((k r).natAbs : ℝ) ≤ B := by
      calc ((k r).natAbs : ℝ)
          ≤ rAction d (k r).natAbs := nat_le_rAction hd _
        _ ≤ ∑ t : Fin m, rAction d (k t).natAbs :=
            Finset.single_le_sum (fun t _ ↦ hnonneg t) (Finset.mem_univ r)
        _ ≤ B := hxB
    have habs : (k r).natAbs ≤ N := by
      exact_mod_cast (hcoord.trans (le_max_right 0 B)).trans (Nat.le_ceil _)
    have habsZ : |k r| ≤ (N : ℤ) := by
      rw [← Int.natCast_natAbs]; exact_mod_cast habs
    exact abs_le.mp habsZ
  exact ((Finset.finite_toSet box).image _).subset hsub

theorem wulffRay_subset_diagFormSpectrum {m d : ℕ} (hm : 1 ≤ m) (hd : 3 ≤ d) :
    wulffRayActions d 1 ⊆ diagFormSpectrum m d := by
  classical
  rintro _ ⟨n, hn, rfl⟩
  let r₀ : Fin m := ⟨0, by omega⟩
  let k : Fin m → ℤ := Pi.single r₀ (n : ℤ)
  have hk_ne : k ≠ 0 := by
    intro h0
    have hval := congrFun h0 r₀
    simp only [k, Pi.single_eq_same, Pi.zero_apply, Nat.cast_eq_zero] at hval
    omega
  refine ⟨k, hk_ne, ?_⟩
  rw [one_mul, diagFormAction]
  have hzero_act : rAction d 0 = 0 := by
    have hpos : (0 : ℝ) < (d : ℝ) / ((d - 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
      have : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
      positivity
    simp [rAction, Real.zero_rpow hpos.ne']
  rw [Finset.sum_eq_single r₀]
  · simp [k]
  · intro r _ hr
    simp [k, Pi.single_eq_of_ne hr, hzero_act]
  · intro hnot; exact absurd (Finset.mem_univ r₀) hnot

/-- Explicit demonstration that the 2D quartic spectrum `diagFormSpectrum 2 4` genuinely
contains exact `s = 2` off-ray additive collisions (`F*(1,0) + F*(0,1) = 1 + 1 = 2 = F*(1,1)`),
which the Jump-Point Derivation Engine automatically bypasses! -/
theorem diagQuartic2D_offray_collision :
    (1 : ℝ) ∈ diagFormSpectrum 2 4 ∧
    (2 : ℝ) ∈ diagFormSpectrum 2 4 ∧
    (1 : ℝ) + 1 = 2 := by
  have h1 : rAction 4 1 = 1 := by simp [rAction]
  have h0 : rAction 4 0 = 0 := by
    have hexp : ((4 : ℕ) : ℝ) / ((4 - 1 : ℕ) : ℝ) ≠ 0 := by norm_num
    rw [rAction, Nat.cast_zero, Real.zero_rpow hexp]
  refine ⟨?_, ?_, by norm_num⟩
  · refine ⟨![1, 0], fun h ↦ by simpa using congrFun h 0, ?_⟩
    simp [diagFormAction, Fin.sum_univ_two, h1, h0]
  · refine ⟨![1, 1], fun h ↦ by simpa using congrFun h 0, ?_⟩
    simp only [diagFormAction, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Int.natAbs_one, h1]
    norm_num

/-- Finite shell of lattice vectors `k ∈ ℤ^m \ {0}` achieving a given action `a ∈ ℝ`. -/
def diagFormShell (m d : ℕ) (a : ℝ) : Finset (Fin m → ℤ) := by
  classical
  let N : ℕ := Nat.ceil (max 0 a)
  let box : Finset (Fin m → ℤ) := Fintype.piFinset fun _ : Fin m ↦ Finset.Icc (-(N : ℤ)) (N : ℤ)
  exact box.filter fun k ↦ k ≠ 0 ∧ diagFormAction m d k = a

theorem diagFormShell_nonempty {m d : ℕ} (hd : 3 ≤ d) {a : ℝ}
    (ha : a ∈ diagFormSpectrum m d) :
    (diagFormShell m d a).Nonempty := by
  classical
  obtain ⟨k, hk, rfl⟩ := ha
  refine ⟨k, ?_⟩
  simp only [diagFormShell, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun r ↦ ?_, hk, trivial⟩
  have hnonneg : ∀ t : Fin m, 0 ≤ rAction d (k t).natAbs := fun t ↦ by
    unfold rAction; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hcoord : ((k r).natAbs : ℝ) ≤ diagFormAction m d k :=
    (nat_le_rAction hd _).trans
      (Finset.single_le_sum (fun t _ ↦ hnonneg t) (Finset.mem_univ r))
  have habs : (k r).natAbs ≤ Nat.ceil (max 0 (diagFormAction m d k)) := by
    exact_mod_cast (hcoord.trans (le_max_right 0 _)).trans (Nat.le_ceil _)
  have habsZ : |k r| ≤ (Nat.ceil (max 0 (diagFormAction m d k)) : ℤ) := by
    rw [← Int.natCast_natAbs]; exact_mod_cast habs
  exact abs_le.mp habsZ

/-- Universal saddle phase `θ(m, d) = -m (d - 2) π / (4 (d - 1))` of a strictly convex
`m`-dimensional degree-`d` homogeneous form. -/
def multivariateSaddlePhase (m d : ℕ) : ℝ :=
  -((m : ℝ) * ((d - 2 : ℕ) : ℝ) * Real.pi) / (4 * ((d - 1 : ℕ) : ℝ))

/-- Constructive shell amplitude `∑_{k ∈ S(a)} 1 · exp(i θ(m, d))` for the `m`-dimensional
diagonal degree-`d` witness. -/
def diagFormCoeff (m d : ℕ) (a : ℝ) : ℂ :=
  ∑ _k ∈ diagFormShell m d a,
    ((1 : ℝ) : ℂ) * Complex.exp (Complex.I * (multivariateSaddlePhase m d : ℂ))

theorem diagFormCoeff_ne_zero {m d : ℕ} (hd : 3 ≤ d) {a : ℝ}
    (ha : a ∈ diagFormSpectrum m d) :
    diagFormCoeff m d a ≠ 0 :=
  constructive_shell_amplitude_ne_zero (diagFormShell m d a)
    (diagFormShell_nonempty hd ha) (fun _ ↦ 1) (fun _ _ ↦ zero_lt_one)
    (multivariateSaddlePhase m d)

theorem diagFormCoeff_eq_zero_of_notMem {m d : ℕ} {a : ℝ}
    (ha : a ∉ diagFormSpectrum m d) :
    diagFormCoeff m d a = 0 := by
  classical
  have hemp : diagFormShell m d a = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro k hk
    simp only [diagFormShell, Finset.mem_filter] at hk
    exact ha ⟨k, hk.2.1, hk.2.2.symm⟩
  simp [diagFormCoeff, hemp]

/-- Concrete formal exponential series witness `∑_{a ∈ 𝒜_{m,d}} c(a) e^{-a X}` in
`HahnSeries ℝ ℂ`. -/
def diagFormSeries (m d : ℕ) (hd : 3 ≤ d) : HahnSeries ℝ ℂ where
  coeff a := diagFormCoeff m d a
  isPWO_support' := (isPWO_of_locallyFinite (diagFormSpectrum_locallyFinite (m := m) hd)).mono
    fun a ha ↦ by
      by_contra hnot
      exact ha (diagFormCoeff_eq_zero_of_notMem hnot)

/-- Concrete formal transseries witness `∑_{a ∈ 𝒜_{m,d}} c(a) X^{m/2} e^{-a X}` in
`TransSeries = HahnSeries ℝ (HahnSeries ℝ ℂ)`. -/
def diagFormTransSeries (m d : ℕ) (hd : 3 ≤ d) : TransSeries where
  coeff a := HahnSeries.single (-((m : ℝ) / 2)) (diagFormCoeff m d a)
  isPWO_support' := (isPWO_of_locallyFinite (diagFormSpectrum_locallyFinite (m := m) hd)).mono
    fun a ha ↦ by
      by_contra hnot
      apply ha
      simp [diagFormCoeff_eq_zero_of_notMem hnot]

/-- **Unconditional Non-Vacuity Theorem (Pure Exponential)**: for EVERY dimension `m ≥ 1`
and EVERY degree `d ≥ 3`, the concrete diagonal-form witness `diagFormSeries m d` has
algebraically independent derivatives of every order `J` over `ℂ`. -/
theorem diagForm_algebraic_dtrans (m d : ℕ) (hm : 1 ≤ m) (hd : 3 ≤ d) (J : ℕ) :
    AlgebraicIndependent ℂ (fun j : Fin J ↦ expDeriv^[j.val] (diagFormSeries m d hd)) := by
  refine multivariate_evenForm_algebraic_dtrans hd zero_lt_one
    (isWF_of_locallyFinite (diagFormSpectrum_locallyFinite hd))
    (wulffRay_subset_diagFormSpectrum hm hd)
    (diagFormSeries m d hd)
    (fun a ha ↦ by
      by_contra hnot
      exact ha (diagFormCoeff_eq_zero_of_notMem hnot))
    (fun a ha ↦ diagFormCoeff_ne_zero hd ha.1) J

/-- **Unconditional Non-Vacuity Theorem (Full Transseries over `AsympCoeff` & `ℂ[X]`)**:
for EVERY dimension `m ≥ 1` and EVERY degree `d ≥ 3`, the concrete multivariate witness
`diagFormTransSeries m d` with exact saddle prefactor `X^{m/2}` is differentially
transcendental over `AsympCoeff` (and hence over `ℂ[X]`). -/
theorem diagForm_transseries_non_ade (m d : ℕ) (hm : 1 ≤ m) (hd : 3 ≤ d) (J : ℕ) :
    AlgebraicIndependent AsympCoeff
      (fun j : Fin J ↦ transDerivX^[j.val] (diagFormTransSeries m d hd)) := by
  refine multivariate_jumpPoint_non_ade hd zero_lt_one
    diagFormSpectrum_pos
    (isWF_of_locallyFinite (diagFormSpectrum_locallyFinite hd))
    (wulffRay_subset_diagFormSpectrum hm hd)
    (diagFormTransSeries m d hd)
    (fun a ha ↦ by
      by_contra hnot
      apply ha
      simp [diagFormTransSeries, diagFormCoeff_eq_zero_of_notMem hnot])
    (fun a ha ↦ HahnSeries.single_ne_zero (diagFormCoeff_ne_zero hd ha.1)) J

/-- **Unconditional 2D Quartic Witness (`m = 2, d = 4`)**: despite genuine `s = 2` off-ray
collisions (`diagQuartic2D_offray_collision`), `diagFormTransSeries 2 4` satisfies NO
nontrivial polynomial ADE over `ℂ[X]` of any order or degree! -/
theorem diagQuartic2D_non_ade (J : ℕ) (P : MvPolynomial (Fin J) (Polynomial ℂ))
    (hP : MvPolynomial.aeval (fun j : Fin J ↦ transDerivX^[j.val] (diagFormTransSeries 2 4 (by decide)))
      (MvPolynomial.map polyToAsymp P) = 0) :
    P = 0 := by
  have hind := diagForm_transseries_non_ade 2 4 (by decide) (by decide) J
  have hmap0 : MvPolynomial.map polyToAsymp P = 0 :=
    algebraicIndependent_iff.mp hind (MvPolynomial.map polyToAsymp P) hP
  exact MvPolynomial.map_injective polyToAsymp polyToAsymp_injective
    (hmap0.trans (map_zero _).symm)

end
end CubicTheta.AllD
