module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Depth-3 `S₃` Eulerian Idempotents, Cubic Slice-Rank Closedness, and Tao's Diagonal Lower Bound

Unconditional Lean 4 formalization from Mathlib (zero placeholders, standard foundations only)
of the algebraic and multilinear core of the exact depth-3 Stokes classification over `F₂`:

1. **`S₃` Eulerian Idempotents & Exact 3-Sector Decomposition (`6 = 2 + 3 + 1`):**
   - On 3-tensors `Tensor3 K D := Fin D → Fin D → Fin D → K` over any characteristic-zero field
     `K`, defines the three explicit Eulerian projectors `eulerianE1` (`[2, 1]_Lie`),
     `eulerianE2` (`[1, 1, 1] ⊕ [2, 1]_sh`), and `eulerianE3` (`[3]`), proving unconditionally:
     `e1 + e2 + e3 = id`, idempotence `e_i ∘ e_i = e_i`, and all six mutual orthogonalities
     `e_i ∘ e_j = 0` (`i ≠ j`).
   - Proves the exact faithful invariants `lieInvariant L(P)`, `mixedBilinear B(P)`, inverse
     reconstructions, and the `(1, 2)`-shuffle tensor identities `L(μ_{1,2}) = 0`,
     `B(μ_{1,2}(u, M))_{a;bc} = 2 u_a A_{bc}`, and `e3(μ_{1,2}(u, M)) = μ_{1,2}(u, M^{sym})`.
   - On the group-algebra module `S3Algebra K := Equiv.Perm (Fin 3) → K` (and `ℚ[S₃]`), defines
     `eulerianRegE1`, `eulerianRegE2`, `eulerianRegE3`, proves resolution of identity,
     idempotence, mutual orthogonality, and exact image dimensions `2, 3, 1` (`6 = 2 + 3 + 1`).
   - On the free shuffle algebra of words `FreeWordSpace K α := List α →₀ K`, defines the
     recursive shuffle product `shuffleMul` and proves the exact depth-3 shuffle identities:
     * `w_a ⧢ (w_{bc} - w_{cb}) + w_c ⧢ (w_{ab} - w_{ba}) = 2 (w_{abc} - w_{cba})`,
     * `w_{abc} - w_{cba} = w_a ⧢ K_{bc} + w_c ⧢ K_{ab}` with `K_{bc} = (1/2)(w_{bc} - w_{cb})`,
     * `∑_{π ∈ S₃} sgn(π) w_{π(a,b,c)} = 2 (w_a ⧢ K_{bc} - w_b ⧢ K_{ac} + w_c ⧢ K_{ab})`,
     * and the exact `e2`-period pairing `V_{P^(2)} = (1/2) ∑ B(P)_{a;bc} J_a K_{bc}`.
2. **Exact Cubic Slice-Rank = Vanishing on Codimension-`N` Subspace Equivalence
   (`HasCubicSliceRankLe`, `VanishesOnCodimLe`, `cubic_sliceRank_le_iff_vanishes_on_codim_subspace`,
   `symTensor_cubic_sliceRank_le_iff_vanishes_on_codim_subspace`):**
   Over any characteristic-zero field `K`, proves that a homogeneous cubic polynomial `f` on
   `K^D` admits a decomposition `∑_{i : Fin N} ℓ_i · q_i` (linear forms `ℓ_i`, quadratic forms
   `q_i`) if and only if there exists a linear subspace `W ≤ K^D` of codimension `≤ N` on which
   `f` vanishes identically (explaining why depth-3 cubic slice rank is Zariski closed via
   Grassmannian elimination).
3. **Tao's Diagonal Cubic Slice-Rank Lower Bound (`exists_mem_support_ge_finrank`,
   `tao_diagonal_cubic_sliceRank_lower_bound`, `tao_diagonal_cubic_sliceRank_exact`,
   `diag_cubic_symSliceRank_lower_bound`, `vCube_jet_poly_symSliceRank_lower_bound`):**
   - Proves over ANY field `K` that any diagonal 3-tensor `T(i, j, k) = if i = j ∧ j = k then c_i else 0`
     (`c_i ≠ 0`) on `Fin D` has slice rank **exact `D`**: every 3-mode slice decomposition
     satisfies `N₁ + N₂ + N₃ ≥ D`, attained with `N₁ = D, N₂ = N₃ = 0`.
   - Polarizing `∑_r ℓ_r(x) q_r(x)` into `3 N` slices proves `3 * N ≥ D` (i.e., `N ≥ (D + 2) / 3`)
     for diagonal cubics `∑ c_i X_i^3`, and `3 * N ≥ D - deg p` for jet-weighted diagonal cubics
     `∑ p(3(i + 1)) c_i X_i^3`, establishing the unbounded symmetric slice-rank obstruction for
     `V_cube = (1/6) ∑ e^{-3n} J_n^3`.
-/

public section

namespace CubicTheta.AllD

open Set Finset Matrix MvPolynomial Polynomial
open scoped BigOperators Classical

noncomputable section

/-! ### 1. `S₃` Eulerian Idempotents, Regular Dimensions `6 = 2 + 3 + 1`, and Depth-3 Shuffle Algebra -/

section EulerianIdempotents

/-- Space of 3-tensors `Fin D → Fin D → Fin D → K`. -/
abbrev Tensor3 (K : Type*) (D : ℕ) := Fin D → Fin D → Fin D → K

/-- First Eulerian projector `e₁` (Lie sector `[2, 1]_Lie`, dim 2 on `K[S₃]`):
`(e₁ P)_{abc} = (1/3)(P_{abc} + P_{cba}) - (1/6)(P_{bac} + P_{acb} + P_{bca} + P_{cab})`. -/
def eulerianE1 (K : Type*) [Field K] (D : ℕ) : Module.End K (Tensor3 K D) where
  toFun P a b c :=
    (3⁻¹ : K) * (P a b c + P c b a) -
      (6⁻¹ : K) * (P b a c + P a c b + P b c a + P c a b)
  map_add' P Q := by funext a b c; simp only [Pi.add_apply]; ring
  map_smul' r P := by funext a b c; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Second Eulerian projector `e₂` (mixed sector `[1, 1, 1] ⊕ [2, 1]_sh`, dim 3 on `K[S₃]`):
`(e₂ P)_{abc} = (1/2)(P_{abc} - P_{cba})`. -/
def eulerianE2 (K : Type*) [Field K] (D : ℕ) : Module.End K (Tensor3 K D) where
  toFun P a b c := (2⁻¹ : K) * (P a b c - P c b a)
  map_add' P Q := by funext a b c; simp only [Pi.add_apply]; ring
  map_smul' r P := by funext a b c; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Third Eulerian projector `e₃` (totally symmetric sector `[3]`, dim 1 on `K[S₃]`):
`(e₃ P)_{abc} = (1/6)(P_{abc} + P_{acb} + P_{bac} + P_{bca} + P_{cab} + P_{cba})`. -/
def eulerianE3 (K : Type*) [Field K] (D : ℕ) : Module.End K (Tensor3 K D) where
  toFun P a b c := (6⁻¹ : K) * (P a b c + P a c b + P b a c + P b c a + P c a b + P c b a)
  map_add' P Q := by funext a b c; simp only [Pi.add_apply]; ring
  map_smul' r P := by funext a b c; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Exact resolution of the identity `e₁ + e₂ + e₃ = id` on 3-tensors over any `CharZero` field. -/
theorem eulerian_sum_eq_id (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    eulerianE1 K D + eulerianE2 K D + eulerianE3 K D = LinearMap.id := by
  apply LinearMap.ext; intro P; funext a b c
  simp only [LinearMap.add_apply, LinearMap.id_apply, Pi.add_apply,
    eulerianE1, eulerianE2, eulerianE3, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem eulerianE1_idem (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    (eulerianE1 K D).comp (eulerianE1 K D) = eulerianE1 K D := by
  apply LinearMap.ext; intro P; funext a b c
  simp only [LinearMap.comp_apply, eulerianE1, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem eulerianE2_idem (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    (eulerianE2 K D).comp (eulerianE2 K D) = eulerianE2 K D := by
  apply LinearMap.ext; intro P; funext a b c
  simp only [LinearMap.comp_apply, eulerianE2, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem eulerianE3_idem (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    (eulerianE3 K D).comp (eulerianE3 K D) = eulerianE3 K D := by
  apply LinearMap.ext; intro P; funext a b c
  simp only [LinearMap.comp_apply, eulerianE3, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem eulerianE1_comp_E2 (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    (eulerianE1 K D).comp (eulerianE2 K D) = 0 := by
  apply LinearMap.ext; intro P; funext a b c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianE1, eulerianE2, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem eulerianE2_comp_E1 (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    (eulerianE2 K D).comp (eulerianE1 K D) = 0 := by
  apply LinearMap.ext; intro P; funext a b c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianE1, eulerianE2, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem eulerianE1_comp_E3 (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    (eulerianE1 K D).comp (eulerianE3 K D) = 0 := by
  apply LinearMap.ext; intro P; funext a b c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianE1, eulerianE3, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem eulerianE3_comp_E1 (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    (eulerianE3 K D).comp (eulerianE1 K D) = 0 := by
  apply LinearMap.ext; intro P; funext a b c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianE1, eulerianE3, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem eulerianE2_comp_E3 (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    (eulerianE2 K D).comp (eulerianE3 K D) = 0 := by
  apply LinearMap.ext; intro P; funext a b c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianE2, eulerianE3, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem eulerianE3_comp_E2 (K : Type*) [Field K] [CharZero K] (D : ℕ) :
    (eulerianE3 K D).comp (eulerianE2 K D) = 0 := by
  apply LinearMap.ext; intro P; funext a b c
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianE2, eulerianE3, LinearMap.coe_mk, AddHom.coe_mk]
  ring

/-- Faithful Lie invariant `L(P)_{abc} = P_{abc} - P_{bac} - P_{cab} + P_{cba}` for sector `e₁`. -/
def lieInvariant {K : Type*} [CommRing K] {D : ℕ} (P : Tensor3 K D) : Tensor3 K D :=
  fun a b c => P a b c - P b a c - P c a b + P c b a

/-- Faithful mixed bilinear invariant `B(P)_{a;bc} = (1/2)(P_{abc} + P_{bca} - P_{acb} - P_{cba})`
for sector `e₂` (antisymmetric in `(b, c)`). -/
def mixedBilinear {K : Type*} [Field K] {D : ℕ} (P : Tensor3 K D) : Tensor3 K D :=
  fun a b c => (2⁻¹ : K) * (P a b c + P b c a - P a c b - P c b a)

theorem mixedBilinear_skew {K : Type*} [Field K] {D : ℕ} (P : Tensor3 K D) (a b c : Fin D) :
    mixedBilinear P a c b = -mixedBilinear P a b c := by
  unfold mixedBilinear; ring

theorem eulerianE1_eq_lieInvariant {K : Type*} [Field K] [CharZero K] {D : ℕ}
    (P : Tensor3 K D) (a b c : Fin D) :
    eulerianE1 K D P a b c = (6⁻¹ : K) * (lieInvariant P a b c + lieInvariant P c b a) := by
  simp only [eulerianE1, lieInvariant, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem lieInvariant_eulerianE1 {K : Type*} [Field K] [CharZero K] {D : ℕ} (P : Tensor3 K D) :
    lieInvariant (eulerianE1 K D P) = lieInvariant P := by
  funext a b c
  simp only [lieInvariant, eulerianE1, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem lieInvariant_eq_zero_iff_eulerianE1_eq_zero {K : Type*} [Field K] [CharZero K] {D : ℕ}
    (P : Tensor3 K D) : lieInvariant P = 0 ↔ eulerianE1 K D P = 0 := by
  constructor
  · intro h
    funext a b c
    rw [eulerianE1_eq_lieInvariant, h]
    simp
  · intro h
    rw [← lieInvariant_eulerianE1 P, h]
    funext a b c; simp [lieInvariant]

theorem eulerianE2_eq_mixedBilinear {K : Type*} [Field K] [CharZero K] {D : ℕ}
    (P : Tensor3 K D) (a b c : Fin D) :
    eulerianE2 K D P a b c =
      (2⁻¹ : K) * (mixedBilinear P a b c - mixedBilinear P b c a + mixedBilinear P c a b) := by
  simp only [eulerianE2, mixedBilinear, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem mixedBilinear_eulerianE2 {K : Type*} [Field K] [CharZero K] {D : ℕ} (P : Tensor3 K D) :
    mixedBilinear (eulerianE2 K D P) = mixedBilinear P := by
  funext a b c
  simp only [mixedBilinear, eulerianE2, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem mixedBilinear_eq_zero_iff_eulerianE2_eq_zero {K : Type*} [Field K] [CharZero K] {D : ℕ}
    (P : Tensor3 K D) : mixedBilinear P = 0 ↔ eulerianE2 K D P = 0 := by
  constructor
  · intro h
    funext a b c
    rw [eulerianE2_eq_mixedBilinear, h]
    simp
  · intro h
    rw [← mixedBilinear_eulerianE2 P, h]
    funext a b c; simp [mixedBilinear]

/-- The `(1, 2)`-shuffle tensor `μ_{1,2}(u, M)_{abc} = u_a M_{bc} + u_b M_{ac} + u_c M_{ab}`
representing the product `V_u · V_M ∈ F₂`. -/
def shuffleTensor12 {K : Type*} [CommRing K] {D : ℕ}
    (u : Fin D → K) (M : Fin D → Fin D → K) : Tensor3 K D :=
  fun a b c => u a * M b c + u b * M a c + u c * M a b

theorem lieInvariant_shuffleTensor12 {K : Type*} [CommRing K] {D : ℕ}
    (u : Fin D → K) (M : Fin D → Fin D → K) :
    lieInvariant (shuffleTensor12 u M) = 0 := by
  funext a b c
  simp only [lieInvariant, shuffleTensor12, Pi.zero_apply]
  ring

theorem eulerianE1_shuffleTensor12 {K : Type*} [Field K] [CharZero K] {D : ℕ}
    (u : Fin D → K) (M : Fin D → Fin D → K) :
    eulerianE1 K D (shuffleTensor12 u M) = 0 :=
  (lieInvariant_eq_zero_iff_eulerianE1_eq_zero _).mp (lieInvariant_shuffleTensor12 u M)

theorem mixedBilinear_shuffleTensor12 {K : Type*} [Field K] [CharZero K] {D : ℕ}
    (u : Fin D → K) (M : Fin D → Fin D → K) (a b c : Fin D) :
    mixedBilinear (shuffleTensor12 u M) a b c =
      2 * u a * ((2⁻¹ : K) * (M b c - M c b)) := by
  simp only [mixedBilinear, shuffleTensor12]
  ring

theorem eulerianE3_shuffleTensor12 {K : Type*} [Field K] [CharZero K] {D : ℕ}
    (u : Fin D → K) (M : Fin D → Fin D → K) :
    eulerianE3 K D (shuffleTensor12 u M) =
      shuffleTensor12 u (fun b c => (2⁻¹ : K) * (M b c + M c b)) := by
  funext a b c
  simp only [eulerianE3, shuffleTensor12, LinearMap.coe_mk, AddHom.coe_mk]
  ring

/-! #### Regular Representation on `K[S₃]` (`Equiv.Perm (Fin 3) → K`) and Exact Dimensions `2, 3, 1` -/

/-- The regular representation module `K[S₃]` modeled as `Equiv.Perm (Fin 3) → K`. -/
abbrev S3Algebra (K : Type*) := Equiv.Perm (Fin 3) → K

/-- The six explicit elements of `S₃ = Equiv.Perm (Fin 3)`. -/
def s3Id : Equiv.Perm (Fin 3) := 1
def s3Rev : Equiv.Perm (Fin 3) := Equiv.swap 0 2
def s3Swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def s3Swap12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
def s3Cyc1 : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
def s3Cyc2 : Equiv.Perm (Fin 3) := Equiv.swap 1 2 * Equiv.swap 0 1

/-- Every element of `Equiv.Perm (Fin 3)` is one of the six explicit permutations. -/
lemma perm_fin3_cases (σ : Equiv.Perm (Fin 3)) :
    σ = s3Id ∨ σ = s3Rev ∨ σ = s3Swap01 ∨ σ = s3Swap12 ∨ σ = s3Cyc1 ∨ σ = s3Cyc2 := by
  revert σ
  decide

/-- First Eulerian projector `e₁` on `K[S₃]` (`Equiv.Perm (Fin 3) → K`, dim 2). -/
def eulerianRegE1 (K : Type*) [Field K] : Module.End K (S3Algebra K) where
  toFun f σ :=
    (3⁻¹ : K) * (f σ + f (σ * s3Rev)) -
      (6⁻¹ : K) * (f (σ * s3Swap01) + f (σ * s3Swap12) + f (σ * s3Cyc1) + f (σ * s3Cyc2))
  map_add' f g := by funext σ; simp only [Pi.add_apply]; ring
  map_smul' r f := by funext σ; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Second Eulerian projector `e₂` on `K[S₃]` (`Equiv.Perm (Fin 3) → K`, dim 3). -/
def eulerianRegE2 (K : Type*) [Field K] : Module.End K (S3Algebra K) where
  toFun f σ := (2⁻¹ : K) * (f σ - f (σ * s3Rev))
  map_add' f g := by funext σ; simp only [Pi.add_apply]; ring
  map_smul' r f := by funext σ; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- Third Eulerian projector `e₃` on `K[S₃]` (`Equiv.Perm (Fin 3) → K`, dim 1). -/
def eulerianRegE3 (K : Type*) [Field K] : Module.End K (S3Algebra K) where
  toFun f σ :=
    (6⁻¹ : K) * (f σ + f (σ * s3Rev) + f (σ * s3Swap01) + f (σ * s3Swap12) +
      f (σ * s3Cyc1) + f (σ * s3Cyc2))
  map_add' f g := by funext σ; simp only [Pi.add_apply]; ring
  map_smul' r f := by funext σ; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private lemma s3_mul_table :
    (s3Rev * s3Rev = s3Id) ∧
    (s3Swap01 * s3Rev = s3Cyc2) ∧ (s3Swap12 * s3Rev = s3Cyc1) ∧
    (s3Cyc1 * s3Rev = s3Swap12) ∧ (s3Cyc2 * s3Rev = s3Swap01) ∧
    (s3Rev * s3Swap01 = s3Cyc1) ∧ (s3Rev * s3Swap12 = s3Cyc2) ∧
    (s3Rev * s3Cyc1 = s3Swap01) ∧ (s3Rev * s3Cyc2 = s3Swap12) ∧
    (s3Swap01 * s3Swap01 = s3Id) ∧ (s3Swap01 * s3Swap12 = s3Cyc1) ∧
    (s3Swap01 * s3Cyc1 = s3Swap12) ∧ (s3Swap01 * s3Cyc2 = s3Rev) ∧
    (s3Swap12 * s3Swap01 = s3Cyc2) ∧ (s3Swap12 * s3Swap12 = s3Id) ∧
    (s3Swap12 * s3Cyc1 = s3Rev) ∧ (s3Swap12 * s3Cyc2 = s3Swap01) ∧
    (s3Cyc1 * s3Swap01 = s3Rev) ∧ (s3Cyc1 * s3Swap12 = s3Swap01) ∧
    (s3Cyc1 * s3Cyc1 = s3Cyc2) ∧ (s3Cyc1 * s3Cyc2 = s3Id) ∧
    (s3Cyc2 * s3Swap01 = s3Swap12) ∧ (s3Cyc2 * s3Swap12 = s3Rev) ∧
    (s3Cyc2 * s3Cyc1 = s3Id) ∧ (s3Cyc2 * s3Cyc2 = s3Cyc1) := by
  decide

private lemma s3_id_mul (σ : Equiv.Perm (Fin 3)) : s3Id * σ = σ := one_mul σ
private lemma s3_mul_id (σ : Equiv.Perm (Fin 3)) : σ * s3Id = σ := mul_one σ

theorem eulerianReg_sum_eq_id (K : Type*) [Field K] [CharZero K] :
    eulerianRegE1 K + eulerianRegE2 K + eulerianRegE3 K = LinearMap.id := by
  apply LinearMap.ext; intro f; funext σ
  simp only [LinearMap.add_apply, LinearMap.id_apply, Pi.add_apply,
    eulerianRegE1, eulerianRegE2, eulerianRegE3, LinearMap.coe_mk, AddHom.coe_mk]
  ring

theorem eulerianRegE1_idem (K : Type*) [Field K] [CharZero K] :
    (eulerianRegE1 K).comp (eulerianRegE1 K) = eulerianRegE1 K := by
  apply LinearMap.ext; intro f; funext σ
  simp only [LinearMap.comp_apply, eulerianRegE1, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  have h := s3_mul_table
  simp only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    s3_mul_id]
  ring

theorem eulerianRegE2_idem (K : Type*) [Field K] [CharZero K] :
    (eulerianRegE2 K).comp (eulerianRegE2 K) = eulerianRegE2 K := by
  apply LinearMap.ext; intro f; funext σ
  simp only [LinearMap.comp_apply, eulerianRegE2, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc,
    s3_mul_table.1, s3_mul_id]
  ring

theorem eulerianRegE3_idem (K : Type*) [Field K] [CharZero K] :
    (eulerianRegE3 K).comp (eulerianRegE3 K) = eulerianRegE3 K := by
  apply LinearMap.ext; intro f; funext σ
  simp only [LinearMap.comp_apply, eulerianRegE3, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  have h := s3_mul_table
  simp only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    s3_mul_id]
  ring

theorem eulerianRegE1_comp_E2 (K : Type*) [Field K] [CharZero K] :
    (eulerianRegE1 K).comp (eulerianRegE2 K) = 0 := by
  apply LinearMap.ext; intro f; funext σ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianRegE1, eulerianRegE2, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  have h := s3_mul_table
  simp only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, s3_mul_id]
  ring

theorem eulerianRegE2_comp_E1 (K : Type*) [Field K] [CharZero K] :
    (eulerianRegE2 K).comp (eulerianRegE1 K) = 0 := by
  apply LinearMap.ext; intro f; funext σ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianRegE1, eulerianRegE2, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  have h := s3_mul_table
  simp only [h.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    s3_mul_id]
  ring

theorem eulerianRegE1_comp_E3 (K : Type*) [Field K] [CharZero K] :
    (eulerianRegE1 K).comp (eulerianRegE3 K) = 0 := by
  apply LinearMap.ext; intro f; funext σ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianRegE1, eulerianRegE3, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  have h := s3_mul_table
  simp only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    s3_mul_id]
  ring

theorem eulerianRegE3_comp_E1 (K : Type*) [Field K] [CharZero K] :
    (eulerianRegE3 K).comp (eulerianRegE1 K) = 0 := by
  apply LinearMap.ext; intro f; funext σ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianRegE1, eulerianRegE3, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  have h := s3_mul_table
  simp only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
    h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
    s3_mul_id]
  ring

theorem eulerianRegE2_comp_E3 (K : Type*) [Field K] [CharZero K] :
    (eulerianRegE2 K).comp (eulerianRegE3 K) = 0 := by
  apply LinearMap.ext; intro f; funext σ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianRegE2, eulerianRegE3, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  have h := s3_mul_table
  simp only [h.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
    s3_mul_id]
  ring

theorem eulerianRegE3_comp_E2 (K : Type*) [Field K] [CharZero K] :
    (eulerianRegE3 K).comp (eulerianRegE2 K) = 0 := by
  apply LinearMap.ext; intro f; funext σ
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply,
    eulerianRegE2, eulerianRegE3, LinearMap.coe_mk, AddHom.coe_mk, mul_assoc]
  have h := s3_mul_table
  simp only [h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, s3_mul_id]
  ring

/-- Helper to prove equality of functions on `Equiv.Perm (Fin 3)` by checking the 6 elements. -/
private lemma funext_perm_fin3 {α : Type*} {f g : Equiv.Perm (Fin 3) → α}
    (h1 : f s3Id = g s3Id) (h2 : f s3Rev = g s3Rev)
    (h3 : f s3Swap01 = g s3Swap01) (h4 : f s3Swap12 = g s3Swap12)
    (h5 : f s3Cyc1 = g s3Cyc1) (h6 : f s3Cyc2 = g s3Cyc2) : f = g := by
  funext σ
  rcases perm_fin3_cases σ with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

/-- Exact image dimension `2` for `eulerianRegE1 K` on `K[S₃]`. -/
theorem eulerianRegE1_finrank (K : Type*) [Field K] [CharZero K] :
    Module.finrank K (LinearMap.range (eulerianRegE1 K)) = 2 := by
  let v0 : S3Algebra K := fun σ =>
    if σ = s3Id ∨ σ = s3Rev then 1 else if σ = s3Swap01 ∨ σ = s3Cyc2 then -1 else 0
  let v1 : S3Algebra K := fun σ =>
    if σ = s3Id ∨ σ = s3Rev then 1 else if σ = s3Swap12 ∨ σ = s3Cyc1 then -1 else 0
  have hv0_vals : v0 s3Id = 1 ∧ v0 s3Rev = 1 ∧ v0 s3Swap01 = -1 ∧
      v0 s3Swap12 = 0 ∧ v0 s3Cyc1 = 0 ∧ v0 s3Cyc2 = -1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [v0]; split_ifs with h1 h2 <;> first | rfl | (exfalso; revert h1; decide) | (exfalso; revert h2; decide))
  have hv1_vals : v1 s3Id = 1 ∧ v1 s3Rev = 1 ∧ v1 s3Swap01 = 0 ∧
      v1 s3Swap12 = -1 ∧ v1 s3Cyc1 = -1 ∧ v1 s3Cyc2 = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [v1]; split_ifs with h1 h2 <;> first | rfl | (exfalso; revert h1; decide) | (exfalso; revert h2; decide))
  have hv0_mem : v0 ∈ LinearMap.range (eulerianRegE1 K) := by
    refine ⟨v0, ?_⟩
    have hm := s3_mul_table
    apply funext_perm_fin3 <;>
      simp only [eulerianRegE1, LinearMap.coe_mk, AddHom.coe_mk,
        hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
        s3_id_mul, hv0_vals.1, hv0_vals.2.1, hv0_vals.2.2.1,
        hv0_vals.2.2.2.1, hv0_vals.2.2.2.2.1, hv0_vals.2.2.2.2.2] <;> ring
  have hv1_mem : v1 ∈ LinearMap.range (eulerianRegE1 K) := by
    refine ⟨v1, ?_⟩
    have hm := s3_mul_table
    apply funext_perm_fin3 <;>
      simp only [eulerianRegE1, LinearMap.coe_mk, AddHom.coe_mk,
        hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
        hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
        s3_id_mul, hv1_vals.1, hv1_vals.2.1, hv1_vals.2.2.1,
        hv1_vals.2.2.2.1, hv1_vals.2.2.2.2.1, hv1_vals.2.2.2.2.2] <;> ring
  let b : Fin 2 → LinearMap.range (eulerianRegE1 K) :=
    fun i => if i = 0 then ⟨v0, hv0_mem⟩ else ⟨v1, hv1_mem⟩
  have hb_ind : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum
    have hval : c 0 • v0 + c 1 • v1 = 0 := by
      have := congrArg Subtype.val hsum
      simpa [Fin.sum_univ_two, b] using this
    have hc0 : c 0 = 0 := by
      have h := congrFun hval s3Swap01
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        hv0_vals.2.2.1, hv1_vals.2.2.1, mul_neg, mul_one, mul_zero, add_zero, neg_eq_zero] at h
      exact h
    have hc1 : c 1 = 0 := by
      have h := congrFun hval s3Swap12
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        hv0_vals.2.2.2.1, hv1_vals.2.2.2.1, mul_neg, mul_one, mul_zero, zero_add, neg_eq_zero] at h
      exact h
    intro i; fin_cases i <;> assumption
  have hb_span : ⊤ ≤ Submodule.span K (Set.range b) := by
    intro ⟨y, f, hf⟩ _
    have hy_eq : y = (-eulerianRegE1 K f s3Swap01) • v0 + (-eulerianRegE1 K f s3Swap12) • v1 := by
      rw [← hf]
      have hm := s3_mul_table
      apply funext_perm_fin3 <;>
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          eulerianRegE1, LinearMap.coe_mk, AddHom.coe_mk,
          hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
          s3_id_mul, hv0_vals.1, hv0_vals.2.1, hv0_vals.2.2.1,
          hv0_vals.2.2.2.1, hv0_vals.2.2.2.2.1, hv0_vals.2.2.2.2.2,
          hv1_vals.1, hv1_vals.2.1, hv1_vals.2.2.1,
          hv1_vals.2.2.2.1, hv1_vals.2.2.2.2.1, hv1_vals.2.2.2.2.2] <;> ring
    have hsub_eq : (⟨y, ⟨f, hf⟩⟩ : LinearMap.range (eulerianRegE1 K)) =
        (-eulerianRegE1 K f s3Swap01) • b 0 + (-eulerianRegE1 K f s3Swap12) • b 1 :=
      Subtype.ext hy_eq
    rw [hsub_eq]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hfr := Module.finrank_eq_card_basis (Module.Basis.mk hb_ind hb_span)
  simpa using hfr

/-- Exact image dimension `3` for `eulerianRegE2 K` on `K[S₃]`. -/
theorem eulerianRegE2_finrank (K : Type*) [Field K] [CharZero K] :
    Module.finrank K (LinearMap.range (eulerianRegE2 K)) = 3 := by
  let w0 : S3Algebra K := fun σ => if σ = s3Id then 1 else if σ = s3Rev then -1 else 0
  let w1 : S3Algebra K := fun σ => if σ = s3Swap01 then 1 else if σ = s3Cyc2 then -1 else 0
  let w2 : S3Algebra K := fun σ => if σ = s3Swap12 then 1 else if σ = s3Cyc1 then -1 else 0
  have hne : s3Id ≠ s3Rev ∧ s3Id ≠ s3Swap01 ∧ s3Id ≠ s3Swap12 ∧ s3Id ≠ s3Cyc1 ∧ s3Id ≠ s3Cyc2 ∧
      s3Rev ≠ s3Swap01 ∧ s3Rev ≠ s3Swap12 ∧ s3Rev ≠ s3Cyc1 ∧ s3Rev ≠ s3Cyc2 ∧
      s3Swap01 ≠ s3Swap12 ∧ s3Swap01 ≠ s3Cyc1 ∧ s3Swap01 ≠ s3Cyc2 ∧
      s3Swap12 ≠ s3Cyc1 ∧ s3Swap12 ≠ s3Cyc2 ∧ s3Cyc1 ≠ s3Cyc2 := by decide
  have hw0_vals : w0 s3Id = 1 ∧ w0 s3Rev = -1 ∧ w0 s3Swap01 = 0 ∧
      w0 s3Swap12 = 0 ∧ w0 s3Cyc1 = 0 ∧ w0 s3Cyc2 = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [w0]; split_ifs <;> first | rfl | (exfalso; grind))
  have hw1_vals : w1 s3Id = 0 ∧ w1 s3Rev = 0 ∧ w1 s3Swap01 = 1 ∧
      w1 s3Swap12 = 0 ∧ w1 s3Cyc1 = 0 ∧ w1 s3Cyc2 = -1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [w1]; split_ifs <;> first | rfl | (exfalso; grind))
  have hw2_vals : w2 s3Id = 0 ∧ w2 s3Rev = 0 ∧ w2 s3Swap01 = 0 ∧
      w2 s3Swap12 = 1 ∧ w2 s3Cyc1 = -1 ∧ w2 s3Cyc2 = 0 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp only [w2]; split_ifs <;> first | rfl | (exfalso; grind))
  have hw0_mem : w0 ∈ LinearMap.range (eulerianRegE2 K) := by
    refine ⟨w0, ?_⟩
    have hm := s3_mul_table
    apply funext_perm_fin3 <;>
      simp only [eulerianRegE2, LinearMap.coe_mk, AddHom.coe_mk,
        hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, s3_id_mul,
        hw0_vals.1, hw0_vals.2.1, hw0_vals.2.2.1, hw0_vals.2.2.2.1,
        hw0_vals.2.2.2.2.1, hw0_vals.2.2.2.2.2] <;> ring
  have hw1_mem : w1 ∈ LinearMap.range (eulerianRegE2 K) := by
    refine ⟨w1, ?_⟩
    have hm := s3_mul_table
    apply funext_perm_fin3 <;>
      simp only [eulerianRegE2, LinearMap.coe_mk, AddHom.coe_mk,
        hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, s3_id_mul,
        hw1_vals.1, hw1_vals.2.1, hw1_vals.2.2.1, hw1_vals.2.2.2.1,
        hw1_vals.2.2.2.2.1, hw1_vals.2.2.2.2.2] <;> ring
  have hw2_mem : w2 ∈ LinearMap.range (eulerianRegE2 K) := by
    refine ⟨w2, ?_⟩
    have hm := s3_mul_table
    apply funext_perm_fin3 <;>
      simp only [eulerianRegE2, LinearMap.coe_mk, AddHom.coe_mk,
        hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, s3_id_mul,
        hw2_vals.1, hw2_vals.2.1, hw2_vals.2.2.1, hw2_vals.2.2.2.1,
        hw2_vals.2.2.2.2.1, hw2_vals.2.2.2.2.2] <;> ring
  let b : Fin 3 → LinearMap.range (eulerianRegE2 K) :=
    ![⟨w0, hw0_mem⟩, ⟨w1, hw1_mem⟩, ⟨w2, hw2_mem⟩]
  have hb_ind : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum
    have hval : c 0 • w0 + c 1 • w1 + c 2 • w2 = 0 := by
      have := congrArg Subtype.val hsum
      simpa [Fin.sum_univ_three, b, add_assoc] using this
    have hc0 : c 0 = 0 := by
      have h := congrFun hval s3Id
      simp [hw0_vals.1, hw1_vals.1, hw2_vals.1] at h; exact h
    have hc1 : c 1 = 0 := by
      have h := congrFun hval s3Swap01
      simp [hw0_vals.2.2.1, hw1_vals.2.2.1, hw2_vals.2.2.1] at h; exact h
    have hc2 : c 2 = 0 := by
      have h := congrFun hval s3Swap12
      simp [hw0_vals.2.2.2.1, hw1_vals.2.2.2.1, hw2_vals.2.2.2.1] at h; exact h
    intro i; fin_cases i <;> assumption
  have hb_span : ⊤ ≤ Submodule.span K (Set.range b) := by
    intro ⟨y, f, hf⟩ _
    have hy_eq : y =
        (eulerianRegE2 K f s3Id) • w0 +
        (eulerianRegE2 K f s3Swap01) • w1 +
        (eulerianRegE2 K f s3Swap12) • w2 := by
      rw [← hf]
      have hm := s3_mul_table
      apply funext_perm_fin3 <;>
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          eulerianRegE2, LinearMap.coe_mk, AddHom.coe_mk,
          hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, s3_id_mul,
          hw0_vals.1, hw0_vals.2.1, hw0_vals.2.2.1, hw0_vals.2.2.2.1,
          hw0_vals.2.2.2.2.1, hw0_vals.2.2.2.2.2,
          hw1_vals.1, hw1_vals.2.1, hw1_vals.2.2.1, hw1_vals.2.2.2.1,
          hw1_vals.2.2.2.2.1, hw1_vals.2.2.2.2.2,
          hw2_vals.1, hw2_vals.2.1, hw2_vals.2.2.1, hw2_vals.2.2.2.1,
          hw2_vals.2.2.2.2.1, hw2_vals.2.2.2.2.2] <;> ring
    have hsub_eq : (⟨y, ⟨f, hf⟩⟩ : LinearMap.range (eulerianRegE2 K)) =
        (eulerianRegE2 K f s3Id) • b 0 +
        (eulerianRegE2 K f s3Swap01) • b 1 +
        (eulerianRegE2 K f s3Swap12) • b 2 :=
      Subtype.ext hy_eq
    rw [hsub_eq]
    exact Submodule.add_mem _
      (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩)))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
  have hfr := Module.finrank_eq_card_basis (Module.Basis.mk hb_ind hb_span)
  simpa using hfr

/-- Exact image dimension `1` for `eulerianRegE3 K` on `K[S₃]`. -/
theorem eulerianRegE3_finrank (K : Type*) [Field K] [CharZero K] :
    Module.finrank K (LinearMap.range (eulerianRegE3 K)) = 1 := by
  let u : S3Algebra K := fun _ => 1
  have hu_mem : u ∈ LinearMap.range (eulerianRegE3 K) := by
    refine ⟨u, ?_⟩
    funext σ
    simp only [eulerianRegE3, LinearMap.coe_mk, AddHom.coe_mk, u]
    ring
  let b : Fin 1 → LinearMap.range (eulerianRegE3 K) := fun _ => ⟨u, hu_mem⟩
  have hb_ind : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum i
    have hval : c 0 • u = 0 := by
      have := congrArg Subtype.val hsum
      simpa [b] using this
    have hc0 : c 0 = 0 := by
      have h := congrFun hval s3Id
      simpa [u] using h
    fin_cases i; exact hc0
  have hb_span : ⊤ ≤ Submodule.span K (Set.range b) := by
    intro ⟨y, f, hf⟩ _
    have hy_eq : y = (eulerianRegE3 K f s3Id) • u := by
      rw [← hf]
      have hm := s3_mul_table
      apply funext_perm_fin3 <;>
        simp only [Pi.smul_apply, smul_eq_mul, u, mul_one,
          eulerianRegE3, LinearMap.coe_mk, AddHom.coe_mk,
          hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
          hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2,
          s3_id_mul] <;> ring
    have hsub_eq : (⟨y, ⟨f, hf⟩⟩ : LinearMap.range (eulerianRegE3 K)) =
        (eulerianRegE3 K f s3Id) • b 0 :=
      Subtype.ext hy_eq
    rw [hsub_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  have hfr := Module.finrank_eq_card_basis (Module.Basis.mk hb_ind hb_span)
  simpa using hfr

/-- **Exact `6 = 2 + 3 + 1` Sector Dimension Decomposition on `ℚ[S₃]`:**
The three orthogonal Eulerian idempotents partition `ℚ[S₃]` (`dim = 6`) into subspaces of exact
dimensions `2` (`[2, 1]_Lie`), `3` (`[1, 1, 1] ⊕ [2, 1]_sh`), and `1` (`[3]`). -/
theorem eulerianReg_dim_decomposition_rat :
    Module.finrank ℚ (S3Algebra ℚ) = 6 ∧
    Module.finrank ℚ (LinearMap.range (eulerianRegE1 ℚ)) = 2 ∧
    Module.finrank ℚ (LinearMap.range (eulerianRegE2 ℚ)) = 3 ∧
    Module.finrank ℚ (LinearMap.range (eulerianRegE3 ℚ)) = 1 := by
  refine ⟨?_, eulerianRegE1_finrank ℚ, eulerianRegE2_finrank ℚ, eulerianRegE3_finrank ℚ⟩
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_perm, Fintype.card_fin]
  decide

/-! #### Free Shuffle Algebra of Words & Exact Depth-3 Shuffle Identities -/

/-- Free `K`-vector space on words over an alphabet `α`. -/
abbrev FreeWordSpace (K α : Type*) [CommRing K] := List α →₀ K

/-- Recursive shuffle product `u ⧢ v` on basis words `List α`, valued in `FreeWordSpace K α`. -/
def wordShuffle {K α : Type*} [CommRing K] : List α → List α → FreeWordSpace K α
  | [], v => Finsupp.single v 1
  | a :: u, [] => Finsupp.single (a :: u) 1
  | a :: u, b :: v =>
      (wordShuffle u (b :: v)).mapDomain (a :: ·) +
      (wordShuffle (a :: u) v).mapDomain (b :: ·)
termination_by u v => u.length + v.length

/-- Bilinear shuffle product `⧢` on the free word space `FreeWordSpace K α`. -/
def shuffleMul (K α : Type*) [CommRing K] :
    FreeWordSpace K α →ₗ[K] FreeWordSpace K α →ₗ[K] FreeWordSpace K α :=
  Finsupp.lsum K fun u =>
    (LinearMap.lsmul K (FreeWordSpace K α →ₗ[K] FreeWordSpace K α)).flip
      (Finsupp.lsum K fun v =>
        (LinearMap.lsmul K (FreeWordSpace K α)).flip (wordShuffle u v))

/-- Basis word constructors of lengths 1, 2, 3 and antisymmetrized 2-letter word `K_{bc}`. -/
def word1 {K α : Type*} [CommRing K] (a : α) : FreeWordSpace K α := Finsupp.single [a] 1
def word2 {K α : Type*} [CommRing K] (a b : α) : FreeWordSpace K α := Finsupp.single [a, b] 1
def word3 {K α : Type*} [CommRing K] (a b c : α) : FreeWordSpace K α := Finsupp.single [a, b, c] 1
def wordK2 {K α : Type*} [Field K] (b c : α) : FreeWordSpace K α :=
  (2⁻¹ : K) • (word2 b c - word2 c b)

lemma shuffleMul_single {K α : Type*} [CommRing K] (u v : List α) :
    shuffleMul K α (Finsupp.single u 1) (Finsupp.single v 1) = wordShuffle u v := by
  simp [shuffleMul]

lemma wordShuffle_one_two {K α : Type*} [CommRing K] (a b c : α) :
    wordShuffle (K := K) [a] [b, c] = word3 a b c + word3 b a c + word3 b c a := by
  unfold wordShuffle
  simp only [wordShuffle, Finsupp.mapDomain_add, Finsupp.mapDomain_single, word3, add_assoc]

/-- **Raw Depth-3 Shuffle Identity (exact factor `2`):**
`w_a ⧢ (w_{bc} - w_{cb}) + w_c ⧢ (w_{ab} - w_{ba}) = 2 • (w_{abc} - w_{cba})`. -/
theorem depth3_shuffle_identity_raw {K α : Type*} [CommRing K] (a b c : α) :
    shuffleMul K α (word1 a) (word2 b c - word2 c b) +
      shuffleMul K α (word1 c) (word2 a b - word2 b a) =
    (2 : K) • (word3 a b c - word3 c b a) := by
  simp only [map_sub, word1, word2, shuffleMul_single, wordShuffle_one_two]
  rw [two_smul]
  abel

/-- **Exact Depth-3 Shuffle Identity for `K_{bc} = (1/2)(w_{bc} - w_{cb})`:**
`w_{abc} - w_{cba} = w_a ⧢ K_{bc} + w_c ⧢ K_{ab}`. -/
theorem depth3_shuffle_identity {K α : Type*} [Field K] [CharZero K] (a b c : α) :
    word3 (K := K) a b c - word3 c b a =
      shuffleMul K α (word1 a) (wordK2 b c) + shuffleMul K α (word1 c) (wordK2 a b) := by
  have hraw := depth3_shuffle_identity_raw (K := K) a b c
  simp only [wordK2, map_smul, ← smul_add, hraw, smul_smul]
  have h2 : (2⁻¹ : K) * 2 = 1 := inv_mul_cancel₀ two_ne_zero
  rw [h2, one_smul]

/-- **Exact Depth-3 Alternating Shuffle Identity:**
`w_{abc} - w_{acb} - w_{bac} + w_{bca} + w_{cab} - w_{cba} = 2 • (w_a ⧢ K_{bc} - w_b ⧢ K_{ac} + w_c ⧢ K_{ab})`. -/
theorem depth3_alternating_shuffle_identity {K α : Type*} [Field K] [CharZero K] (a b c : α) :
    word3 (K := K) a b c - word3 a c b - word3 b a c + word3 b c a + word3 c a b - word3 c b a =
      (2 : K) • (shuffleMul K α (word1 a) (wordK2 b c) -
        shuffleMul K α (word1 b) (wordK2 a c) +
        shuffleMul K α (word1 c) (wordK2 a b)) := by
  have h2 : (2 : K) * 2⁻¹ = 1 := mul_inv_cancel₀ two_ne_zero
  simp only [wordK2, map_smul, smul_add, smul_sub, smul_smul, h2, one_smul,
    map_sub, word1, word2, shuffleMul_single, wordShuffle_one_two]
  abel

/-- **Exact `e₂`-Period Pairing Formula:**
For any period evaluation `(J₁, J₂, J₃)` obeying the `(1, 2)`-shuffle identity
`J₁ a * J₂ b c = J₃ a b c + J₃ b a c + J₃ b c a` (with `K_{bc} = (1/2)(J₂ b c - J₂ c b)`):
`∑ a, ∑ b, ∑ c, (e₂ P)_{abc} J₃_{abc} = (1/2) ∑ a, ∑ b, ∑ c, B(P)_{a;bc} J₁_a K_{bc}`. -/
theorem depth3_e2_period_pairing {K : Type*} [Field K] [CharZero K] {D : ℕ}
    (P : Tensor3 K D) (J₁ : Fin D → K) (J₂ : Fin D → Fin D → K) (J₃ : Tensor3 K D)
    (hshuf : ∀ a b c : Fin D, J₁ a * J₂ b c = J₃ a b c + J₃ b a c + J₃ b c a) :
    ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, eulerianE2 K D P a b c * J₃ a b c =
      (2⁻¹ : K) * ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D,
        mixedBilinear P a b c * J₁ a * ((2⁻¹ : K) * (J₂ b c - J₂ c b)) := by
  -- First derive J₃ a b c - J₃ c b a = J₁ a * K b c + J₁ c * K a b
  let K₂ : Fin D → Fin D → K := fun b c => (2⁻¹ : K) * (J₂ b c - J₂ c b)
  have hJdiff : ∀ a b c : Fin D, J₃ a b c - J₃ c b a = J₁ a * K₂ b c + J₁ c * K₂ a b := by
    intro a b c
    have h1 := hshuf a b c
    have h2 := hshuf a c b
    have h3 := hshuf c a b
    have h4 := hshuf c b a
    dsimp only [K₂]
    have hcomb : J₁ a * (J₂ b c - J₂ c b) + J₁ c * (J₂ a b - J₂ b a) =
        2 * (J₃ a b c - J₃ c b a) := by
      rw [mul_sub, mul_sub, h1, h2, h3, h4]; ring
    have hmul : J₁ a * (2⁻¹ * (J₂ b c - J₂ c b)) + J₁ c * (2⁻¹ * (J₂ a b - J₂ b a)) =
        2⁻¹ * (J₁ a * (J₂ b c - J₂ c b) + J₁ c * (J₂ a b - J₂ b a)) := by ring
    rw [hmul, hcomb]
    ring
  -- Rewrite LHS as (1/2) ∑ P a b c * (J₃ a b c - J₃ c b a)
  have hlhs : ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, eulerianE2 K D P a b c * J₃ a b c =
      (2⁻¹ : K) * ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, P a b c * (J₃ a b c - J₃ c b a) := by
    have hswap' : ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, P c b a * J₃ a b c =
        ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, P a b c * J₃ c b a := by
      calc ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, P c b a * J₃ a b c
          = ∑ a : Fin D, ∑ c : Fin D, ∑ b : Fin D, P c b a * J₃ a b c :=
            Finset.sum_congr rfl fun a _ => Finset.sum_comm
        _ = ∑ c : Fin D, ∑ a : Fin D, ∑ b : Fin D, P c b a * J₃ a b c := Finset.sum_comm
        _ = ∑ c : Fin D, ∑ b : Fin D, ∑ a : Fin D, P c b a * J₃ a b c :=
            Finset.sum_congr rfl fun c _ => Finset.sum_comm
    have h1 : ∀ a b c : Fin D,
        eulerianE2 K D P a b c * J₃ a b c =
          (2⁻¹ : K) * (P a b c * J₃ a b c) - (2⁻¹ : K) * (P c b a * J₃ a b c) := by
      intro a b c; simp only [eulerianE2, LinearMap.coe_mk, AddHom.coe_mk]; ring
    simp_rw [h1, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hswap']
    simp_rw [← mul_sub, ← Finset.sum_sub_distrib, ← mul_sub]
  rw [hlhs]
  congr 1
  simp_rw [hJdiff, mul_add, Finset.sum_add_distrib]
  -- Relabel second sum: ∑ a b c, P a b c * (J₁ c * K₂ a b) = ∑ a b c, P b c a * (J₁ a * K₂ b c)
  have hcyc : ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, P a b c * (J₁ c * K₂ a b) =
      ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, P b c a * (J₁ a * K₂ b c) := by
    calc ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, P a b c * (J₁ c * K₂ a b)
        = ∑ a : Fin D, ∑ c : Fin D, ∑ b : Fin D, P a b c * (J₁ c * K₂ a b) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c : Fin D, ∑ a : Fin D, ∑ b : Fin D, P a b c * (J₁ c * K₂ a b) := Finset.sum_comm
  rw [hcyc]
  -- Antisymmetrize (P a b c + P b c a) against skew K₂ b c = -K₂ c b
  have hKskew : ∀ b c : Fin D, K₂ c b = -K₂ b c := fun b c => by dsimp only [K₂]; ring
  have hanti : ∀ (Q : Tensor3 K D),
      ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, Q a b c * (J₁ a * K₂ b c) =
      ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D, (2⁻¹ : K) * (Q a b c - Q a c b) * (J₁ a * K₂ b c) := by
    intro Q
    refine Finset.sum_congr rfl fun a _ => ?_
    have hsw : ∑ b : Fin D, ∑ c : Fin D, Q a c b * (J₁ a * K₂ b c) =
        -(∑ b : Fin D, ∑ c : Fin D, Q a b c * (J₁ a * K₂ b c)) := by
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      rw [hKskew]; ring
    have hexp : ∑ b : Fin D, ∑ c : Fin D, (2⁻¹ : K) * (Q a b c - Q a c b) * (J₁ a * K₂ b c) =
        (2⁻¹ : K) * (∑ b : Fin D, ∑ c : Fin D, Q a b c * (J₁ a * K₂ b c)) -
        (2⁻¹ : K) * (∑ b : Fin D, ∑ c : Fin D, Q a c b * (J₁ a * K₂ b c)) := by
      simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
    rw [hexp, hsw]
    ring
  rw [← Finset.sum_add_distrib]
  have hcomb : ∀ a : Fin D,
      (∑ b : Fin D, ∑ c : Fin D, P a b c * (J₁ a * K₂ b c)) +
      (∑ b : Fin D, ∑ c : Fin D, P b c a * (J₁ a * K₂ b c)) =
      ∑ b : Fin D, ∑ c : Fin D, (P a b c + P b c a) * (J₁ a * K₂ b c) := fun a => by
    simp_rw [← Finset.sum_add_distrib, ← add_mul]
  simp_rw [hcomb]
  rw [hanti (fun a b c => P a b c + P b c a)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => ?_
  simp only [mixedBilinear, K₂]
  ring

end EulerianIdempotents

/-! ### 2. Exact Cubic Slice-Rank = Vanishing on Codimension-`N` Subspace Equivalence -/

section CubicSliceRankClosedness

/-- A homogeneous cubic polynomial `f : MvPolynomial (Fin D) K` has symmetric cubic slice rank
at most `N` if it can be written as `∑_{i : Fin N} ℓ_i * q_i` with each `ℓ_i` homogeneous of
degree 1 and each `q_i` homogeneous of degree 2. -/
def HasCubicSliceRankLe {K : Type*} [CommRing K] {D : ℕ}
    (N : ℕ) (f : MvPolynomial (Fin D) K) : Prop :=
  ∃ (ℓ q : Fin N → MvPolynomial (Fin D) K),
    (∀ i : Fin N, (ℓ i).IsHomogeneous 1) ∧
    (∀ i : Fin N, (q i).IsHomogeneous 2) ∧
    f = ∑ i : Fin N, ℓ i * q i

/-- A polynomial `f : MvPolynomial (Fin D) K` vanishes on a codimension-`≤ N` linear subspace
of `Fin D → K`. -/
def VanishesOnCodimLe {K : Type*} [Field K] {D : ℕ}
    (N : ℕ) (f : MvPolynomial (Fin D) K) : Prop :=
  ∃ W : Submodule K (Fin D → K),
    Module.finrank K ((Fin D → K) ⧸ W) ≤ N ∧
    ∀ x ∈ W, MvPolynomial.eval x f = 0

/-- Every homogeneous degree-1 polynomial is a linear combination of the coordinate variables `X j`. -/
lemma isHomogeneous_one_eq_sum {K : Type*} [CommRing K] {D : ℕ}
    {ℓ : MvPolynomial (Fin D) K} (hℓ : ℓ.IsHomogeneous 1) :
    ℓ = ∑ j : Fin D, MvPolynomial.C (ℓ.coeff (Finsupp.single j 1)) * MvPolynomial.X j := by
  ext d
  rw [MvPolynomial.coeff_sum]
  by_cases hd : d.sum (fun _ k => k) = 1
  · -- A multi-index of degree 1 is Finsupp.single j₀ 1 for a unique j₀
    have hex : ∃ j₀ : Fin D, d = Finsupp.single j₀ 1 := by
      have hne : d ≠ 0 := by
        intro h0; subst h0; simp at hd
      have hexj : ∃ j₀ : Fin D, d j₀ ≠ 0 := by
        by_contra hall; push Not at hall; exact hne (Finsupp.ext hall)
      obtain ⟨j₀, hj₀⟩ := hexj
      refine ⟨j₀, Finsupp.ext fun j => ?_⟩
      have hsum : ∑ i : Fin D, d i = 1 := by
        rw [← hd, Finsupp.sum_fintype]; intro _; rfl
      by_cases hjj : j = j₀
      · subst hjj
        have hle : d j ≤ ∑ i : Fin D, d i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_eq_of_ne hjj]
        have h2 : d j₀ + d j ≤ ∑ i : Fin D, d i := by
          have hpair : ({j₀, j} : Finset (Fin D)) ⊆ Finset.univ := Finset.subset_univ _
          have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => d i) hpair
            (fun _ _ _ => Nat.zero_le _)
          rw [Finset.sum_pair (Ne.symm hjj)] at hle
          exact hle
        omega
    obtain ⟨j₀, rfl⟩ := hex
    rw [Finset.sum_eq_single j₀]
    · simp [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    · intro j _ hne
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
      have hne' : Finsupp.single j 1 ≠ Finsupp.single j₀ 1 := fun h =>
        hne (by
          have := congrArg (fun f : Fin D →₀ ℕ => f j) h
          simp [Finsupp.single_eq_of_ne hne] at this)
      split_ifs with h
      · exact absurd h hne'
      · exact mul_zero _
    · intro h; exact absurd (Finset.mem_univ j₀) h
  · rw [hℓ.coeff_eq_zero hd]
    symm
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X]
    have hne : Finsupp.single j 1 ≠ d := fun h =>
      hd (by rw [← h, Finsupp.sum_single_index rfl])
    split_ifs with h
    · exact absurd h hne
    · exact mul_zero _

/-- Evaluating a homogeneous degree-1 polynomial defines a `K`-linear functional on `Fin D → K`. -/
def linearFormOfHomogOne {K : Type*} [CommRing K] {D : ℕ}
    {ℓ : MvPolynomial (Fin D) K} (hℓ : ℓ.IsHomogeneous 1) : (Fin D → K) →ₗ[K] K where
  toFun x := MvPolynomial.eval x ℓ
  map_add' x y := by
    rw [isHomogeneous_one_eq_sum hℓ]
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    rw [isHomogeneous_one_eq_sum hℓ]
    simp [Finset.mul_sum, mul_left_comm]

/-- Linear change of variables on `MvPolynomial (Fin D) K` induced by a linear map `L : (Fin D → K) →ₗ[K] (Fin D → K)`. -/
def linChangeVars {K : Type*} [CommRing K] {D : ℕ}
    (L : (Fin D → K) →ₗ[K] (Fin D → K)) :
    MvPolynomial (Fin D) K →ₐ[K] MvPolynomial (Fin D) K :=
  MvPolynomial.aeval fun a : Fin D =>
    ∑ b : Fin D, MvPolynomial.C (L (Pi.single b 1) a) * MvPolynomial.X b

lemma eval_linChangeVars {K : Type*} [CommRing K] {D : ℕ}
    (L : (Fin D → K) →ₗ[K] (Fin D → K)) (y : Fin D → K) (p : MvPolynomial (Fin D) K) :
    MvPolynomial.eval y (linChangeVars L p) = MvPolynomial.eval (L y) p := by
  let φ₁ : MvPolynomial (Fin D) K →ₐ[K] K := (MvPolynomial.aeval y).comp (linChangeVars L)
  let φ₂ : MvPolynomial (Fin D) K →ₐ[K] K := MvPolynomial.aeval (L y)
  have hEq : φ₁ = φ₂ := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [φ₁, φ₂, AlgHom.comp_apply, linChangeVars, MvPolynomial.aeval_X,
      map_sum, map_mul, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]
    have hy : y = ∑ b : Fin D, y b • Pi.single b (1 : K) := by
      funext j; simp [Pi.single_apply]
    conv_rhs => rw [hy, map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  exact AlgHom.congr_fun hEq p

lemma linChangeVars_comp {K : Type*} [CommRing K] {D : ℕ}
    (L₁ L₂ : (Fin D → K) →ₗ[K] (Fin D → K)) :
    (linChangeVars L₂).comp (linChangeVars L₁) = linChangeVars (L₁.comp L₂) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, linChangeVars, MvPolynomial.aeval_X, map_sum, map_mul,
    MvPolynomial.aeval_C, LinearMap.comp_apply]
  change ∑ b : Fin D, MvPolynomial.C (L₁ (Pi.single b 1) a) *
      (∑ c : Fin D, MvPolynomial.C (L₂ (Pi.single c 1) b) * MvPolynomial.X c) =
    ∑ c : Fin D, MvPolynomial.C (L₁ (L₂ (Pi.single c 1)) a) * MvPolynomial.X c
  simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_mul, ← map_sum]
  congr 2
  have hL₂ : L₂ (Pi.single c 1) = ∑ b : Fin D, (L₂ (Pi.single c 1) b) • Pi.single b (1 : K) := by
    funext j; simp [Pi.single_apply]
  conv_rhs => rw [hL₂, map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

lemma linChangeVars_id {K : Type*} [CommRing K] {D : ℕ} :
    linChangeVars (LinearMap.id : (Fin D → K) →ₗ[K] (Fin D → K)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro a
  simp only [linChangeVars, MvPolynomial.aeval_X, LinearMap.id_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hne; simp [Ne.symm hne]
  · intro h; exact absurd (Finset.mem_univ a) h

lemma linChangeVars_isHomogeneous {K : Type*} [CommRing K] {D d : ℕ}
    (L : (Fin D → K) →ₗ[K] (Fin D → K)) {p : MvPolynomial (Fin D) K}
    (hp : p.IsHomogeneous d) : (linChangeVars L p).IsHomogeneous d := by
  have hlin : ∀ a : Fin D, (linChangeVars L (MvPolynomial.X a)).IsHomogeneous 1 := by
    intro a
    simp only [linChangeVars, MvPolynomial.aeval_X]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun b _ => ?_
    have h1 := (MvPolynomial.isHomogeneous_C (Fin D) (L (Pi.single b 1) a)).mul
      (MvPolynomial.isHomogeneous_X K b)
    simpa using h1
  have hp_eq : p = ∑ m ∈ p.support, MvPolynomial.C (p.coeff m) * ∏ a : Fin D, (MvPolynomial.X a) ^ (m a) := by
    conv_lhs => rw [p.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    intro _; exact pow_zero _
  rw [hp_eq, map_sum]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun m hm => ?_
  have hm_deg : ∑ a : Fin D, m a = d := by
    have hsum : m.sum (fun _ k => k) = d := by
      by_contra hne
      exact (MvPolynomial.mem_support_iff.mp hm) (hp.coeff_eq_zero hne)
    rw [← hsum, Finsupp.sum_fintype]
    intro _; rfl
  rw [map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, map_prod]
  have hprod : ∀ (S : Finset (Fin D)),
      (∏ a ∈ S, linChangeVars L ((MvPolynomial.X a) ^ (m a))).IsHomogeneous (∑ a ∈ S, m a) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using MvPolynomial.isHomogeneous_one (Fin D) K
    | @insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, map_pow]
      have hpow : (linChangeVars L (MvPolynomial.X a) ^ m a).IsHomogeneous (m a) := by
        simpa using (hlin a).pow (m a)
      exact hpow.mul ih
  have hC : (algebraMap K (MvPolynomial (Fin D) K) (p.coeff m)).IsHomogeneous 0 :=
    MvPolynomial.isHomogeneous_C (Fin D) (p.coeff m)
  have hmul := hC.mul (hprod Finset.univ)
  simpa [hm_deg] using hmul

/-- **Exact Cubic Slice-Rank = Vanishing on Codimension-`N` Subspace Equivalence:**
Over any characteristic-zero field `K`, a homogeneous cubic polynomial `f : MvPolynomial (Fin D) K`
can be written as `∑_{i : Fin N} ℓ_i * q_i` (linear forms `ℓ_i`, quadratic forms `q_i`)
if and only if there exists a linear subspace `W ≤ K^D` of codimension `≤ N` on which `f`
vanishes identically. -/
theorem cubic_sliceRank_le_iff_vanishes_on_codim_subspace
    {K : Type*} [Field K] [CharZero K] {D N : ℕ}
    {f : MvPolynomial (Fin D) K} (hf : f.IsHomogeneous 3) :
    HasCubicSliceRankLe N f ↔ VanishesOnCodimLe N f := by
  constructor
  · -- (→) Take W = ⋂ ker ℓ_i = ker (x ↦ fun i => eval x (ℓ i))
    rintro ⟨ℓ, q, hℓ, _, hf_eq⟩
    let Φ : (Fin D → K) →ₗ[K] (Fin N → K) :=
      { toFun := fun x i => linearFormOfHomogOne (hℓ i) x
        map_add' := fun x y => by funext i; simp
        map_smul' := fun c x => by funext i; simp }
    refine ⟨LinearMap.ker Φ, ?_, ?_⟩
    · have hquot : ((Fin D → K) ⧸ LinearMap.ker Φ) ≃ₗ[K] LinearMap.range Φ :=
        Φ.quotKerEquivRange
      rw [hquot.finrank_eq]
      calc Module.finrank K (LinearMap.range Φ)
          ≤ Module.finrank K (Fin N → K) := Submodule.finrank_le _
        _ = N := Module.finrank_fin_fun K
    · intro x hx
      rw [hf_eq, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hxi : MvPolynomial.eval x (ℓ i) = 0 := congrFun hx i
      rw [map_mul, hxi, zero_mul]
  · -- (←) Coordinate-change W to {y | ∀ i < m, y i = 0}
    rintro ⟨W, hcodim, hvanish⟩
    let m : ℕ := Module.finrank K ((Fin D → K) ⧸ W)
    let k : ℕ := Module.finrank K W
    have hmk : m + k = D := by
      have h := Submodule.finrank_quotient_add_finrank W
      simpa [m, k, Module.finrank_fin_fun] using h
    -- Pick a complementary subspace U to W (finrank U = m)
    obtain ⟨U, hcomplW⟩ := Submodule.exists_isCompl W
    have hcompl : IsCompl U W := hcomplW.symm
    have hU_dim : Module.finrank K U = m := by
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq U W
      rw [hcompl.sup_eq_top, hcompl.inf_eq_bot, finrank_top, finrank_bot,
          add_zero, Module.finrank_fin_fun] at h1
      omega
    let bU : Module.Basis (Fin m) K U := Module.finBasisOfFinrankEq K U hU_dim
    let bW : Module.Basis (Fin k) K W := Module.finBasisOfFinrankEq K W rfl
    -- Combine bU and bW into a basis B of Fin D → K indexed by Fin D
    let eIdx : Fin m ⊕ Fin k ≃ Fin D := finSumFinEquiv.trans (finCongr hmk)
    let vSum : Fin m ⊕ Fin k → (Fin D → K) := Sum.elim (fun i => (bU i).1) (fun j => (bW j).1)
    have hvSum_ind : LinearIndependent K vSum := by
      rw [Fintype.linearIndependent_iff]
      intro c hsum
      rw [Fintype.sum_sum_type] at hsum
      simp only [vSum, Sum.elim_inl, Sum.elim_inr] at hsum
      have hu_mem : (∑ i : Fin m, c (Sum.inl i) • (bU i).1) ∈ U :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bU i).2
      have hw_mem : (∑ j : Fin k, c (Sum.inr j) • (bW j).1) ∈ W :=
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (bW j).2
      have heq_neg : (∑ i : Fin m, c (Sum.inl i) • (bU i).1) =
          -(∑ j : Fin k, c (Sum.inr j) • (bW j).1) := eq_neg_of_add_eq_zero_left hsum
      have hu_in_W : (∑ i : Fin m, c (Sum.inl i) • (bU i).1) ∈ W := heq_neg ▸ W.neg_mem hw_mem
      have hu_zero : ∑ i : Fin m, c (Sum.inl i) • (bU i).1 = 0 := by
        have hinf : (∑ i : Fin m, c (Sum.inl i) • (bU i).1) ∈ U ⊓ W := ⟨hu_mem, hu_in_W⟩
        rwa [hcompl.inf_eq_bot, Submodule.mem_bot] at hinf
      have hw_zero : ∑ j : Fin k, c (Sum.inr j) • (bW j).1 = 0 := by
        simpa [hu_zero] using hsum
      intro s
      cases s with
      | inl i =>
        have hsub : ∑ x : Fin m, c (Sum.inl x) • bU x = 0 :=
          Subtype.ext (by simpa using hu_zero)
        exact Fintype.linearIndependent_iff.mp bU.linearIndependent _ hsub i
      | inr j =>
        have hsub : ∑ x : Fin k, c (Sum.inr x) • bW x = 0 :=
          Subtype.ext (by simpa using hw_zero)
        exact Fintype.linearIndependent_iff.mp bW.linearIndependent _ hsub j
    have hvSum_span : ⊤ ≤ Submodule.span K (Set.range vSum) := by
      intro x _
      have hx : x ∈ U ⊔ W := by rw [hcompl.sup_eq_top]; trivial
      rw [Submodule.mem_sup] at hx
      obtain ⟨u, hu, w, hw, rfl⟩ := hx
      have hu_rep : u = ∑ i : Fin m, (bU.repr ⟨u, hu⟩ i) • (bU i).1 := by
        have h := congrArg Subtype.val (bU.sum_repr ⟨u, hu⟩)
        rw [Submodule.coe_sum] at h
        exact h.symm
      have hw_rep : w = ∑ j : Fin k, (bW.repr ⟨w, hw⟩ j) • (bW j).1 := by
        have h := congrArg Subtype.val (bW.sum_repr ⟨w, hw⟩)
        rw [Submodule.coe_sum] at h
        exact h.symm
      rw [hu_rep, hw_rep]
      exact Submodule.add_mem _
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩))
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩))
    let B : Module.Basis (Fin D) K (Fin D → K) :=
      (Module.Basis.mk hvSum_ind hvSum_span).reindex eIdx
    -- Linear equivalence e : y ↦ ∑ d, y d • B d sends {y | ∀ i < m, y i = 0} into W
    let e : (Fin D → K) ≃ₗ[K] (Fin D → K) := B.equivFun.symm
    have he_mem_W : ∀ y : Fin D → K, (∀ i : Fin D, i.val < m → y i = 0) → e y ∈ W := by
      intro y hy
      have he_eq : e y = ∑ d : Fin D, y d • B d := by
        change B.equivFun.symm y = _
        rw [Module.Basis.equivFun_symm_apply]
      rw [he_eq]
      refine Submodule.sum_mem W fun d _ => ?_
      by_cases hdm : d.val < m
      · rw [hy d hdm, zero_smul]; exact W.zero_mem
      · refine Submodule.smul_mem W (y d) ?_
        have hBd : B d = vSum (eIdx.symm d) := by
          simp [B, Module.Basis.reindex_apply]
        rw [hBd]
        cases hsym : eIdx.symm d with
        | inl i =>
          have hd_eq : d = eIdx (Sum.inl i) := (Equiv.symm_apply_eq eIdx).mp hsym
          have hlt : d.val < m := by simp [hd_eq, eIdx]
          exact absurd hlt hdm
        | inr j =>
          exact (bW j).2
    -- Pull back f along e to g = linChangeVars e f
    let g : MvPolynomial (Fin D) K := linChangeVars e.toLinearMap f
    have hg_hom : g.IsHomogeneous 3 := linChangeVars_isHomogeneous e.toLinearMap hf
    have hg_vanish : ∀ y : Fin D → K, (∀ i : Fin D, i.val < m → y i = 0) →
        MvPolynomial.eval y g = 0 := fun y hy => by
      rw [eval_linChangeVars]
      exact hvanish (e y) (he_mem_W y hy)
    -- Show every monomial d ∈ g.support uses at least one coordinate i < m
    have hsupp_uses_m : ∀ d ∈ g.support, ∃ i : Fin D, i.val < m ∧ 1 ≤ d i := by
      -- First prove g_bad (monomials avoiding i < m) vanishes identically
      let badSupp : Finset (Fin D →₀ ℕ) := g.support.filter fun d => ∀ i : Fin D, i.val < m → d i = 0
      -- Convert g_bad into a polynomial in Fin k → K and apply MvPolynomial.funext
      let embedK : Fin k → Fin D := fun j => eIdx (Sum.inr j)
      have hembedK_ge : ∀ j : Fin k, ¬ (embedK j).val < m := fun j => by
        simp [embedK, eIdx]
      have hembedK_inj : Function.Injective embedK := fun a b h =>
        Sum.inr.inj (eIdx.injective h)
      let gBad : MvPolynomial (Fin k) K :=
        ∑ d ∈ badSupp, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun j : Fin k => d (embedK j))
          (g.coeff d)
      have hgBad_eval : ∀ z : Fin k → K, MvPolynomial.eval z gBad = 0 := by
        intro z
        let y : Fin D → K := fun i =>
          if h : i.val < m then 0 else z ⟨i.val - m, by have := i.isLt; omega⟩
        have hy_zero : ∀ i : Fin D, i.val < m → y i = 0 := fun i hi => by simp [y, hi]
        have hy_embed : ∀ j : Fin k, y (embedK j) = z j := fun j => by
          have hge := hembedK_ge j
          have hval : (embedK j).val = m + j.val := by simp [embedK, eIdx]
          simp only [y, hge, ↓reduceDIte]
          congr 1; ext; dsimp only; omega
        have hg_eq : MvPolynomial.eval y g = MvPolynomial.eval z gBad := by
          rw [MvPolynomial.eval_eq', map_sum]
          have hsub : badSupp ⊆ g.support := Finset.filter_subset _ _
          rw [← Finset.sum_subset hsub]
          · refine Finset.sum_congr rfl fun d hd => ?_
            have hd_bad : ∀ i : Fin D, i.val < m → d i = 0 := (Finset.mem_filter.mp hd).2
            rw [MvPolynomial.eval_monomial]
            congr 1
            rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
            have hprod_split :
                ∏ i : Fin D, y i ^ d i = ∏ j : Fin k, y (embedK j) ^ d (embedK j) := by
              rw [← Finset.prod_image (f := fun i : Fin D => y i ^ d i) (s := Finset.univ)
                (g := embedK) (fun a _ b _ h => hembedK_inj h)]
              refine (Finset.prod_subset (Finset.subset_univ _) ?_).symm
              intro i _ hi_not
              have hi_lt : i.val < m := by
                by_contra hge
                have hiD := i.isLt
                have hmem : i ∈ Finset.univ.image embedK := by
                  refine Finset.mem_image.mpr ⟨⟨i.val - m, by omega⟩, Finset.mem_univ _, ?_⟩
                  ext; simp [embedK, eIdx]; omega
                exact hi_not hmem
              rw [hd_bad i hi_lt, pow_zero]
            rw [hprod_split]
            refine Finset.prod_congr rfl fun j _ => by simp [hy_embed j]
          · intro d hd_supp hd_not_bad
            have hex : ∃ i : Fin D, i.val < m ∧ d i ≠ 0 := by
              by_contra hall; push Not at hall
              exact hd_not_bad (Finset.mem_filter.mpr ⟨hd_supp, hall⟩)
            obtain ⟨i, hi_lt, hdi_ne⟩ := hex
            have hprod0 : (∏ a : Fin D, y a ^ d a) = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ i)
                (by rw [hy_zero i hi_lt, zero_pow hdi_ne])
            rw [hprod0, mul_zero]
        rw [← hg_eq]
        exact hg_vanish y hy_zero
      have hgBad_zero : gBad = 0 := MvPolynomial.funext fun z => by rw [hgBad_eval z, map_zero]
      -- Each d ∈ badSupp determines a distinct multi-index on Fin k, so badSupp = ∅
      intro d hd_supp
      by_contra hall
      push Not at hall
      have hd_bad : d ∈ badSupp := Finset.mem_filter.mpr ⟨hd_supp, fun i hi => by
        have := hall i hi; omega⟩
      let dK : Fin k →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j : Fin k => d (embedK j)
      have hcoeff0 : gBad.coeff dK = 0 := by rw [hgBad_zero]; simp
      dsimp only [gBad] at hcoeff0
      rw [MvPolynomial.coeff_sum] at hcoeff0
      have hsingle : ∑ d' ∈ badSupp,
          (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun j : Fin k => d' (embedK j))
            (g.coeff d')).coeff dK = g.coeff d := by
        rw [Finset.sum_eq_single d]
        · simp [dK, MvPolynomial.coeff_monomial]
        · intro d' hd' hne
          rw [MvPolynomial.coeff_monomial]
          have hneK : (Finsupp.equivFunOnFinite.symm fun j : Fin k => d' (embedK j)) ≠ dK := by
            intro heqK
            apply hne
            ext i
            by_cases hi : i.val < m
            · rw [(Finset.mem_filter.mp hd').2 i hi, (Finset.mem_filter.mp hd_bad).2 i hi]
            · let j : Fin k := ⟨i.val - m, by omega⟩
              have hj : embedK j = i := by ext; simp [embedK, eIdx, j]; omega
              have hval := congrArg (fun f : Fin k →₀ ℕ => f j) heqK
              simpa [dK, hj] using hval
          rw [ite_eq_right_iff.mpr fun h => absurd h hneK]
        · intro h; exact absurd hd_bad h
      rw [hsingle] at hcoeff0
      exact (MvPolynomial.mem_support_iff.mp hd_supp) hcoeff0
    -- Partition g.support by assigning each d ∈ g.support to a coordinate idx(d) : Fin m
    have hpick : ∀ d ∈ g.support, ∃ i : Fin m, 1 ≤ d ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩ := by
      intro d hd
      obtain ⟨i, hi_lt, hdi⟩ := hsupp_uses_m d hd
      exact ⟨⟨i.val, hi_lt⟩, hdi⟩
    let iEmb : Fin m → Fin D := fun i => ⟨i.val, lt_of_lt_of_le i.isLt (by omega)⟩
    by_cases hm0 : m = 0
    · -- If m = 0, g.support = ∅, so g = 0 and f = 0
      have hg0 : g = 0 := by
        ext d
        by_contra hne
        have hd_supp : d ∈ g.support := MvPolynomial.mem_support_iff.mpr hne
        obtain ⟨i, hi_lt, _⟩ := hsupp_uses_m d hd_supp
        omega
      have hf0 : f = 0 := by
        have hcomp := linChangeVars_comp e.toLinearMap e.symm.toLinearMap
        have hid : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
          ext x; simp
        have hfeq : linChangeVars e.symm.toLinearMap g = f := by
          change ((linChangeVars e.symm.toLinearMap).comp (linChangeVars e.toLinearMap)) f = f
          rw [hcomp, hid, linChangeVars_id, AlgHom.id_apply]
        rw [← hfeq, hg0, map_zero]
      refine ⟨fun _ => 0, fun _ => 0, fun _ => MvPolynomial.isHomogeneous_zero _ _ 1,
        fun _ => MvPolynomial.isHomogeneous_zero _ _ 2, by simp [hf0]⟩
    · have hm_pos : 0 < m := Nat.pos_of_ne_zero hm0
      let assign : (Fin D →₀ ℕ) → Fin m := fun d =>
        if h : d ∈ g.support then Classical.choose (hpick d h) else ⟨0, hm_pos⟩
      have hassign_ge : ∀ d ∈ g.support, 1 ≤ d (iEmb (assign d)) := fun d hd => by
        simp only [assign]
        split_ifs
        exact Classical.choose_spec (hpick d hd)
      -- Define quadratic factors qTilde : Fin m → MvPolynomial (Fin D) K
      let qTilde : Fin m → MvPolynomial (Fin D) K := fun i =>
        ∑ d ∈ g.support.filter (fun d => assign d = i),
          MvPolynomial.monomial (d - Finsupp.single (iEmb i) 1) (g.coeff d)
      have hqTilde_hom : ∀ i : Fin m, (qTilde i).IsHomogeneous 2 := by
        intro i
        refine MvPolynomial.IsHomogeneous.sum _ _ _ fun d hd => ?_
        have hd_supp : d ∈ g.support := (Finset.mem_filter.mp hd).1
        have hdi : assign d = i := (Finset.mem_filter.mp hd).2
        have hge : 1 ≤ d (iEmb i) := hdi ▸ hassign_ge d hd_supp
        have hd_deg : d.sum (fun _ r => r) = 3 := by
          by_contra hne
          exact (MvPolynomial.mem_support_iff.mp hd_supp) (hg_hom.coeff_eq_zero hne)
        have hsub_add : (d - Finsupp.single (iEmb i) 1) + Finsupp.single (iEmb i) 1 = d := by
          ext j
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          by_cases hji : iEmb i = j
          · subst hji; simp only [ite_true]; omega
          · simp [hji]
        have hdeg2 : (d - Finsupp.single (iEmb i) 1).sum (fun _ r => r) = 2 := by
          have h1 : ((d - Finsupp.single (iEmb i) 1) + Finsupp.single (iEmb i) 1).sum
              (fun _ r => r) = (d - Finsupp.single (iEmb i) 1).sum (fun _ r => r) + 1 := by
            rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
                Finsupp.sum_single_index rfl]
          rw [hsub_add, hd_deg] at h1
          omega
        exact MvPolynomial.isHomogeneous_monomial (g.coeff d) hdeg2
      have hg_decomp : g = ∑ i : Fin m, MvPolynomial.X (iEmb i) * qTilde i := by
        conv_lhs => rw [g.as_sum]
        rw [← Finset.sum_fiberwise_of_maps_to (g := assign) (t := Finset.univ)
          (fun _ _ => Finset.mem_univ _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [qTilde, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d hd => ?_
        have hd_supp : d ∈ g.support := (Finset.mem_filter.mp hd).1
        have hdi : assign d = i := (Finset.mem_filter.mp hd).2
        have hge : 1 ≤ d (iEmb i) := hdi ▸ hassign_ge d hd_supp
        have hsub_add : Finsupp.single (iEmb i) 1 + (d - Finsupp.single (iEmb i) 1) = d := by
          ext j
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          by_cases hji : iEmb i = j
          · subst hji; simp only [ite_true]; omega
          · simp [hji]
        rw [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul, hsub_add]
      -- Pad from Fin m to Fin N (using m ≤ N) and pull back via linChangeVars e.symm
      let ℓFin : Fin N → MvPolynomial (Fin D) K := fun j =>
        if hj : j.val < m then
          linChangeVars e.symm.toLinearMap (MvPolynomial.X (iEmb ⟨j.val, hj⟩))
        else 0
      let qFin : Fin N → MvPolynomial (Fin D) K := fun j =>
        if hj : j.val < m then
          linChangeVars e.symm.toLinearMap (qTilde ⟨j.val, hj⟩)
        else 0
      refine ⟨ℓFin, qFin, ?_, ?_, ?_⟩
      · intro j
        simp only [ℓFin]
        split_ifs
        · exact linChangeVars_isHomogeneous _ (MvPolynomial.isHomogeneous_X K _)
        · exact MvPolynomial.isHomogeneous_zero _ _ 1
      · intro j
        simp only [qFin]
        split_ifs
        · exact linChangeVars_isHomogeneous _ (hqTilde_hom _)
        · exact MvPolynomial.isHomogeneous_zero _ _ 2
      · have hfeq : f = linChangeVars e.symm.toLinearMap g := by
          have hcomp := linChangeVars_comp e.toLinearMap e.symm.toLinearMap
          have hid : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext x; simp
          change f = ((linChangeVars e.symm.toLinearMap).comp (linChangeVars e.toLinearMap)) f
          rw [hcomp, hid, linChangeVars_id, AlgHom.id_apply]
        rw [hfeq, hg_decomp, map_sum]
        have hpad : ∑ j : Fin N, ℓFin j * qFin j =
            ∑ i : Fin m, linChangeVars e.symm.toLinearMap (MvPolynomial.X (iEmb i) * qTilde i) := by
          let embM : Fin m ↪ Fin N := ⟨fun i => ⟨i.val, lt_of_lt_of_le i.isLt hcodim⟩,
            fun a b h => Fin.ext (by simpa using congrArg Fin.val h)⟩
          rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map embM))]
          · rw [Finset.sum_map]
            refine Finset.sum_congr rfl fun i _ => ?_
            have hi : (embM i).val < m := i.isLt
            simp only [ℓFin, qFin, hi, ↓reduceDIte, map_mul]
            rfl
          · intro j _ hj_not
            have hnotlt : ¬ j.val < m := fun hlt =>
              hj_not (Finset.mem_map.mpr ⟨⟨j.val, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
            simp [ℓFin, qFin, hnotlt]
        exact hpad.symm

/-- Cubic polynomial associated to a 3-tensor `S : Tensor3 K D`. -/
def cubicPolyOfTensor {K : Type*} [CommRing K] {D : ℕ} (S : Tensor3 K D) :
    MvPolynomial (Fin D) K :=
  ∑ a : Fin D, ∑ b : Fin D, ∑ c : Fin D,
    MvPolynomial.C (S a b c) * MvPolynomial.X a * MvPolynomial.X b * MvPolynomial.X c

lemma cubicPolyOfTensor_isHomogeneous {K : Type*} [CommRing K] {D : ℕ} (S : Tensor3 K D) :
    (cubicPolyOfTensor S).IsHomogeneous 3 := by
  unfold cubicPolyOfTensor
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun a _ =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun b _ =>
    MvPolynomial.IsHomogeneous.sum _ _ _ fun c _ => ?_
  have h1 := ((MvPolynomial.isHomogeneous_C (Fin D) (S a b c)).mul
    (MvPolynomial.isHomogeneous_X K a)).mul (MvPolynomial.isHomogeneous_X K b)
  have h2 := h1.mul (MvPolynomial.isHomogeneous_X K c)
  simpa using h2

/-- Tensor-level specialization of `cubic_sliceRank_le_iff_vanishes_on_codim_subspace`. -/
theorem symTensor_cubic_sliceRank_le_iff_vanishes_on_codim_subspace
    {K : Type*} [Field K] [CharZero K] {D N : ℕ} (S : Tensor3 K D) :
    HasCubicSliceRankLe N (cubicPolyOfTensor S) ↔ VanishesOnCodimLe N (cubicPolyOfTensor S) :=
  cubic_sliceRank_le_iff_vanishes_on_codim_subspace (cubicPolyOfTensor_isHomogeneous S)

end CubicSliceRankClosedness

/-! ### 3. Tao's Diagonal Cubic Slice-Rank Lower Bound & `V_cube` Escape from `F₂` -/

section TaoDiagonalSliceRank

/-- **Support-Size Linear Algebra Lemma (valid over EVERY field `K`):**
Every subspace `S ≤ (Fin D → K)` of dimension `s = Module.finrank K S` contains a vector `v ∈ S`
with at least `s` nonzero coordinates. -/
theorem exists_mem_support_ge_finrank {K : Type*} [Field K] {D : ℕ}
    (S : Submodule K (Fin D → K)) :
    ∃ v ∈ S, Module.finrank K S ≤ (Finset.univ.filter fun k : Fin D => v k ≠ 0).card := by
  let s := Module.finrank K S
  let B : Module.Basis (Fin s) K S := Module.finBasisOfFinrankEq K S rfl
  let colVec : Fin D → (Fin s → K) := fun k a => (B a).1 k
  -- The columns colVec k span Fin s → K
  have hcol_span : Submodule.span K (Set.range colVec) = ⊤ := by
    by_contra hne
    let U := Submodule.span K (Set.range colVec)
    have hlt : Module.finrank K U < Module.finrank K (Fin s → K) := by
      rw [← finrank_top K (Fin s → K)]
      exact Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hne)
    let ev : (Fin s → K) →ₗ[K] (U →ₗ[K] K) :=
      { toFun := fun α =>
          { toFun := fun u => ∑ a : Fin s, α a * u.1 a
            map_add' := fun u₁ u₂ => by simp [mul_add, Finset.sum_add_distrib]
            map_smul' := fun r u => by simp [Finset.mul_sum, mul_left_comm] }
        map_add' := fun α₁ α₂ => by ext u; simp [add_mul, Finset.sum_add_distrib]
        map_smul' := fun r α => by ext u; simp [Finset.mul_sum, mul_assoc] }
    have hker_pos : 0 < Module.finrank K (LinearMap.ker ev) := by
      have h1 := LinearMap.finrank_range_add_finrank_ker ev
      have h2 : Module.finrank K (LinearMap.range ev) ≤ Module.finrank K (U →ₗ[K] K) :=
        Submodule.finrank_le _
      have h3 : Module.finrank K (U →ₗ[K] K) = Module.finrank K U :=
        Module.finrank_linearMap_self K K U
      omega
    have : Nontrivial (LinearMap.ker ev) := Module.nontrivial_of_finrank_pos hker_pos
    obtain ⟨⟨α, hα_ker⟩, hα_ne⟩ := exists_ne (0 : LinearMap.ker ev)
    have hα_ne0 : α ≠ 0 := fun h0 => hα_ne (Subtype.ext h0)
    have hlin : ∑ a : Fin s, α a • B a = 0 := by
      apply Subtype.ext
      funext k
      have hk : colVec k ∈ U := Submodule.subset_span ⟨k, rfl⟩
      have h0 := congrArg (fun f : U →ₗ[K] K => f ⟨colVec k, hk⟩) hα_ker
      simpa [ev, colVec] using h0
    exact hα_ne0 (funext (Fintype.linearIndependent_iff.mp B.linearIndependent α hlin))
  -- Extract s linearly independent columns by induction on m ≤ s
  have hex_cols : ∀ m ≤ s, ∃ idx : Fin m → Fin D,
      LinearIndependent K (fun j : Fin m => colVec (idx j)) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨Fin.elim0, linearIndependent_empty_type⟩
    | succ m ih =>
      intro hm
      obtain ⟨idx, hidx_ind⟩ := ih (Nat.le_of_succ_le hm)
      have hlt : Module.finrank K (Submodule.span K (Set.range fun j : Fin m => colVec (idx j))) <
          Module.finrank K (Fin s → K) := by
        rw [finrank_span_eq_card hidx_ind, Fintype.card_fin, Module.finrank_fin_fun]
        exact hm
      have hne_top : Submodule.span K (Set.range fun j : Fin m => colVec (idx j)) ≠ ⊤ := by
        intro htop; rw [htop, finrank_top] at hlt; exact lt_irrefl _ hlt
      have hex_k : ∃ k : Fin D, colVec k ∉ Submodule.span K (Set.range fun j : Fin m => colVec (idx j)) := by
        by_contra hall; push Not at hall
        have hsub : Submodule.span K (Set.range colVec) ≤
            Submodule.span K (Set.range fun j : Fin m => colVec (idx j)) := by
          rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact hall k
        rw [hcol_span, top_le_iff] at hsub
        exact hne_top hsub
      obtain ⟨k₀, hk₀⟩ := hex_k
      refine ⟨Fin.snoc idx k₀, ?_⟩
      rw [Fintype.linearIndependent_iff]
      intro g hsum
      have hglast : g (Fin.last m) = 0 := by
        by_contra hgne
        have hmem : colVec k₀ ∈ Submodule.span K (Set.range fun j : Fin m => colVec (idx j)) := by
          rw [Fin.sum_univ_castSucc] at hsum
          simp only [Fin.snoc_castSucc, Fin.snoc_last] at hsum
          have h1 : g (Fin.last m) • colVec k₀ = -(∑ j : Fin m, g j.castSucc • colVec (idx j)) :=
            eq_neg_of_add_eq_zero_right hsum
          have h2 := congrArg ((g (Fin.last m))⁻¹ • ·) h1
          simp only [inv_smul_smul₀ hgne] at h2
          rw [h2]
          exact Submodule.smul_mem _ _ (Submodule.neg_mem _ (Submodule.sum_mem _ fun j _ =>
            Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)))
        exact hk₀ hmem
      intro j
      refine Fin.lastCases hglast (fun j' => ?_) j
      rw [Fin.sum_univ_castSucc] at hsum
      simp only [Fin.snoc_castSucc, Fin.snoc_last, hglast, zero_smul, add_zero] at hsum
      exact Fintype.linearIndependent_iff.mp hidx_ind (fun x => g x.castSucc) hsum j'
  obtain ⟨idx, hidx_ind⟩ := hex_cols s le_rfl
  let A : Matrix (Fin s) (Fin s) K := Matrix.of fun a j => (B a).1 (idx j)
  have hdet_ne : A.det ≠ 0 := by
    intro hdet0
    obtain ⟨w, hw_ne, hw_mul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
    have hlin : ∑ j : Fin s, w j • colVec (idx j) = 0 := by
      funext a
      have ha := congrFun hw_mul a
      simpa [Matrix.mulVec, dotProduct, A, colVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        mul_comm] using ha
    exact hw_ne (funext (Fintype.linearIndependent_iff.mp hidx_ind w hlin))
  have hidx_inj : Function.Injective idx := by
    intro j₁ j₂ hEq
    by_contra hne
    exact hdet_ne (Matrix.det_zero_of_column_eq hne fun a => by simp [A, hEq])
  -- Solve α ᵥ* A = (1, ..., 1) and form v = ∑ a, α a • (B a).1 ∈ S
  let α : Fin s → K := (fun _ : Fin s => (1 : K)) ᵥ* A⁻¹
  let v : Fin D → K := ∑ a : Fin s, α a • (B a).1
  have hv_mem : v ∈ S := Submodule.sum_mem S fun a _ => Submodule.smul_mem S _ (B a).2
  have hv_one : ∀ j : Fin s, v (idx j) = 1 := fun j => by
    have hmul : α ᵥ* A = fun _ : Fin s => (1 : K) := by
      simp only [α, Matrix.vecMul_vecMul,
        Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdet_ne), Matrix.vecMul_one]
    have hj := congrFun hmul j
    simpa [v, Matrix.vecMul, dotProduct, A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hj
  refine ⟨v, hv_mem, ?_⟩
  have hsub : Finset.univ.image idx ⊆ Finset.univ.filter fun k : Fin D => v k ≠ 0 := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hv_one j]; exact one_ne_zero⟩
  calc s = (Finset.univ : Finset (Fin s)).card := by simp
    _ = (Finset.univ.image idx).card := (Finset.card_image_of_injective _ hidx_inj).symm
    _ ≤ (Finset.univ.filter fun k : Fin D => v k ≠ 0).card := Finset.card_le_card hsub

/-- Rank of a sum of `N` outer products `u α i * w α j` is at most `N`. -/
lemma matrix_rank_sum_outer_le {K : Type*} [Field K] {D N : ℕ}
    (u w : Fin N → Fin D → K) :
    (Matrix.of fun i j : Fin D => ∑ α : Fin N, u α i * w α j).rank ≤ N := by
  let M : Matrix (Fin D) (Fin D) K := Matrix.of fun i j => ∑ α : Fin N, u α i * w α j
  let Φ : (Fin N → K) →ₗ[K] (Fin D → K) :=
    { toFun := fun c i => ∑ α : Fin N, c α * u α i
      map_add' := fun c₁ c₂ => by funext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by funext i; simp [Finset.mul_sum, mul_assoc] }
  have hle : LinearMap.range M.mulVecLin ≤ LinearMap.range Φ := by
    rintro _ ⟨x, rfl⟩
    refine ⟨fun α => ∑ j : Fin D, w α j * x j, ?_⟩
    funext i
    change ∑ α : Fin N, (∑ j : Fin D, w α j * x j) * u α i =
      ∑ j : Fin D, (∑ α : Fin N, u α i * w α j) * x j
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun α _ => by ring
  calc M.rank = Module.finrank K (LinearMap.range M.mulVecLin) := rfl
    _ ≤ Module.finrank K (LinearMap.range Φ) := Submodule.finrank_mono hle
    _ ≤ Module.finrank K (Fin N → K) := by
        have h := LinearMap.finrank_range_add_finrank_ker Φ
        omega
    _ = N := Module.finrank_fin_fun K

/-- Subadditivity of matrix rank: `(A + B).rank ≤ A.rank + B.rank`. -/
lemma matrix_rank_add_le {K : Type*} [Field K] {D : ℕ} (A B : Matrix (Fin D) (Fin D) K) :
    (A + B).rank ≤ A.rank + B.rank := by
  have hle : LinearMap.range (A + B).mulVecLin ≤
      LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin := by
    rintro _ ⟨x, rfl⟩
    have hadd : (A + B).mulVecLin x = A.mulVecLin x + B.mulVecLin x := by simp
    rw [hadd]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ ⟨x, rfl⟩
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  have hmono := Submodule.finrank_mono hle
  change Module.finrank K (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank K (LinearMap.range A.mulVecLin) +
    Module.finrank K (LinearMap.range B.mulVecLin)
  omega

/-- Exact rank of a diagonal matrix equals the number of nonzero diagonal entries. -/
lemma matrix_rank_diagonal_eq_card_ne_zero {K : Type*} [Field K] {D : ℕ} (d : Fin D → K) :
    (Matrix.diagonal d).rank = (Finset.univ.filter fun i : Fin D => d i ≠ 0).card := by
  let S := Finset.univ.filter fun i : Fin D => d i ≠ 0
  let v : S → LinearMap.range (Matrix.diagonal d).mulVecLin := fun i =>
    ⟨(Pi.single i.1 (1 : K) : Fin D → K), ⟨(Pi.single i.1 (d i.1)⁻¹ : Fin D → K), by
      funext j
      change (Matrix.diagonal d *ᵥ (Pi.single i.1 (d i.1)⁻¹ : Fin D → K)) j =
        (Pi.single i.1 (1 : K) : Fin D → K) j
      rw [Matrix.mulVec_diagonal]
      by_cases hji : j = i.1
      · subst hji
        have hne : d i.1 ≠ 0 := (Finset.mem_filter.mp i.2).2
        simp [mul_inv_cancel₀ hne]
      · simp [hji]⟩⟩
  have hv_ind : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro c hsum i
    have hval := congrFun (congrArg Subtype.val hsum) i.1
    simp only [Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
      smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply, v] at hval
    rw [Finset.sum_eq_single i] at hval
    · simpa using hval
    · intro j _ hne
      have hne' : i.1 ≠ j.1 := fun h => hne (Subtype.ext h.symm)
      simp [hne']
    · intro h; exact absurd (Finset.mem_univ i) h
  have hv_span : ⊤ ≤ Submodule.span K (Set.range v) := by
    rintro ⟨_, ⟨x, rfl⟩⟩ _
    have hrep : (⟨(Matrix.diagonal d).mulVecLin x, ⟨x, rfl⟩⟩ :
        LinearMap.range (Matrix.diagonal d).mulVecLin) =
        ∑ i : S, (d i.1 * x i.1) • v i := by
      apply Subtype.ext
      funext j
      simp only [Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
        smul_eq_mul, v]
      change (Matrix.diagonal d *ᵥ x) j =
        ∑ i : S, (d i.1 * x i.1) * (Pi.single i.1 (1 : K) : Fin D → K) j
      rw [Matrix.mulVec_diagonal]
      by_cases hdj : d j = 0
      · rw [hdj, zero_mul]
        symm
        refine Finset.sum_eq_zero fun i _ => ?_
        have hne : j ≠ i.1 := fun h => (Finset.mem_filter.mp i.2).2 (h ▸ hdj)
        simp [hne]
      · have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hdj⟩
        rw [Finset.sum_eq_single (⟨j, hjS⟩ : S)]
        · simp
        · intro i _ hne
          have hne' : j ≠ i.1 := fun h => hne (Subtype.ext h.symm)
          simp [hne']
        · intro h; exact absurd (Finset.mem_univ (⟨j, hjS⟩ : S)) h
    rw [hrep]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hfr := Module.finrank_eq_card_basis (Module.Basis.mk hv_ind hv_span)
  rw [Matrix.rank, hfr, Fintype.card_coe]

/-- **Tao's Diagonal Cubic Slice-Rank Lower Bound (10-line proof over ANY field `K`):**
For ANY diagonal 3-tensor `T(i, j, k) = if i = j ∧ j = k then c i else 0` with `∀ i, c i ≠ 0`
on `Fin D`, EVERY 3-mode slice decomposition
`T(i,j,k) = ∑_{α < N₁} a α i * A α j k + ∑_{β < N₂} b β j * B β i k + ∑_{γ < N₃} d γ k * C γ i j`
satisfies **`D ≤ N₁ + N₂ + N₃`**. -/
theorem tao_diagonal_cubic_sliceRank_lower_bound
    {K : Type*} [Field K] {D N₁ N₂ N₃ : ℕ}
    (c : Fin D → K) (hc : ∀ i : Fin D, c i ≠ 0)
    (a : Fin N₁ → Fin D → K) (A : Fin N₁ → Fin D → Fin D → K)
    (b : Fin N₂ → Fin D → K) (B : Fin N₂ → Fin D → Fin D → K)
    (d : Fin N₃ → Fin D → K) (C : Fin N₃ → Fin D → Fin D → K)
    (hdecomp : ∀ i j k : Fin D,
      (if i = j ∧ j = k then c i else 0) =
        (∑ α : Fin N₁, a α i * A α j k) +
        (∑ β : Fin N₂, b β j * B β i k) +
        (∑ γ : Fin N₃, d γ k * C γ i j)) :
    D ≤ N₁ + N₂ + N₃ := by
  -- Kernel of the N₃ mode-3 linear forms
  let Φ : (Fin D → K) →ₗ[K] (Fin N₃ → K) :=
    { toFun := fun v γ => ∑ k : Fin D, d γ k * v k
      map_add' := fun v₁ v₂ => by funext γ; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r v => by funext γ; simp [Finset.mul_sum, mul_left_comm] }
  let S := LinearMap.ker Φ
  have hdim_S : D - N₃ ≤ Module.finrank K S := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Φ
    have hrg : Module.finrank K (LinearMap.range Φ) ≤ N₃ := by
      calc Module.finrank K (LinearMap.range Φ)
          ≤ Module.finrank K (Fin N₃ → K) := Submodule.finrank_le _
        _ = N₃ := Module.finrank_fin_fun K
    rw [Module.finrank_fin_fun] at hrn
    change D - N₃ ≤ Module.finrank K (LinearMap.ker Φ)
    omega
  obtain ⟨v, hv_ker, hv_supp⟩ := exists_mem_support_ge_finrank S
  -- Contract the 3rd index with v
  let M₁ : Matrix (Fin D) (Fin D) K :=
    Matrix.of fun i j => ∑ α : Fin N₁, a α i * (∑ k : Fin D, A α j k * v k)
  let M₂ : Matrix (Fin D) (Fin D) K :=
    Matrix.of fun i j => ∑ β : Fin N₂, (∑ k : Fin D, B β i k * v k) * b β j
  have hdiag_eq : Matrix.diagonal (fun i => c i * v i) = M₁ + M₂ := by
    ext i j
    have hsum : ∑ k : Fin D, (if i = j ∧ j = k then c i else 0) * v k =
        Matrix.diagonal (fun i => c i * v i) i j := by
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Finset.sum_eq_single i]
        · simp
        · intro k _ hne; simp [Ne.symm hne]
        · intro h; exact absurd (Finset.mem_univ i) h
      · rw [Matrix.diagonal_apply_ne _ hij]
        exact Finset.sum_eq_zero fun k _ => by simp [hij]
    rw [← hsum]
    simp_rw [hdecomp, add_mul, Finset.sum_add_distrib]
    have hthird : ∑ k : Fin D, (∑ γ : Fin N₃, d γ k * C γ i j) * v k = 0 := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun γ _ => ?_
      have hγ : ∑ k : Fin D, d γ k * v k = 0 := congrFun hv_ker γ
      have hfact : ∑ k : Fin D, d γ k * C γ i j * v k =
          C γ i j * ∑ k : Fin D, d γ k * v k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hfact, hγ, mul_zero]
    rw [hthird, add_zero]
    change (∑ k : Fin D, (∑ α : Fin N₁, a α i * A α j k) * v k) +
        (∑ k : Fin D, (∑ β : Fin N₂, b β j * B β i k) * v k) = M₁ i j + M₂ i j
    congr 1
    · simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      change ∑ k : Fin D, a α i * A α j k * v k = a α i * ∑ k : Fin D, A α j k * v k
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => by ring
    · simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      change ∑ k : Fin D, b β j * B β i k * v k = (∑ k : Fin D, B β i k * v k) * b β j
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by ring
  -- Compare ranks
  have hfilt_eq : (Finset.univ.filter fun i : Fin D => c i * v i ≠ 0) =
      (Finset.univ.filter fun i : Fin D => v i ≠ 0) := by
    ext i
    simp [hc i]
  have hrk_diag : (Matrix.diagonal (fun i => c i * v i)).rank =
      (Finset.univ.filter fun i : Fin D => v i ≠ 0).card := by
    rw [matrix_rank_diagonal_eq_card_ne_zero, hfilt_eq]
  have hrk_le : (M₁ + M₂).rank ≤ N₁ + N₂ :=
    le_trans (matrix_rank_add_le M₁ M₂)
      (Nat.add_le_add (matrix_rank_sum_outer_le a (fun α j => ∑ k, A α j k * v k))
        (matrix_rank_sum_outer_le (fun β i => ∑ k, B β i k * v k) b))
  rw [hdiag_eq] at hrk_diag
  have hS_le : Module.finrank K S ≤ (M₁ + M₂).rank := by
    rw [hrk_diag]
    exact hv_supp
  omega

/-- **Exact Diagonal Slice Rank = `D`:**
Combines Tao's lower bound (`D ≤ N₁ + N₂ + N₃`) with the explicit size-`D` upper-bound
decomposition (`N₁ = D, N₂ = 0, N₃ = 0`). -/
theorem tao_diagonal_cubic_sliceRank_exact
    {K : Type*} [Field K] {D : ℕ} (c : Fin D → K) (hc : ∀ i : Fin D, c i ≠ 0) :
    (∃ (a : Fin D → Fin D → K) (A : Fin D → Fin D → Fin D → K),
      ∀ i j k : Fin D, (if i = j ∧ j = k then c i else 0) = ∑ α : Fin D, a α i * A α j k) ∧
    (∀ (N₁ N₂ N₃ : ℕ)
      (a : Fin N₁ → Fin D → K) (A : Fin N₁ → Fin D → Fin D → K)
      (b : Fin N₂ → Fin D → K) (B : Fin N₂ → Fin D → Fin D → K)
      (d : Fin N₃ → Fin D → K) (C : Fin N₃ → Fin D → Fin D → K),
      (∀ i j k : Fin D,
        (if i = j ∧ j = k then c i else 0) =
          (∑ α : Fin N₁, a α i * A α j k) +
          (∑ β : Fin N₂, b β j * B β i k) +
          (∑ γ : Fin N₃, d γ k * C γ i j)) →
      D ≤ N₁ + N₂ + N₃) := by
  refine ⟨⟨fun α i => if i = α then c α else 0,
    fun α j k => if j = α ∧ k = α then 1 else 0, fun i j k => ?_⟩,
    fun _ _ _ a A b B d C h => tao_diagonal_cubic_sliceRank_lower_bound c hc a A b B d C h⟩
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij
      by_cases hik : i = k
      · subst hik; simp
      · simp [hik, Ne.symm hik]
    · simp [hij, Ne.symm hij]
  · intro α _ hne; simp [hne.symm]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Diagonal homogeneous cubic polynomial `∑_{i : Fin D} c_i X_i^3`. -/
def diagCubic {K : Type*} [CommRing K] {D : ℕ} (c : Fin D → K) : MvPolynomial (Fin D) K :=
  ∑ i : Fin D, MvPolynomial.C (c i) * (MvPolynomial.X i) ^ 3

/-- Trilinear polarization of any polynomial `f : MvPolynomial (Fin D) K` on standard basis
vectors `(e_i, e_j, e_k)`. -/
def cubicPolarTensor {K : Type*} [CommRing K] {D : ℕ}
    (f : MvPolynomial (Fin D) K) (i j k : Fin D) : K :=
  let ei : Fin D → K := Pi.single i 1
  let ej : Fin D → K := Pi.single j 1
  let ek : Fin D → K := Pi.single k 1
  MvPolynomial.eval (ei + ej + ek) f -
    MvPolynomial.eval (ei + ej) f -
    MvPolynomial.eval (ei + ek) f -
    MvPolynomial.eval (ej + ek) f +
    MvPolynomial.eval ei f +
    MvPolynomial.eval ej f +
    MvPolynomial.eval ek f

private lemma eval_homogTwo_add {K : Type*} [CommRing K] {D : ℕ}
    {q : MvPolynomial (Fin D) K} (hq : q.IsHomogeneous 2) (x y z : Fin D → K) :
    let B : (Fin D → K) → (Fin D → K) → K := fun u v =>
      MvPolynomial.eval (u + v) q - MvPolynomial.eval u q - MvPolynomial.eval v q
    MvPolynomial.eval (x + y + z) q =
      MvPolynomial.eval x q + MvPolynomial.eval y q + MvPolynomial.eval z q +
        B x y + B x z + B y z := by
  intro B
  have hq_eq : q = ∑ d ∈ q.support,
      MvPolynomial.C (q.coeff d) * ∏ a : Fin D, (MvPolynomial.X a) ^ (d a) := by
    conv_lhs => rw [q.as_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    intro _; exact pow_zero _
  -- Every multi-index of degree 2 is either single a 2 or single a 1 + single b 1
  have hmon : ∀ d : Fin D →₀ ℕ, d.sum (fun _ k => k) = 2 →
      ∃ a b : Fin D, d = Finsupp.single a 1 + Finsupp.single b 1 := by
    intro d hd
    have hsum : ∑ i : Fin D, d i = 2 := by
      rw [← hd, Finsupp.sum_fintype]; intro _; rfl
    have hex1 : ∃ a : Fin D, 1 ≤ d a := by
      by_contra hall; push Not at hall
      have h0 : ∑ i : Fin D, d i = 0 := Finset.sum_eq_zero fun i _ => by have := hall i; omega
      omega
    obtain ⟨a, ha⟩ := hex1
    let d' := d - Finsupp.single a 1
    have hsum' : ∑ i : Fin D, d' i = 1 := by
      have hadd : ∀ i : Fin D, d' i + (Finsupp.single a 1) i = d i := fun i => by
        simp only [d', Finsupp.tsub_apply, Finsupp.single_apply]
        by_cases hia : a = i
        · subst hia; simp only [ite_true]; omega
        · simp [hia]
      have htot : (∑ i : Fin D, d' i) + (∑ i : Fin D, (Finsupp.single a 1) i) = ∑ i : Fin D, d i := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => hadd i
      have h1 : ∑ i : Fin D, (Finsupp.single a 1 : Fin D →₀ ℕ) i = 1 := by
        rw [Finset.sum_eq_single a]
        · rw [Finsupp.single_eq_same]
        · intro i _ hne; rw [Finsupp.single_eq_of_ne hne]
        · intro h; exact absurd (Finset.mem_univ a) h
      omega
    have hex2 : ∃ b : Fin D, 1 ≤ d' b := by
      by_contra hall; push Not at hall
      have h0 : ∑ i : Fin D, d' i = 0 := Finset.sum_eq_zero fun i _ => by have := hall i; omega
      omega
    obtain ⟨b, hb⟩ := hex2
    refine ⟨a, b, Finsupp.ext fun i => ?_⟩
    have hd'_eq : d' = Finsupp.single b 1 := by
      ext j
      by_cases hjb : j = b
      · subst hjb
        have hle : d' j ≤ ∑ r : Fin D, d' r :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        rw [Finsupp.single_eq_same]; omega
      · rw [Finsupp.single_eq_of_ne hjb]
        have hpair : ({b, j} : Finset (Fin D)) ⊆ Finset.univ := Finset.subset_univ _
        have hle := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => d' i) hpair
          (fun _ _ _ => Nat.zero_le _)
        rw [Finset.sum_pair (Ne.symm hjb)] at hle
        omega
    have hadd : d' i + (Finsupp.single a 1) i = d i := by
      simp only [d', Finsupp.tsub_apply, Finsupp.single_apply]
      by_cases hia : a = i
      · subst hia; simp only [ite_true]; omega
      · simp [hia]
    rw [← hadd, hd'_eq, Finsupp.add_apply, add_comm]
  -- Reduce to verifying the identity for each degree-2 monomial (u a * u b)
  dsimp only [B]
  rw [hq_eq]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, map_pow, MvPolynomial.eval_X,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd_deg : d.sum (fun _ k => k) = 2 := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hq.coeff_eq_zero hne)
  obtain ⟨a, b, rfl⟩ := hmon d hd_deg
  have hprod_eval : ∀ u : Fin D → K,
      (∏ r : Fin D, u r ^ ((Finsupp.single a 1 + Finsupp.single b 1 : Fin D →₀ ℕ) r)) = u a * u b := fun u => by
    have hsingle : ∀ x : Fin D, (∏ r : Fin D, u r ^ ((Finsupp.single x 1 : Fin D →₀ ℕ) r)) = u x := fun x => by
      rw [Finset.prod_eq_single x]
      · rw [Finsupp.single_eq_same, pow_one]
      · intro r _ hne; rw [Finsupp.single_eq_of_ne hne, pow_zero]
      · intro h; exact absurd (Finset.mem_univ x) h
    have hsplit : ∏ r : Fin D, u r ^ ((Finsupp.single a 1 + Finsupp.single b 1 : Fin D →₀ ℕ) r) =
        (∏ r : Fin D, u r ^ ((Finsupp.single a 1 : Fin D →₀ ℕ) r)) *
        (∏ r : Fin D, u r ^ ((Finsupp.single b 1 : Fin D →₀ ℕ) r)) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun r _ => by rw [Finsupp.add_apply, pow_add]
    rw [hsplit, hsingle a, hsingle b]
  simp only [hprod_eval, Pi.add_apply]
  ring

private lemma cubicPolarTensor_mul_homog {K : Type*} [CommRing K] {D : ℕ}
    {ℓ q : MvPolynomial (Fin D) K} (hℓ : ℓ.IsHomogeneous 1) (hq : q.IsHomogeneous 2)
    (i j k : Fin D) :
    let B : (Fin D → K) → (Fin D → K) → K := fun u v =>
      MvPolynomial.eval (u + v) q - MvPolynomial.eval u q - MvPolynomial.eval v q
    let ei : Fin D → K := Pi.single i 1
    let ej : Fin D → K := Pi.single j 1
    let ek : Fin D → K := Pi.single k 1
    cubicPolarTensor (ℓ * q) i j k =
      MvPolynomial.eval ei ℓ * B ej ek +
      MvPolynomial.eval ej ℓ * B ei ek +
      MvPolynomial.eval ek ℓ * B ei ej := by
  intro B ei ej ek
  unfold cubicPolarTensor
  dsimp only
  simp only [map_mul]
  let L := linearFormOfHomogOne hℓ
  have hL : ∀ u, MvPolynomial.eval u ℓ = L u := fun _ => rfl
  have hLxy : MvPolynomial.eval (ei + ej) ℓ = L ei + L ej := L.map_add ei ej
  have hLxz : MvPolynomial.eval (ei + ek) ℓ = L ei + L ek := L.map_add ei ek
  have hLyz : MvPolynomial.eval (ej + ek) ℓ = L ej + L ek := L.map_add ej ek
  have hLxyz : MvPolynomial.eval (ei + ej + ek) ℓ = L ei + L ej + L ek := by
    rw [hL, L.map_add, L.map_add]
  have hqxyz := eval_homogTwo_add hq ei ej ek
  have hqxy : MvPolynomial.eval (ei + ej) q = MvPolynomial.eval ei q + MvPolynomial.eval ej q + B ei ej := by
    dsimp only [B]; ring
  have hqxz : MvPolynomial.eval (ei + ek) q = MvPolynomial.eval ei q + MvPolynomial.eval ek q + B ei ek := by
    dsimp only [B]; ring
  have hqyz : MvPolynomial.eval (ej + ek) q = MvPolynomial.eval ej q + MvPolynomial.eval ek q + B ej ek := by
    dsimp only [B]; ring
  rw [hLxyz, hLxy, hLxz, hLyz, hL, hL, hL, hqxyz, hqxy, hqxz, hqyz]
  ring

private lemma cubicPolarTensor_diagCubic {K : Type*} [CommRing K] {D : ℕ}
    (c : Fin D → K) (i j k : Fin D) :
    cubicPolarTensor (diagCubic c) i j k = if i = j ∧ j = k then 6 * c i else 0 := by
  unfold cubicPolarTensor diagCubic
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X,
    Pi.add_apply, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  let ei : Fin D → K := Pi.single i 1
  let ej : Fin D → K := Pi.single j 1
  let ek : Fin D → K := Pi.single k 1
  have hterm : ∀ m : Fin D,
      c m * (ei m + ej m + ek m) ^ 3 -
      c m * (ei m + ej m) ^ 3 -
      c m * (ei m + ek m) ^ 3 -
      c m * (ej m + ek m) ^ 3 +
      c m * ei m ^ 3 +
      c m * ej m ^ 3 +
      c m * ek m ^ 3 =
      6 * c m * ei m * ej m * ek m := fun m => by ring
  change ∑ m : Fin D,
      (c m * (ei m + ej m + ek m) ^ 3 -
      c m * (ei m + ej m) ^ 3 -
      c m * (ei m + ek m) ^ 3 -
      c m * (ej m + ek m) ^ 3 +
      c m * ei m ^ 3 +
      c m * ej m ^ 3 +
      c m * ek m ^ 3) = if i = j ∧ j = k then 6 * c i else 0
  simp_rw [hterm]
  rw [Finset.sum_eq_single i]
  · by_cases hij : i = j
    · subst hij
      by_cases hik : i = k
      · subst hik; simp [ei, ej, ek]
      · simp [ei, ej, ek, hik]
    · simp [ei, ej, ek, hij]
  · intro m _ hne; simp [ei, hne]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Symmetric Cubic Slice-Rank Lower Bound (`3 * N ≥ D`, i.e., `symSliceRank ≥ ⌈D / 3⌉`):**
Over any characteristic-zero field `K`, if the diagonal cubic `∑_{i : Fin D} c_i X_i^3`
(`∀ i, c_i ≠ 0`) admits a symmetric slice decomposition `∑_{r : Fin N} ℓ_r * q_r`, then
**`D ≤ 3 * N`** (equivalently `(D + 2) / 3 ≤ N`). -/
theorem diag_cubic_symSliceRank_lower_bound
    {K : Type*} [Field K] [CharZero K] {D N : ℕ}
    (c : Fin D → K) (hc : ∀ i : Fin D, c i ≠ 0)
    (hslice : HasCubicSliceRankLe N (diagCubic c)) :
    D ≤ 3 * N ∧ (D + 2) / 3 ≤ N := by
  obtain ⟨ℓ, q, hℓ, hq, hf_eq⟩ := hslice
  let B : Fin N → (Fin D → K) → (Fin D → K) → K := fun r u v =>
    MvPolynomial.eval (u + v) (q r) - MvPolynomial.eval u (q r) - MvPolynomial.eval v (q r)
  have hdecomp : ∀ i j k : Fin D,
      (if i = j ∧ j = k then 6 * c i else 0) =
        (∑ r : Fin N, MvPolynomial.eval (Pi.single i 1) (ℓ r) * B r (Pi.single j 1) (Pi.single k 1)) +
        (∑ r : Fin N, MvPolynomial.eval (Pi.single j 1) (ℓ r) * B r (Pi.single i 1) (Pi.single k 1)) +
        (∑ r : Fin N, MvPolynomial.eval (Pi.single k 1) (ℓ r) * B r (Pi.single i 1) (Pi.single j 1)) := by
    intro i j k
    rw [← cubicPolarTensor_diagCubic c i j k, hf_eq]
    have hsum_polar : cubicPolarTensor (∑ r : Fin N, ℓ r * q r) i j k =
        ∑ r : Fin N, cubicPolarTensor (ℓ r * q r) i j k := by
      unfold cubicPolarTensor
      simp only [map_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    rw [hsum_polar]
    simp_rw [cubicPolarTensor_mul_homog (hℓ _) (hq _), Finset.sum_add_distrib]
    rfl
  have h6c : ∀ i : Fin D, (6 : K) * c i ≠ 0 := fun i => mul_ne_zero (by norm_num) (hc i)
  have hle := tao_diagonal_cubic_sliceRank_lower_bound (fun i => 6 * c i) h6c
    (fun r i => MvPolynomial.eval (Pi.single i 1) (ℓ r))
    (fun r j k => B r (Pi.single j 1) (Pi.single k 1))
    (fun r j => MvPolynomial.eval (Pi.single j 1) (ℓ r))
    (fun r i k => B r (Pi.single i 1) (Pi.single k 1))
    (fun r k => MvPolynomial.eval (Pi.single k 1) (ℓ r))
    (fun r i j => B r (Pi.single i 1) (Pi.single j 1))
    hdecomp
  refine ⟨by omega, by omega⟩

/-- **`V_cube` Jet-Weighted Diagonal Cubic Lower Bound (Audit Polish `#2E`):**
For any nonzero jet polynomial `p : Polynomial K` and nonzero weights `c : Fin D → K`, at most
`p.natDegree` diagonal entries of `p(3(i + 1)) c_i` vanish, so any symmetric cubic slice
decomposition of `∑_{i : Fin D} p(3(i + 1)) c_i X_i^3` of length `N` satisfies
`D - p.natDegree ≤ 3 * N` (i.e., `⌈(D - deg p) / 3⌉ ≤ N`). -/
theorem vCube_jet_poly_symSliceRank_lower_bound
    {K : Type*} [Field K] [CharZero K] {D N : ℕ}
    (p : Polynomial K) (hp : p ≠ 0) (c : Fin D → K) (hc : ∀ i : Fin D, c i ≠ 0)
    (hslice : HasCubicSliceRankLe N
      (diagCubic fun i : Fin D => p.eval (3 * ((i.val + 1 : ℕ) : K)) * c i)) :
    D - p.natDegree ≤ 3 * N ∧ (D - p.natDegree + 2) / 3 ≤ N := by
  -- Restrict to the subset S of indices where p(3(i + 1)) ≠ 0
  let S : Finset (Fin D) :=
    Finset.univ.filter fun i : Fin D => p.eval (3 * ((i.val + 1 : ℕ) : K)) ≠ 0
  let Z : Finset (Fin D) :=
    Finset.univ.filter fun i : Fin D => p.eval (3 * ((i.val + 1 : ℕ) : K)) = 0
  have hZ_le : Z.card ≤ p.natDegree := by
    let emb : Fin D ↪ K :=
      ⟨fun i => 3 * ((i.val + 1 : ℕ) : K), fun i j h => by
        have h3 : (3 : K) ≠ 0 := by norm_num
        have h1 : ((i.val + 1 : ℕ) : K) = ((j.val + 1 : ℕ) : K) := mul_left_cancel₀ h3 h
        have h2 : i.val + 1 = j.val + 1 := Nat.cast_injective h1
        exact Fin.ext (by omega)⟩
    have hsub : Z.map emb ⊆ p.roots.toFinset := by
      intro x hx
      obtain ⟨i, hiZ, rfl⟩ := Finset.mem_map.mp hx
      have hroot : p.IsRoot (emb i) := (Finset.mem_filter.mp hiZ).2
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr hroot)
    calc Z.card = (Z.map emb).card := (Finset.card_map emb).symm
      _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ p.roots.card := Multiset.toFinset_card_le p.roots
      _ ≤ p.natDegree := Polynomial.card_roots' p
  have hS_ge : D - p.natDegree ≤ S.card := by
    have hdisj : Disjoint S Z := by
      rw [Finset.disjoint_left]
      intro i hiS hiZ
      exact (Finset.mem_filter.mp hiS).2 (Finset.mem_filter.mp hiZ).2
    have hunion : S ∪ Z = Finset.univ := by
      ext i
      simp only [S, Z, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact ne_or_eq _ _
    have hpart : S.card + Z.card = D := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ, Fintype.card_fin]
    omega
  -- Restrict the cubic polynomial to the |S| surviving coordinates
  let eS : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (by rw [Fintype.card_coe])).symm
  let inc : Fin S.card → Fin D := fun j => (eS j).1
  have hinc_inj : Function.Injective inc := fun a b h => eS.injective (Subtype.ext h)
  let restr : MvPolynomial (Fin D) K →ₐ[K] MvPolynomial (Fin S.card) K :=
    MvPolynomial.aeval fun i : Fin D =>
      if h : i ∈ S then MvPolynomial.X (eS.symm ⟨i, h⟩) else 0
  have hrestr_hom : ∀ (d : ℕ) (g : MvPolynomial (Fin D) K),
      g.IsHomogeneous d → (restr g).IsHomogeneous d := by
    intro d g hg
    have hg_eq : g = ∑ m ∈ g.support,
        MvPolynomial.C (g.coeff m) * ∏ a : Fin D, (MvPolynomial.X a) ^ (m a) := by
      conv_lhs => rw [g.as_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype]
      intro _; exact pow_zero _
    rw [hg_eq, map_sum]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun m hm => ?_
    have hm_deg : ∑ a : Fin D, m a = d := by
      have hsum : m.sum (fun _ k => k) = d := by
        by_contra hne
        exact (MvPolynomial.mem_support_iff.mp hm) (hg.coeff_eq_zero hne)
      rw [← hsum, Finsupp.sum_fintype]; intro _; rfl
    rw [map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, map_prod]
    have hX : ∀ a : Fin D, (restr (MvPolynomial.X a)).IsHomogeneous 1 := fun a => by
      simp only [restr, MvPolynomial.aeval_X]
      split_ifs
      · exact MvPolynomial.isHomogeneous_X K _
      · exact MvPolynomial.isHomogeneous_zero _ _ 1
    have hprod : ∀ (T : Finset (Fin D)),
        (∏ a ∈ T, restr ((MvPolynomial.X a) ^ (m a))).IsHomogeneous (∑ a ∈ T, m a) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simpa using MvPolynomial.isHomogeneous_one (Fin S.card) K
      | @insert a T ha ih =>
        rw [Finset.prod_insert ha, Finset.sum_insert ha, map_pow]
        exact (by simpa using (hX a).pow (m a) : (restr (MvPolynomial.X a) ^ m a).IsHomogeneous (m a)).mul ih
    have hmul := (MvPolynomial.isHomogeneous_C (Fin S.card) (g.coeff m)).mul (hprod Finset.univ)
    simpa [hm_deg] using hmul
  -- Evaluate restr on diagCubic
  let cS : Fin S.card → K := fun j => p.eval (3 * (((inc j).val + 1 : ℕ) : K)) * c (inc j)
  have hcS : ∀ j : Fin S.card, cS j ≠ 0 := fun j =>
    mul_ne_zero (Finset.mem_filter.mp (eS j).2).2 (hc (inc j))
  have hrestr_diag :
      restr (diagCubic fun i : Fin D => p.eval (3 * ((i.val + 1 : ℕ) : K)) * c i) =
      diagCubic cS := by
    unfold diagCubic
    rw [map_sum]
    have hterm : ∀ i : Fin D,
        restr (MvPolynomial.C (p.eval (3 * ((i.val + 1 : ℕ) : K)) * c i) * (MvPolynomial.X i) ^ 3) =
        if h : i ∈ S then
          MvPolynomial.C (p.eval (3 * ((i.val + 1 : ℕ) : K)) * c i) *
            (MvPolynomial.X (eS.symm ⟨i, h⟩)) ^ 3
        else 0 := fun i => by
      simp only [map_mul, map_pow, restr, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
        Algebra.algebraMap_eq_smul_one]
      split_ifs with h
      · simp [MvPolynomial.C_eq_smul_one]
      · simp
    simp_rw [hterm]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    · symm
      refine Finset.sum_bij (fun (j : Fin S.card) _ => inc j)
        (fun j _ => (eS j).2)
        (fun a _ b _ h => hinc_inj h)
        (fun i hi => ⟨eS.symm ⟨i, hi⟩, Finset.mem_univ _, by simp [inc]⟩)
        (fun j _ => ?_)
      have hj : inc j ∈ S := (eS j).2
      simp only [hj, ↓reduceDIte, cS]
      have hsymm : eS.symm ⟨inc j, hj⟩ = j := by
        apply eS.injective
        apply Subtype.ext
        simp [inc]
      rw [hsymm]
    · intro i _ hi
      simp [hi]
  obtain ⟨ℓ, q, hℓ, hq, hf_eq⟩ := hslice
  have hslice_S : HasCubicSliceRankLe N (diagCubic cS) := by
    refine ⟨fun r => restr (ℓ r), fun r => restr (q r),
      fun r => hrestr_hom 1 (ℓ r) (hℓ r),
      fun r => hrestr_hom 2 (q r) (hq r), ?_⟩
    rw [← hrestr_diag, hf_eq, map_sum]
    exact Finset.sum_congr rfl fun r _ => map_mul _ _ _
  have hbound := (diag_cubic_symSliceRank_lower_bound cS hcS hslice_S).1
  omega

end TaoDiagonalSliceRank

end

end CubicTheta.AllD
