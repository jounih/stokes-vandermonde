module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Tactic.Ring

/-! # Depth-2 Triangular Automorphism, Group Commutator & Minimal-Degree Elimination

Unconditional Lean 4 formalization from Mathlib (zero placeholders, standard foundations only)
of the algebraic and Wronskian/Vandermonde core of the depth-2 Vafa–Witten `SU(3)` on `ℂℙ²`
differential transcendence theorem:

1. **Formal-Grading Triangular Substitution & Group Commutator (`triSub`, `triSub_inv`,
   `triSub_commutator_lower`, `triSub_commutator_depth2`, `triSub_commutator_self_zero`,
   `triSub_commutator_symmetric_product_zero`, `triCommutator_iterate`, `multiTriSub`,
   `triCommutatorAlgHom`):**
   For any commutative ring `R` and finite channel index type `ι`, the triangular map
   `(U, V) ↦ (U + A, V + ∑ α, B α * U α + C)` has explicit inverse
   `triSub (-A) (-B) (-C + ∑ α, B α * A α)`. Its group commutator `S₁ ∘ S₂ ∘ S₁⁻¹ ∘ S₂⁻¹`:
   - fixes every lower generator `U α` identically (and every product `U α * U β`, and every
     polynomial in the lower generators);
   - cancels both direct-pole constants `C₁, C₂` identically;
   - translates `V` by the exact antisymmetric bilinear pairing
     `∑ α, (A₂ α * B₁ α - A₁ α * B₂ α)` (and in the contravariant algebra-endomorphism lift on
     `R[V, (U_α)]`, shifts `V` by `∑ α, (A₁ α * B₂ α - A₂ α * B₁ α)`);
   - vanishes identically when `(A₁, B₁, C₁) = (A₂, B₂, C₂)`.
2. **Exact Shifted Vandermonde & Two-Sector Block Determinant (`shiftedVandermonde_det`,
   `shiftedVandermonde_det_ne_zero`, `twoSector_blockVandermonde_det_ne_zero`):**
   Proves `det ((a + b_i)^j) = ∏_{i < j} (b_j - b_i) ≠ 0` for pairwise distinct `b_i`, and
   extends to scaled block-diagonal two-sector Vandermonde matrices of arbitrary jet order `r`.
3. **Integer-Iterate Linearization & Minimal-Degree Elimination Criterion
   (`linear_shift_deriv_eq_zero_of_forall_int_shift`, `all_pderiv_aeval_eq_zero_of_det_ne_zero`,
   `minimal_degree_elimination_of_nonsingular_matrix`,
   `minimal_degree_elimination_of_int_shifts`,
   `minimal_degree_elimination_vandermonde`,
   `minimal_degree_elimination_twoSector_vandermonde`):**
   Over any `CharZero` integral domain `K` injectively embedded into a `CharZero` domain `B`,
   no nonzero minimal-total-degree annihilator `R` of a jet `V` can admit shifts whose
   derivative rows form a nonsingular matrix.
-/

public section

namespace CubicTheta.AllD

open Finset Matrix MvPolynomial Polynomial
open scoped BigOperators

/-! ### 1. Formal-Grading Triangular Substitution & Group Commutator -/

section TriangularCommutator

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

/-- Triangular substitution acting on lower generators `U : ι → R` and a depth-2 generator `V : R`:
`triSub A B C (U, V) = (fun α => U α + A α, V + ∑ α, B α * U α + C)`. -/
def triSub (A B : ι → R) (C : R) (p : (ι → R) × R) : (ι → R) × R :=
  (fun α => p.1 α + A α, p.2 + (∑ α : ι, B α * p.1 α) + C)

/-- Explicit inverse of `triSub A B C`: `triSub (-A) (-B) (-C + ∑ α, B α * A α)`. -/
def triSubInv (A B : ι → R) (C : R) : ((ι → R) × R) → ((ι → R) × R) :=
  triSub (-A) (-B) (-C + ∑ α : ι, B α * A α)

/-- Antisymmetric bilinear pairing produced by the group commutator of two triangular substitutions:
`G(A₁, B₁, A₂, B₂) = ∑ α, (A₂ α * B₁ α - A₁ α * B₂ α)`. -/
def commutatorPairing (A₁ B₁ A₂ B₂ : ι → R) : R :=
  ∑ α : ι, (A₂ α * B₁ α - A₁ α * B₂ α)

/-- Group commutator `S₁ ∘ S₂ ∘ S₁⁻¹ ∘ S₂⁻¹` of two triangular substitutions. -/
def triCommutator (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R) :
    ((ι → R) × R) → ((ι → R) × R) :=
  triSub A₁ B₁ C₁ ∘ triSub A₂ B₂ C₂ ∘ triSubInv A₁ B₁ C₁ ∘ triSubInv A₂ B₂ C₂

theorem triSub_zero : triSub (0 : ι → R) (0 : ι → R) (0 : R) = id := by
  funext ⟨U, V⟩
  apply Prod.ext
  · funext α; simp [triSub]
  · simp [triSub]

theorem triSub_comp (A₁ B₁ A₂ B₂ : ι → R) (C₁ C₂ : R) :
    triSub A₁ B₁ C₁ ∘ triSub A₂ B₂ C₂ =
      triSub (A₁ + A₂) (B₁ + B₂) (C₁ + C₂ + ∑ α : ι, B₁ α * A₂ α) := by
  funext ⟨U, V⟩
  apply Prod.ext
  · funext α; simp only [Function.comp_apply, triSub, Pi.add_apply]; ring
  · simp only [Function.comp_apply, triSub, Pi.add_apply]
    have h1 : (∑ α : ι, B₁ α * (U α + A₂ α)) =
        (∑ α : ι, B₁ α * U α) + ∑ α : ι, B₁ α * A₂ α := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun α _ => by ring
    have h2 : (∑ α : ι, (B₁ α + B₂ α) * U α) =
        (∑ α : ι, B₁ α * U α) + ∑ α : ι, B₂ α * U α := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun α _ => by ring
    rw [h1, h2]; ring

theorem triSub_comp_inv (A B : ι → R) (C : R) : triSub A B C ∘ triSubInv A B C = id := by
  rw [triSubInv, triSub_comp]
  have hC : C + (-C + ∑ α : ι, B α * A α) + ∑ α : ι, B α * (-A) α = 0 := by
    have hneg : (∑ α : ι, B α * (-A) α) = -∑ α : ι, B α * A α := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun α _ => by simp [Pi.neg_apply]
    rw [hneg]; ring
  rw [add_neg_cancel, add_neg_cancel, hC, triSub_zero]

theorem triSub_inv_comp (A B : ι → R) (C : R) : triSubInv A B C ∘ triSub A B C = id := by
  rw [triSubInv, triSub_comp]
  have hC : (-C + ∑ α : ι, B α * A α) + C + ∑ α : ι, (-B) α * A α = 0 := by
    have hneg : (∑ α : ι, (-B) α * A α) = -∑ α : ι, B α * A α := by
      rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun α _ => by simp [Pi.neg_apply]
    rw [hneg]; ring
  rw [neg_add_cancel, neg_add_cancel, hC, triSub_zero]

/-- Explicit two-sided inverse statement for `triSub A B C`. -/
theorem triSub_inv (A B : ι → R) (C : R) :
    Function.LeftInverse (triSub (-A) (-B) (-C + ∑ α : ι, B α * A α)) (triSub A B C) ∧
      Function.RightInverse (triSub (-A) (-B) (-C + ∑ α : ι, B α * A α)) (triSub A B C) :=
  ⟨fun p => congrFun (triSub_inv_comp A B C) p, fun p => congrFun (triSub_comp_inv A B C) p⟩

/-- `triSub A B C` packaged as an explicit bijection on `(ι → R) × R`. -/
def triSubEquiv (A B : ι → R) (C : R) : ((ι → R) × R) ≃ ((ι → R) × R) where
  toFun := triSub A B C
  invFun := triSubInv A B C
  left_inv := (triSub_inv A B C).1
  right_inv := (triSub_inv A B C).2

theorem commutatorPairing_eq (A₁ B₁ A₂ B₂ : ι → R) :
    commutatorPairing A₁ B₁ A₂ B₂ = ∑ α : ι, (A₂ α * B₁ α - A₁ α * B₂ α) := by
  rfl

theorem commutatorPairing_self_zero (A B : ι → R) : commutatorPairing A B A B = 0 := by
  exact Finset.sum_eq_zero fun α _ => by ring

theorem commutatorPairing_antisymm (A₁ B₁ A₂ B₂ : ι → R) :
    commutatorPairing A₂ B₂ A₁ B₁ = -commutatorPairing A₁ B₁ A₂ B₂ := by
  unfold commutatorPairing
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun α _ => by ring

/-- The group commutator `S₁ ∘ S₂ ∘ S₁⁻¹ ∘ S₂⁻¹` reduces identically to a pure depth-2 translation
by `commutatorPairing A₁ B₁ A₂ B₂`, cancelling both direct-pole constants `C₁, C₂`. -/
theorem triCommutator_eq_triSub (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R) :
    triCommutator A₁ B₁ C₁ A₂ B₂ C₂ =
      triSub 0 0 (commutatorPairing A₁ B₁ A₂ B₂) := by
  unfold triCommutator triSubInv
  rw [triSub_comp, triSub_comp, triSub_comp]
  have hA : A₁ + (A₂ + (-A₁ + -A₂)) = 0 := by
    funext α; simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; ring
  have hB : B₁ + (B₂ + (-B₁ + -B₂)) = 0 := by
    funext α; simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; ring
  have hC :
      C₁ + (C₂ + ((-C₁ + ∑ α : ι, B₁ α * A₁ α) + (-C₂ + ∑ α : ι, B₂ α * A₂ α) +
        ∑ α : ι, (-B₁) α * (-A₂) α) + ∑ α : ι, B₂ α * (-A₁ + -A₂) α) +
        ∑ α : ι, B₁ α * (A₂ + (-A₁ + -A₂)) α =
      commutatorPairing A₁ B₁ A₂ B₂ := by
    unfold commutatorPairing
    have hsum :
        (∑ α : ι, B₁ α * A₁ α) + (∑ α : ι, B₂ α * A₂ α) +
          (∑ α : ι, (-B₁) α * (-A₂) α) + (∑ α : ι, B₂ α * (-A₁ + -A₂) α) +
          (∑ α : ι, B₁ α * (A₂ + (-A₁ + -A₂)) α) =
        ∑ α : ι, (A₂ α * B₁ α - A₁ α * B₂ α) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by simp only [Pi.add_apply, Pi.neg_apply]; ring
    calc
      C₁ + (C₂ + ((-C₁ + ∑ α : ι, B₁ α * A₁ α) + (-C₂ + ∑ α : ι, B₂ α * A₂ α) +
        ∑ α : ι, (-B₁) α * (-A₂) α) + ∑ α : ι, B₂ α * (-A₁ + -A₂) α) +
        ∑ α : ι, B₁ α * (A₂ + (-A₁ + -A₂)) α
          = (∑ α : ι, B₁ α * A₁ α) + (∑ α : ι, B₂ α * A₂ α) +
            (∑ α : ι, (-B₁) α * (-A₂) α) + (∑ α : ι, B₂ α * (-A₁ + -A₂) α) +
            (∑ α : ι, B₁ α * (A₂ + (-A₁ + -A₂)) α) := by ring
      _ = ∑ α : ι, (A₂ α * B₁ α - A₁ α * B₂ α) := hsum
  rw [hA, hB, hC]

/-- The group commutator fixes every lower generator `U α` identically. -/
theorem triSub_commutator_lower (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R)
    (U : ι → R) (V : R) (α : ι) :
    (triCommutator A₁ B₁ C₁ A₂ B₂ C₂ (U, V)).1 α = U α := by
  rw [triCommutator_eq_triSub]; simp [triSub]

/-- The group commutator cancels `C₁, C₂` and translates `V` by the exact antisymmetric pairing
`∑ α, (A₂ α * B₁ α - A₁ α * B₂ α)`. -/
theorem triSub_commutator_depth2 (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R)
    (U : ι → R) (V : R) :
    (triCommutator A₁ B₁ C₁ A₂ B₂ C₂ (U, V)).2 =
      V + ∑ α : ι, (A₂ α * B₁ α - A₁ α * B₂ α) := by
  rw [triCommutator_eq_triSub]; simp [triSub, commutatorPairing]

/-- Setting `(A₁, B₁, C₁) = (A₂, B₂, C₂)` (i.e. `S = T`) annihilates the commutator shift. -/
theorem triSub_commutator_self_zero (A B : ι → R) (C : R) (U : ι → R) (V : R) :
    triCommutator A B C A B C (U, V) = (U, V) := by
  rw [triCommutator_eq_triSub, commutatorPairing_self_zero, triSub_zero, id_eq]

/-- Depth-1 product control: the group commutator fixes every product `U α * U β` of lower
generators identically. -/
theorem triSub_commutator_symmetric_product_zero (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R)
    (U : ι → R) (V : R) (α β : ι) :
    (triCommutator A₁ B₁ C₁ A₂ B₂ C₂ (U, V)).1 α *
        (triCommutator A₁ B₁ C₁ A₂ B₂ C₂ (U, V)).1 β =
      U α * U β := by
  rw [triSub_commutator_lower, triSub_commutator_lower]

/-- Iterating the group commutator `n` times translates `V` by `n * commutatorPairing A₁ B₁ A₂ B₂`
while fixing `U`. -/
theorem triCommutator_iterate (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R)
    (n : ℕ) (U : ι → R) (V : R) :
    (triCommutator A₁ B₁ C₁ A₂ B₂ C₂)^[n] (U, V) =
      (U, V + (n : R) * commutatorPairing A₁ B₁ A₂ B₂) := by
  induction n generalizing U V with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    have hstep : triCommutator A₁ B₁ C₁ A₂ B₂ C₂ (U, V) =
        (U, V + commutatorPairing A₁ B₁ A₂ B₂) := by
      rw [triCommutator_eq_triSub]
      apply Prod.ext
      · funext α; simp [triSub]
      · simp [triSub]
    rw [hstep, ih]
    refine Prod.ext rfl ?_
    push_cast; ring

/-- `triCommutator` packaged as a permutation (`Equiv.Perm`) of `(ι → R) × R`. -/
def triCommutatorEquiv (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R) :
    Equiv.Perm ((ι → R) × R) :=
  (triSubEquiv A₁ B₁ C₁) * (triSubEquiv A₂ B₂ C₂) *
    (triSubEquiv A₁ B₁ C₁)⁻¹ * (triSubEquiv A₂ B₂ C₂)⁻¹

theorem triCommutatorEquiv_apply (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R)
    (U : ι → R) (V : R) :
    triCommutatorEquiv A₁ B₁ C₁ A₂ B₂ C₂ (U, V) =
      (U, V + commutatorPairing A₁ B₁ A₂ B₂) := by
  have h : (triCommutatorEquiv A₁ B₁ C₁ A₂ B₂ C₂ : ((ι → R) × R) → ((ι → R) × R)) =
      triCommutator A₁ B₁ C₁ A₂ B₂ C₂ := rfl
  rw [h, triCommutator_eq_triSub]
  apply Prod.ext
  · funext α; simp [triSub]
  · simp [triSub]

/-- Every integer power `m : ℤ` of the group commutator fixes `U` and translates `V` by
`m * commutatorPairing A₁ B₁ A₂ B₂`. -/
theorem triCommutatorEquiv_zpow (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R)
    (m : ℤ) (U : ι → R) (V : R) :
    ((triCommutatorEquiv A₁ B₁ C₁ A₂ B₂ C₂) ^ m) (U, V) =
      (U, V + (m : R) * commutatorPairing A₁ B₁ A₂ B₂) := by
  let g := triCommutatorEquiv A₁ B₁ C₁ A₂ B₂ C₂
  have hnat : ∀ (n : ℕ) (U : ι → R) (V : R),
      (g ^ n) (U, V) = (U, V + (n : R) * commutatorPairing A₁ B₁ A₂ B₂) := by
    intro n; induction n with
    | zero => intro U V; simp
    | succ n ih =>
      intro U V
      rw [pow_succ, Equiv.Perm.mul_apply, triCommutatorEquiv_apply, ih]
      refine Prod.ext rfl ?_; push_cast; ring
  have hinv_nat : ∀ (n : ℕ) (U : ι → R) (V : R),
      ((g ^ n)⁻¹) (U, V) = (U, V - (n : R) * commutatorPairing A₁ B₁ A₂ B₂) := by
    intro n U V
    apply (g ^ n).injective
    rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply, hnat]
    refine Prod.ext rfl ?_; ring
  cases m with
  | ofNat n => simpa using hnat n U V
  | negSucc n =>
    rw [zpow_negSucc, hinv_nat]
    refine Prod.ext rfl ?_
    push_cast; ring

/-! ### 1B. Multi-Sector Triangular Commutator & Polynomial Algebra Lift -/

/-- Multi-sector triangular substitution acting simultaneously on flux sectors `ν : σ`. -/
def multiTriSub {σ : Type*} (A B : σ → ι → R) (C : σ → R)
    (p : (σ → ι → R) × (σ → R)) : (σ → ι → R) × (σ → R) :=
  (fun ν α => p.1 ν α + A ν α, fun ν => p.2 ν + (∑ α : ι, B ν α * p.1 ν α) + C ν)

/-- Explicit inverse of `multiTriSub A B C`. -/
def multiTriSubInv {σ : Type*} (A B : σ → ι → R) (C : σ → R) :
    ((σ → ι → R) × (σ → R)) → ((σ → ι → R) × (σ → R)) :=
  multiTriSub (-A) (-B) (fun ν => -C ν + ∑ α : ι, B ν α * A ν α)

/-- Group commutator of two multi-sector triangular substitutions. -/
def multiTriCommutator {σ : Type*} (A₁ B₁ : σ → ι → R) (C₁ : σ → R)
    (A₂ B₂ : σ → ι → R) (C₂ : σ → R) :
    ((σ → ι → R) × (σ → R)) → ((σ → ι → R) × (σ → R)) :=
  multiTriSub A₁ B₁ C₁ ∘ multiTriSub A₂ B₂ C₂ ∘ multiTriSubInv A₁ B₁ C₁ ∘ multiTriSubInv A₂ B₂ C₂

theorem multiTriSub_commutator_lower {σ : Type*} (A₁ B₁ : σ → ι → R) (C₁ : σ → R)
    (A₂ B₂ : σ → ι → R) (C₂ : σ → R) (U : σ → ι → R) (V : σ → R) (ν : σ) (α : ι) :
    (multiTriCommutator A₁ B₁ C₁ A₂ B₂ C₂ (U, V)).1 ν α = U ν α := by
  have h := triSub_commutator_lower (A₁ ν) (B₁ ν) (C₁ ν) (A₂ ν) (B₂ ν) (C₂ ν) (U ν) (V ν) α
  simpa [multiTriCommutator, multiTriSub, multiTriSubInv, triCommutator, triSub, triSubInv] using h

theorem multiTriSub_commutator_depth2 {σ : Type*} (A₁ B₁ : σ → ι → R) (C₁ : σ → R)
    (A₂ B₂ : σ → ι → R) (C₂ : σ → R) (U : σ → ι → R) (V : σ → R) (ν : σ) :
    (multiTriCommutator A₁ B₁ C₁ A₂ B₂ C₂ (U, V)).2 ν =
      V ν + commutatorPairing (A₁ ν) (B₁ ν) (A₂ ν) (B₂ ν) := by
  have h := triSub_commutator_depth2 (A₁ ν) (B₁ ν) (C₁ ν) (A₂ ν) (B₂ ν) (C₂ ν) (U ν) (V ν)
  simpa [multiTriCommutator, multiTriSub, multiTriSubInv, triCommutator, triSub, triSubInv,
    commutatorPairing] using h

/-- Algebra endomorphism of `R[V, (U_α)_{α ∈ ι}]` (`none` = depth-2 generator `V`,
`some α` = lower generator `U_α`) induced by `triSub A B C`. -/
noncomputable def triSubAlgHom (A B : ι → R) (C : R) :
    MvPolynomial (Option ι) R →ₐ[R] MvPolynomial (Option ι) R :=
  MvPolynomial.aeval fun x =>
    match x with
    | none => MvPolynomial.X none + (∑ α : ι, MvPolynomial.C (B α) * MvPolynomial.X (some α)) +
        MvPolynomial.C C
    | some α => MvPolynomial.X (some α) + MvPolynomial.C (A α)

/-- Group commutator algebra endomorphism `S₁ ∘ S₂ ∘ S₁⁻¹ ∘ S₂⁻¹` on `R[V, (U_α)]`. -/
noncomputable def triCommutatorAlgHom (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R) :
    MvPolynomial (Option ι) R →ₐ[R] MvPolynomial (Option ι) R :=
  (triSubAlgHom A₁ B₁ C₁).comp <|
    (triSubAlgHom A₂ B₂ C₂).comp <|
      (triSubAlgHom (-A₁) (-B₁) (-C₁ + ∑ α : ι, B₁ α * A₁ α)).comp
        (triSubAlgHom (-A₂) (-B₂) (-C₂ + ∑ α : ι, B₂ α * A₂ α))

theorem triSubAlgHom_comp (A₁ B₁ A₂ B₂ : ι → R) (C₁ C₂ : R) :
    (triSubAlgHom A₁ B₁ C₁).comp (triSubAlgHom A₂ B₂ C₂) =
      triSubAlgHom (A₁ + A₂) (B₁ + B₂) (C₁ + C₂ + ∑ α : ι, B₂ α * A₁ α) := by
  apply MvPolynomial.algHom_ext
  intro x
  cases x with
  | some α =>
    simp only [AlgHom.comp_apply, triSubAlgHom, MvPolynomial.aeval_X, map_add,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Pi.add_apply]
    ring
  | none =>
    simp only [AlgHom.comp_apply, triSubAlgHom, MvPolynomial.aeval_X, map_add, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Pi.add_apply]
    have h1 : (∑ α : ι, MvPolynomial.C (B₂ α) * (MvPolynomial.X (some α) + MvPolynomial.C (A₁ α))) =
        (∑ α : ι, MvPolynomial.C (B₂ α) * MvPolynomial.X (some α)) +
          ∑ α : ι, MvPolynomial.C (B₂ α) * MvPolynomial.C (A₁ α) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    have h2 : (∑ α : ι, (MvPolynomial.C (B₁ α) + MvPolynomial.C (B₂ α)) * MvPolynomial.X (some α)) =
        (∑ α : ι, MvPolynomial.C (B₁ α) * MvPolynomial.X (some α)) +
          (∑ α : ι, MvPolynomial.C (B₂ α) * MvPolynomial.X (some α)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by ring
    rw [h1, h2]; ring

/-- Contravariant group commutator on `R[V, (U_α)]`: fixes every lower generator `U_α` and shifts
`V` by `∑ α, (A₁ α * B₂ α - A₂ α * B₁ α)`. -/
theorem triCommutatorAlgHom_eq (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R) :
    triCommutatorAlgHom A₁ B₁ C₁ A₂ B₂ C₂ =
      triSubAlgHom 0 0 (∑ α : ι, (A₁ α * B₂ α - A₂ α * B₁ α)) := by
  unfold triCommutatorAlgHom
  rw [triSubAlgHom_comp, triSubAlgHom_comp, triSubAlgHom_comp]
  have hA : A₁ + (A₂ + (-A₁ + -A₂)) = 0 := by
    funext α; simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; ring
  have hB : B₁ + (B₂ + (-B₁ + -B₂)) = 0 := by
    funext α; simp only [Pi.add_apply, Pi.neg_apply, Pi.zero_apply]; ring
  have hC :
      C₁ + (C₂ + ((-C₁ + ∑ α : ι, B₁ α * A₁ α) + (-C₂ + ∑ α : ι, B₂ α * A₂ α) +
        ∑ α : ι, (-B₂) α * (-A₁) α) + ∑ α : ι, (-B₁ + -B₂) α * A₂ α) +
        ∑ α : ι, (B₂ + (-B₁ + -B₂)) α * A₁ α =
      ∑ α : ι, (A₁ α * B₂ α - A₂ α * B₁ α) := by
    have hsum :
        (∑ α : ι, B₁ α * A₁ α) + (∑ α : ι, B₂ α * A₂ α) +
          (∑ α : ι, (-B₂) α * (-A₁) α) + (∑ α : ι, (-B₁ + -B₂) α * A₂ α) +
          (∑ α : ι, (B₂ + (-B₁ + -B₂)) α * A₁ α) =
        ∑ α : ι, (A₁ α * B₂ α - A₂ α * B₁ α) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun α _ => by simp only [Pi.add_apply, Pi.neg_apply]; ring
    calc
      C₁ + (C₂ + ((-C₁ + ∑ α : ι, B₁ α * A₁ α) + (-C₂ + ∑ α : ι, B₂ α * A₂ α) +
        ∑ α : ι, (-B₂) α * (-A₁) α) + ∑ α : ι, (-B₁ + -B₂) α * A₂ α) +
        ∑ α : ι, (B₂ + (-B₁ + -B₂)) α * A₁ α
          = (∑ α : ι, B₁ α * A₁ α) + (∑ α : ι, B₂ α * A₂ α) +
            (∑ α : ι, (-B₂) α * (-A₁) α) + (∑ α : ι, (-B₁ + -B₂) α * A₂ α) +
            (∑ α : ι, (B₂ + (-B₁ + -B₂)) α * A₁ α) := by ring
      _ = ∑ α : ι, (A₁ α * B₂ α - A₂ α * B₁ α) := hsum
  rw [hA, hB, hC]

/-- Every polynomial purely in the lower generators `U_α` (including every symmetric product
`U_α * U_β`) is fixed identically by `triCommutatorAlgHom`. -/
theorem triCommutatorAlgHom_fixes_lower_poly (A₁ B₁ : ι → R) (C₁ : R) (A₂ B₂ : ι → R) (C₂ : R)
    (P : MvPolynomial ι R) :
    triCommutatorAlgHom A₁ B₁ C₁ A₂ B₂ C₂ (MvPolynomial.rename Option.some P) =
      MvPolynomial.rename Option.some P := by
  rw [triCommutatorAlgHom_eq]
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => rw [map_add, map_add, hP, hQ]
  | mul_X P α hP =>
    rw [map_mul, map_mul, hP, MvPolynomial.rename_X]
    simp [triSubAlgHom]

end TriangularCommutator

/-! ### 2. Exact Shifted Vandermonde & Two-Sector Block Determinant -/

section ShiftedVandermonde

variable {R : Type*} [CommRing R]

/-- Shifted Vandermonde matrix `((a + b_i)^j)_{i, j}` of size `(r + 1) × (r + 1)`. -/
def shiftedVandermonde {r : ℕ} (a : R) (b : Fin (r + 1) → R) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  Matrix.of fun i j => (a + b i) ^ (j : ℕ)

@[simp]
theorem shiftedVandermonde_apply {r : ℕ} (a : R) (b : Fin (r + 1) → R) (i j : Fin (r + 1)) :
    shiftedVandermonde a b i j = (a + b i) ^ (j : ℕ) := by
  rfl

theorem shiftedVandermonde_eq_vandermonde {r : ℕ} (a : R) (b : Fin (r + 1) → R) :
    shiftedVandermonde a b = Matrix.vandermonde (fun i => a + b i) := by
  ext i j; rfl

/-- Exact shifted Vandermonde determinant: `det ((a + b_i)^j) = ∏_{i < j} (b_j - b_i)`. -/
theorem shiftedVandermonde_det {r : ℕ} (a : R) (b : Fin (r + 1) → R) :
    (shiftedVandermonde a b).det =
      ∏ i : Fin (r + 1), ∏ j ∈ Finset.Ioi i, (b j - b i) := by
  rw [shiftedVandermonde_eq_vandermonde, Matrix.det_vandermonde]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by ring

/-- Over any integral domain `R`, pairwise distinct `b_i` give nonzero Vandermonde determinant. -/
theorem shiftedVandermonde_det_ne_zero [IsDomain R] {r : ℕ} (a : R)
    (b : Fin (r + 1) → R) (hb : Function.Injective b) :
    (shiftedVandermonde a b).det ≠ 0 := by
  rw [shiftedVandermonde_det]
  refine Finset.prod_ne_zero_iff.mpr fun i _ => Finset.prod_ne_zero_iff.mpr fun j hj => ?_
  have hij : i ≠ j := (Finset.mem_Ioi.mp hj).ne
  exact sub_ne_zero.mpr fun h => hij (hb h.symm)

/-- Scaling the rows of a shifted Vandermonde matrix by nonzero scalars preserves nonsingularity. -/
theorem scaledShiftedVandermonde_det_ne_zero [IsDomain R] {r : ℕ} (a : R)
    (b c : Fin (r + 1) → R) (hb : Function.Injective b) (hc : ∀ i, c i ≠ 0) :
    (Matrix.diagonal c * shiftedVandermonde a b).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hc i)
    (shiftedVandermonde_det_ne_zero a b hb)

/-- Block-diagonal two-sector Vandermonde matrix of size `2(r + 1) × 2(r + 1)` has strictly nonzero
determinant over any integral domain `R`. -/
theorem twoSector_blockVandermonde_det_ne_zero [IsDomain R] {r : ℕ}
    (a₀ a₁ : R) (b₀ b₁ c₀ c₁ : Fin (r + 1) → R)
    (hb₀ : Function.Injective b₀) (hb₁ : Function.Injective b₁)
    (hc₀ : ∀ i, c₀ i ≠ 0) (hc₁ : ∀ i, c₁ i ≠ 0) :
    (Matrix.fromBlocks
      (Matrix.diagonal c₀ * shiftedVandermonde a₀ b₀) 0
      0 (Matrix.diagonal c₁ * shiftedVandermonde a₁ b₁)).det ≠ 0 := by
  rw [Matrix.det_fromBlocks_zero₁₂]
  exact mul_ne_zero
    (scaledShiftedVandermonde_det_ne_zero a₀ b₀ c₀ hb₀ hc₀)
    (scaledShiftedVandermonde_det_ne_zero a₁ b₁ c₁ hb₁ hc₁)

end ShiftedVandermonde

/-! ### 3. Integer-Iterate Linearization & Minimal-Degree Elimination Criterion -/

section MinimalDegreeElimination

variable {K B : Type*} [CommRing K] [CommRing B] [Algebra K B]
variable {ι : Type*}

/-- Univariate polynomial `t ↦ R(V + t · W)` over `B`. -/
noncomputable def linearShiftPoly (V W : ι → B) (R : MvPolynomial ι K) : Polynomial B :=
  MvPolynomial.eval₂ (Polynomial.C.comp (algebraMap K B))
    (fun j => Polynomial.C (V j) + Polynomial.C (W j) * Polynomial.X) R

theorem linearShiftPoly_eval (V W : ι → B) (R : MvPolynomial ι K) (t : B) :
    (linearShiftPoly V W R).eval t = MvPolynomial.aeval (fun j => V j + t * W j) R := by
  unfold linearShiftPoly
  induction R using MvPolynomial.induction_on with
  | C k =>
    rw [MvPolynomial.eval₂_C, RingHom.comp_apply, Polynomial.eval_C, MvPolynomial.aeval_C]
  | add P Q hP hQ =>
    rw [MvPolynomial.eval₂_add, Polynomial.eval_add, hP, hQ, map_add]
  | mul_X P k hP =>
    rw [MvPolynomial.eval₂_mul, Polynomial.eval_mul, hP, MvPolynomial.eval₂_X,
      map_mul, MvPolynomial.aeval_X]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
    ring

theorem linearShiftPoly_eval_zero (V W : ι → B) (R : MvPolynomial ι K) :
    (linearShiftPoly V W R).eval 0 = MvPolynomial.aeval V R := by
  simpa using linearShiftPoly_eval V W R 0

section FiniteVars

variable [Fintype ι] [DecidableEq ι]

theorem derivative_linearShiftPoly_eval_zero (V W : ι → B) (R : MvPolynomial ι K) :
    (Polynomial.derivative (linearShiftPoly V W R)).eval 0 =
      ∑ j : ι, W j * MvPolynomial.aeval V (MvPolynomial.pderiv j R) := by
  induction R using MvPolynomial.induction_on with
  | C k => simp [linearShiftPoly]
  | add P Q hP hQ =>
    have hadd : linearShiftPoly V W (P + Q) = linearShiftPoly V W P + linearShiftPoly V W Q := by
      simp [linearShiftPoly]
    rw [hadd, map_add, Polynomial.eval_add, hP, hQ]
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  | mul_X P k hP =>
    have hmul : linearShiftPoly V W (P * MvPolynomial.X k) =
        linearShiftPoly V W P * (Polynomial.C (V k) + Polynomial.C (W k) * Polynomial.X) := by
      simp [linearShiftPoly]
    rw [hmul, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul, hP, linearShiftPoly_eval_zero]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      mul_zero, add_zero, Polynomial.derivative_C, zero_add,
      Polynomial.derivative_mul, Polynomial.derivative_X, mul_one, zero_mul,
      Derivation.leibniz, smul_eq_mul, map_add, map_mul, MvPolynomial.aeval_X,
      MvPolynomial.pderiv_X, Pi.single_apply, apply_ite (MvPolynomial.aeval V),
      map_one, map_zero, mul_add, Finset.sum_add_distrib]
    have hdiag :
        (∑ j : ι, W j * (MvPolynomial.aeval V P * if k = j then (1 : B) else 0)) =
          MvPolynomial.aeval V P * W k := by
      rw [Finset.sum_eq_single k]
      · simp [mul_comm]
      · intro j _ hjk; simp [Ne.symm hjk]
      · intro hnot; exact absurd (Finset.mem_univ k) hnot
    rw [hdiag, add_comm, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring

theorem linearShiftPoly_coeff_one (V W : ι → B) (R : MvPolynomial ι K) :
    (linearShiftPoly V W R).coeff 1 =
      ∑ j : ι, W j * MvPolynomial.aeval V (MvPolynomial.pderiv j R) := by
  have hder : (Polynomial.derivative (linearShiftPoly V W R)).eval 0 =
      (linearShiftPoly V W R).coeff 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]; simp
  rw [← hder, derivative_linearShiftPoly_eval_zero]

/-- Over a `CharZero` integral domain `B`, any polynomial vanishing on all `m : ℕ` is zero. -/
theorem poly_eq_zero_of_forall_nat_eval_eq_zero [IsDomain B] [CharZero B]
    (P : Polynomial B) (hP : ∀ m : ℕ, P.eval (m : B) = 0) : P = 0 := by
  classical
  by_contra hne
  let S : Finset B := (Finset.range (P.natDegree + 1)).image (Nat.cast : ℕ → B)
  have hcard : S.card = P.natDegree + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have hsub : S ⊆ P.roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨m, _, rfl⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot.def]
    exact hP m
  have hle1 : S.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
  have hle2 : P.roots.toFinset.card ≤ P.roots.card := Multiset.toFinset_card_le P.roots
  have hle3 : P.roots.card ≤ P.natDegree := Polynomial.card_roots' P
  omega

/-- If `R(V + m · W) = 0` for all `m : ℕ`, then `∑ j, W j * aeval V (pderiv j R) = 0`. -/
theorem linear_shift_deriv_eq_zero_of_forall_nat_shift [IsDomain B] [CharZero B]
    (V W : ι → B) (R : MvPolynomial ι K)
    (hshift : ∀ m : ℕ, MvPolynomial.aeval (fun j => V j + (m : B) * W j) R = 0) :
    ∑ j : ι, W j * MvPolynomial.aeval V (MvPolynomial.pderiv j R) = 0 := by
  have hP0 : linearShiftPoly V W R = 0 :=
    poly_eq_zero_of_forall_nat_eval_eq_zero _ fun m => by rw [linearShiftPoly_eval]; exact hshift m
  rw [← linearShiftPoly_coeff_one, hP0, Polynomial.coeff_zero]

/-- If `R(V + m · W) = 0` for all integer iterates `m : ℤ`, then
`∑ j, W j * aeval V (pderiv j R) = 0`. -/
theorem linear_shift_deriv_eq_zero_of_forall_int_shift [IsDomain B] [CharZero B]
    (V W : ι → B) (R : MvPolynomial ι K)
    (hshift : ∀ m : ℤ, MvPolynomial.aeval (fun j => V j + (m : B) * W j) R = 0) :
    ∑ j : ι, W j * MvPolynomial.aeval V (MvPolynomial.pderiv j R) = 0 :=
  linear_shift_deriv_eq_zero_of_forall_nat_shift V W R fun m => by simpa using hshift (m : ℤ)

/-- If the directional derivative rows form a nonsingular matrix `M` (`M.det ≠ 0`), then every
partial derivative evaluation `aeval V (pderiv j R)` vanishes. -/
theorem all_pderiv_aeval_eq_zero_of_det_ne_zero [IsDomain B]
    (V : ι → B) (R : MvPolynomial ι K) (M : Matrix ι ι B) (hdet : M.det ≠ 0)
    (hrows : ∀ i : ι, ∑ j : ι, M i j * MvPolynomial.aeval V (MvPolynomial.pderiv j R) = 0) :
    ∀ j : ι, MvPolynomial.aeval V (MvPolynomial.pderiv j R) = 0 := by
  let v : ι → B := fun j => MvPolynomial.aeval V (MvPolynomial.pderiv j R)
  have hMv : M *ᵥ v = 0 := by funext i; simpa [Matrix.mulVec, dotProduct, v] using hrows i
  have hv0 : v = 0 :=
    M.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
      (mem_nonZeroDivisors_of_ne_zero hdet) hMv
  intro j; exact congrFun hv0 j

/-- Over a `CharZero` integral domain `K`, any polynomial of positive total degree has a nonzero
partial derivative of strictly smaller total degree. -/
theorem exists_pderiv_ne_zero_and_totalDegree_lt [IsDomain K] [CharZero K]
    {R : MvPolynomial ι K} (hdeg : 0 < R.totalDegree) :
    ∃ j : ι, MvPolynomial.pderiv j R ≠ 0 ∧ (MvPolynomial.pderiv j R).totalDegree < R.totalDegree := by
  have hex : ∃ j : ι, MvPolynomial.pderiv j R ≠ 0 := by
    by_contra hall
    push Not at hall
    have hR_const : R = MvPolynomial.C (R.coeff 0) := by
      apply MvPolynomial.ext; intro m
      rw [MvPolynomial.coeff_C]
      by_cases hm : m = 0
      · subst hm; simp
      · simp only [Ne.symm hm, ↓reduceIte]
        obtain ⟨j, hj⟩ : ∃ j : ι, m j ≠ 0 := by
          by_contra h0; push Not at h0; exact hm (Finsupp.ext h0)
        have h0 := congrArg (fun f : MvPolynomial ι K => f.coeff (m - Finsupp.single j 1)) (hall j)
        simp only [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel hj] at h0
        have h0' : R.coeff m * (((m - Finsupp.single j (1 : ℕ)) j : K) + 1) = 0 := by simpa using h0
        have hnat : (((m - Finsupp.single j (1 : ℕ)) j : K) + 1) ≠ 0 := by
          exact_mod_cast Nat.succ_ne_zero ((m - Finsupp.single j (1 : ℕ)) j)
        exact (mul_eq_zero.mp h0').resolve_right hnat
    rw [hR_const, MvPolynomial.totalDegree_C] at hdeg
    exact lt_irrefl 0 hdeg
  obtain ⟨j, hj⟩ := hex
  refine ⟨j, hj, ?_⟩
  rw [MvPolynomial.totalDegree_eq]
  apply lt_of_le_of_lt (Finset.sup_le fun m hm => ?_) (Nat.pred_lt hdeg.ne')
  have hn := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hn
  have hs := MvPolynomial.le_totalDegree
    (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn))
  change ((m + Finsupp.single j 1).sum fun _ => id) ≤ _ at hs
  rw [← Finsupp.card_toMultiset, Finsupp.toMultiset_add, Finsupp.toMultiset_single] at hs
  simp at hs
  rw [Finsupp.card_toMultiset, Nat.pred_eq_sub_one]
  omega

/-- **Minimal-Degree Elimination Criterion (Nonsingular Matrix Form):**
No nonzero minimal-total-degree annihilator `R` of `V` over a `CharZero` domain `K` injectively
embedded in `B` can admit a nonsingular matrix `M` annihilating `(aeval V (pderiv j R))_j`. -/
theorem minimal_degree_elimination_of_nonsingular_matrix
    [IsDomain K] [CharZero K] [IsDomain B]
    (hinj : Function.Injective (algebraMap K B))
    (V : ι → B) (R : MvPolynomial ι K) (hR_ne : R ≠ 0) (hR_ann : MvPolynomial.aeval V R = 0)
    (hR_min : ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.aeval V Q = 0 →
      R.totalDegree ≤ Q.totalDegree)
    (M : Matrix ι ι B) (hdet : M.det ≠ 0)
    (hrows : ∀ i : ι, ∑ j : ι, M i j * MvPolynomial.aeval V (MvPolynomial.pderiv j R) = 0) :
    False := by
  have hdeg : 0 < R.totalDegree := by
    by_contra h0
    have hd0 : R.totalDegree = 0 := Nat.eq_zero_of_not_pos h0
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hd0
    rw [hC, MvPolynomial.aeval_C] at hR_ann
    have hc0 : R.coeff 0 = 0 := hinj (by simpa using hR_ann)
    exact hR_ne (by rw [hC, hc0, MvPolynomial.C_0])
  have hall := all_pderiv_aeval_eq_zero_of_det_ne_zero V R M hdet hrows
  obtain ⟨j, hj_ne, hj_lt⟩ := exists_pderiv_ne_zero_and_totalDegree_lt hdeg
  have hle := hR_min (MvPolynomial.pderiv j R) hj_ne (hall j)
  omega

/-- **Minimal-Degree Elimination Criterion (Integer-Iterate Commutator Shifts Form):**
If `R` has minimal total degree among nonzero annihilators of `V` and vanishes at all integer
translates `V + m · (M i)` along the rows of a nonsingular matrix `M`, then `False`. -/
theorem minimal_degree_elimination_of_int_shifts
    [IsDomain K] [CharZero K] [IsDomain B] [CharZero B]
    (hinj : Function.Injective (algebraMap K B))
    (V : ι → B) (R : MvPolynomial ι K) (hR_ne : R ≠ 0) (hR_ann : MvPolynomial.aeval V R = 0)
    (hR_min : ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.aeval V Q = 0 →
      R.totalDegree ≤ Q.totalDegree)
    (M : Matrix ι ι B) (hdet : M.det ≠ 0)
    (hshifts : ∀ i : ι, ∀ m : ℤ,
      MvPolynomial.aeval (fun j => V j + (m : B) * M i j) R = 0) :
    False :=
  minimal_degree_elimination_of_nonsingular_matrix hinj V R hR_ne hR_ann hR_min M hdet fun i =>
    linear_shift_deriv_eq_zero_of_forall_int_shift V (M i) R (hshifts i)

/-- **Shifted Vandermonde Elimination Theorem (Single Sector, Arbitrary Jet Order `r`).** -/
theorem minimal_degree_elimination_vandermonde
    [IsDomain K] [CharZero K] [IsDomain B]
    (hinj : Function.Injective (algebraMap K B))
    {r : ℕ} (a : B) (b c : Fin (r + 1) → B)
    (hb : Function.Injective b) (hc : ∀ i, c i ≠ 0)
    (V : Fin (r + 1) → B) (R : MvPolynomial (Fin (r + 1)) K)
    (hR_ne : R ≠ 0) (hR_ann : MvPolynomial.aeval V R = 0)
    (hR_min : ∀ Q : MvPolynomial (Fin (r + 1)) K, Q ≠ 0 → MvPolynomial.aeval V Q = 0 →
      R.totalDegree ≤ Q.totalDegree)
    (hrows : ∀ i : Fin (r + 1),
      ∑ j : Fin (r + 1), (c i * (a + b i) ^ (j : ℕ)) * MvPolynomial.aeval V (MvPolynomial.pderiv j R) = 0) :
    False := by
  refine minimal_degree_elimination_of_nonsingular_matrix hinj V R hR_ne hR_ann hR_min
    (Matrix.diagonal c * shiftedVandermonde a b)
    (scaledShiftedVandermonde_det_ne_zero a b c hb hc) fun i => ?_
  simpa [Matrix.diagonal_mul, shiftedVandermonde] using hrows i

/-- **Two-Sector Block Vandermonde Elimination Theorem (Joint Independence for `(V₀, V₁)`).** -/
theorem minimal_degree_elimination_twoSector_vandermonde
    [IsDomain K] [CharZero K] [IsDomain B]
    (hinj : Function.Injective (algebraMap K B))
    {r : ℕ} (a₀ a₁ : B) (b₀ b₁ c₀ c₁ : Fin (r + 1) → B)
    (hb₀ : Function.Injective b₀) (hb₁ : Function.Injective b₁)
    (hc₀ : ∀ i, c₀ i ≠ 0) (hc₁ : ∀ i, c₁ i ≠ 0)
    (V : Fin (r + 1) ⊕ Fin (r + 1) → B)
    (R : MvPolynomial (Fin (r + 1) ⊕ Fin (r + 1)) K)
    (hR_ne : R ≠ 0) (hR_ann : MvPolynomial.aeval V R = 0)
    (hR_min : ∀ Q : MvPolynomial (Fin (r + 1) ⊕ Fin (r + 1)) K,
      Q ≠ 0 → MvPolynomial.aeval V Q = 0 → R.totalDegree ≤ Q.totalDegree)
    (hrows₀ : ∀ i : Fin (r + 1),
      ∑ j : Fin (r + 1),
        (c₀ i * (a₀ + b₀ i) ^ (j : ℕ)) *
          MvPolynomial.aeval V (MvPolynomial.pderiv (Sum.inl j) R) = 0)
    (hrows₁ : ∀ i : Fin (r + 1),
      ∑ j : Fin (r + 1),
        (c₁ i * (a₁ + b₁ i) ^ (j : ℕ)) *
          MvPolynomial.aeval V (MvPolynomial.pderiv (Sum.inr j) R) = 0) :
    False := by
  let M := Matrix.fromBlocks
    (Matrix.diagonal c₀ * shiftedVandermonde a₀ b₀) 0
    0 (Matrix.diagonal c₁ * shiftedVandermonde a₁ b₁)
  refine minimal_degree_elimination_of_nonsingular_matrix hinj V R hR_ne hR_ann hR_min M
    (twoSector_blockVandermonde_det_ne_zero a₀ a₁ b₀ b₁ c₀ c₁ hb₀ hb₁ hc₀ hc₁) fun i => ?_
  rw [Fintype.sum_sum_type]
  cases i with
  | inl i =>
    simpa [M, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.diagonal_mul,
      shiftedVandermonde] using hrows₀ i
  | inr i =>
    simpa [M, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_mul,
      shiftedVandermonde] using hrows₁ i

/-- **Minimal-Degree Elimination Criterion over a `CharZero` Field `F`:**
Same conclusion as `minimal_degree_elimination_vandermonde`, discharging injectivity of
`algebraMap F D` automatically for any field `F` and nontrivial domain `D`. -/
theorem minimal_degree_elimination_field_vandermonde
    {F D : Type*} [Field F] [CharZero F] [CommRing D] [IsDomain D] [Algebra F D]
    {r : ℕ} (a : D) (b c : Fin (r + 1) → D)
    (hb : Function.Injective b) (hc : ∀ i, c i ≠ 0)
    (V : Fin (r + 1) → D) (R : MvPolynomial (Fin (r + 1)) F)
    (hR_ne : R ≠ 0) (hR_ann : MvPolynomial.aeval V R = 0)
    (hR_min : ∀ Q : MvPolynomial (Fin (r + 1)) F, Q ≠ 0 → MvPolynomial.aeval V Q = 0 →
      R.totalDegree ≤ Q.totalDegree)
    (hrows : ∀ i : Fin (r + 1),
      ∑ j : Fin (r + 1), (c i * (a + b i) ^ (j : ℕ)) *
        MvPolynomial.aeval V (MvPolynomial.pderiv j R) = 0) :
    False :=
  minimal_degree_elimination_vandermonde (RingHom.injective (algebraMap F D))
    a b c hb hc V R hR_ne hR_ann hR_min hrows

end FiniteVars

end MinimalDegreeElimination

end CubicTheta.AllD
