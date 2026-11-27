module

public import PakStokes.MarkedJacobian
public import Mathlib.Algebra.MvPolynomial.Variables
import all PakStokes.MarkedJacobian

/-! Select an ordinary point of an implicit equation on the actual curve.
No separant is evaluated on an asymptotic background. -/
public section
namespace CubicTheta.Flow
open MvPolynomial
noncomputable section

private theorem partial_ne {P : MvPolynomial ℕ ℂ} {i : ℕ} (hi : i ∈ P.vars) :
    pderiv i P ≠ 0 := by
  obtain ⟨m,hm,hi⟩ := (mem_vars_iff_mem_support i).mp hi
  have h := Finsupp.mem_support_iff.mp hi
  intro hz
  have he := congrArg (fun f : MvPolynomial ℕ ℂ ↦ f.coeff (m-Finsupp.single i 1)) hz
  rw [coeff_pderiv,Finsupp.sub_add_single_one_cancel h] at he
  change _ = (0:ℂ) at he
  refine (mul_ne_zero (mem_support_iff.mp hm) ?_) he
  exact_mod_cast (Nat.succ_ne_zero (((m-Finsupp.single i 1 : ℕ →₀ ℕ)) i))

/-- For arbitrary observations y_i on a nonempty set, a nontrivial
polynomial relation has one with a top variable of nonzero sensitivity at
some observation. The index zero is allowed and handled by the caller. -/
theorem ordinary_relation {α : Type} (U : Set α) (ne : U.Nonempty) (y : ℕ → α → ℂ)
    (ex : ∃ P : MvPolynomial ℕ ℂ, P ≠ 0 ∧ ∀ x ∈ U, eval (fun i ↦ y i x) P=0) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n+1)) ℂ) (x : α), x ∈ U ∧
      eval (fun i : Fin (n+1) ↦ y i.val x) (pderiv (Fin.last n) Q) ≠ 0 ∧
      ∀ z ∈ U, eval (fun i : Fin (n+1) ↦ y i.val z) Q = 0 := by
  classical
  let rel (P : MvPolynomial ℕ ℂ) := P ≠ 0 ∧ ∀ x ∈ U, eval (fun i ↦ y i x) P = 0
  have hex : ∃ d : ℕ, ∃ P : MvPolynomial ℕ ℂ, P.totalDegree=d ∧ rel P := by
    obtain ⟨P,hp⟩ := ex; exact ⟨_,P,rfl,hp⟩
  obtain ⟨P,hd,hp⟩ := Nat.find_spec hex
  have vars : P.vars.Nonempty := by
    by_contra! hv
    have hc := vars_eq_empty_iff_eq_C.mp hv
    obtain ⟨x,hx⟩ := ne
    have hh := hp.2 x hx; rw [hc,eval_C] at hh
    exact hp.1 (hc.trans (by rw [hh,C_0]))
  let n := P.vars.max' vars
  have hn : n ∈ P.vars := Finset.max'_mem _ _
  obtain ⟨Q,hQ⟩ := exists_rename_eq_of_vars_subset_range P (Fin.val : Fin (n+1) → ℕ) Fin.val_injective
    (fun i hi ↦ ⟨⟨i,Nat.lt_succ_of_le (Finset.le_max' _ i hi)⟩,rfl⟩)
  have hpd : 0 < P.totalDegree := by
    by_contra! h
    have hc := totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero h)
    rw [hc,vars_C] at hn
    exact Finset.notMem_empty _ hn
  have low := CubicTheta.lower_degree n P hpd
  have notRel : ¬ rel (pderiv n P) := fun h ↦
    Nat.find_min hex (hd ▸ low) ⟨_,rfl,h⟩
  obtain ⟨x,hx,hS⟩ : ∃ x ∈ U, eval (fun i ↦ y i x) (pderiv n P) ≠ 0 := by
    by_contra! hz; exact notRel ⟨partial_ne hn,hz⟩
  refine ⟨n,Q,x,hx,?_,?_⟩
  · rw [← hQ] at hS
    have d := pderiv_rename (f := (Fin.val : Fin (n+1) → ℕ)) Fin.val_injective (Fin.last n) Q
    have hh := congrArg (eval (fun i ↦ y i x)) d
    rw [eval_rename] at hh
    exact fun he ↦ hS (hh.trans he)
  · intro z hz; have h := hp.2 z hz; rw [← hQ,eval_rename] at h; exact h
end
end CubicTheta.Flow
