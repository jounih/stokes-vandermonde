module

public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.Basic

/-! A scalar polynomial readout of a finite polynomial differential system
satisfies a nonzero autonomous equation. Only a neighborhood of one ordinary
point is needed; all elimination takes place in a polynomial ring. -/
public section
namespace CubicTheta.Flow
open Filter MvPolynomial
open scoped Topology
noncomputable section

theorem polynomial_chain {ι : Type} [Fintype ι] (P : MvPolynomial ι ℂ)
    (u v : ι → ℝ → ℂ) (x : ℝ) (hu : ∀ i, HasDerivAt (u i) (v i x) x) :
    HasDerivAt (fun p ↦ eval (fun i ↦ u i p) P)
      (∑ i, eval (fun j ↦ u j x) (pderiv i P)*v i x) x := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simpa [pderiv_C] using (hasDerivAt_const x a)
  | add P Q hP hQ => simpa only [map_add,add_mul,Finset.sum_add_distrib] using! hP.add hQ
  | mul_X P k hP =>
    have h := hP.mul (hu k)
    simp only [map_mul,eval_X,pderiv_mul,map_add,pderiv_X,Pi.single_apply,add_mul,Finset.sum_add_distrib]
    convert h using 1
    simp [Finset.mul_sum,mul_comm,mul_left_comm]

/-- Membership in the algebra of local polynomial functions of a finite state. -/
def Generated {ι : Type} (u : ι → ℝ → ℂ) (x : ℝ) (f : ℝ → ℂ) :=
  ∃ A : MvPolynomial ι ℂ, f =ᶠ[𝓝 x] fun p ↦ eval (fun i ↦ u i p) A

namespace Generated
variable {ι : Type} {u : ι → ℝ → ℂ} {x : ℝ} {f g : ℝ → ℂ}
theorem coord (i : ι) : Generated u x (u i) := ⟨X i,by simp⟩
theorem const (c : ℂ) : Generated u x (fun _ ↦ c) := ⟨C c,by simp⟩
theorem congr (h : Generated u x f) (e : f =ᶠ[𝓝 x] g) : Generated u x g := by
  obtain ⟨P,h⟩ := h; exact ⟨P,e.symm.trans h⟩
theorem add (h : Generated u x f) (k : Generated u x g) : Generated u x (f+g) := by
  obtain ⟨A,h⟩ := h; obtain ⟨B,k⟩ := k; exact ⟨A+B,by simpa using! h.add k⟩
theorem sub (h : Generated u x f) (k : Generated u x g) : Generated u x (f-g) := by
  obtain ⟨A,h⟩ := h; obtain ⟨B,k⟩ := k; exact ⟨A-B,by simpa using! h.sub k⟩
theorem mul (h : Generated u x f) (k : Generated u x g) : Generated u x (f*g) := by
  obtain ⟨A,h⟩ := h; obtain ⟨B,k⟩ := k; exact ⟨A*B,by simpa using! h.mul k⟩
theorem pow (h : Generated u x f) (n : ℕ) : Generated u x (f^n) := by
  obtain ⟨A,h⟩ := h; exact ⟨A^n,by filter_upwards [h] with p hp; simp [hp]⟩
theorem finsetSum {κ : Type*} (s : Finset κ) (f : κ → ℝ → ℂ) (h : ∀ i ∈ s, Generated u x (f i)) :
    Generated u x (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! (const (u := u) (x := x) 0)
  | insert i s hi ih => simpa [hi] using (h i (by simp)).add (ih (fun j hj ↦ h j (by simp [hj])))

theorem evalPoly {κ : Type} (v : κ → ℝ → ℂ) (hv : ∀ i, Generated u x (v i))
    (P : MvPolynomial κ ℂ) : Generated u x (fun p ↦ eval (fun i ↦ v i p) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using const (u := u) (x := x) a
  | add p q hp hq => simpa only [map_add] using! hp.add hq
  | mul_X p i hp => simpa only [map_mul,eval_X] using! hp.mul (hv i)

theorem deriv [Fintype ι] (h : Generated u x f)
    (smooth : ∀ᶠ p in 𝓝 x, ∀ i, DifferentiableAt ℝ (u i) p)
    (closed : ∀ i, Generated u x (_root_.deriv (u i))) :
    Generated u x (_root_.deriv f) := by
  classical
  obtain ⟨A,ha⟩ := h
  have g (i : ι) : Generated u x (fun p ↦ eval (fun j ↦ u j p) (pderiv i A)) := ⟨_,.rfl⟩
  apply (finsetSum Finset.univ _ (fun i _ ↦ (g i).mul (closed i))).congr
  filter_upwards [ha.eventuallyEq_nhds,smooth] with p hp hd
  simpa only [Finset.sum_apply,Pi.mul_apply] using
    ((polynomial_chain A u (fun i ↦ _root_.deriv (u i)) p (fun i ↦ (hd i).hasDerivAt)).deriv.symm.trans hp.deriv_eq.symm)
end Generated

theorem autonomous_readout {ι : Type} [Fintype ι] (u : ι → ℝ → ℂ) (x : ℝ) (f : ℝ → ℂ)
    (readout : Generated u x f)
    (smooth : ∀ᶠ p in 𝓝 x, ∀ i, DifferentiableAt ℝ (u i) p)
    (closed : ∀ i, Generated u x (deriv (u i))) :
    ∃ P : MvPolynomial (Fin (Fintype.card ι+1)) ℂ, P ≠ 0 ∧
      ∀ᶠ p in 𝓝 x, eval (fun i : Fin (Fintype.card ι+1) ↦ iteratedDeriv i.val f p) P = 0 := by
  classical
  have all (j : ℕ) : Generated u x (iteratedDeriv j f) := by
    induction j with
    | zero => simpa using readout
    | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv smooth closed
  choose jet hj using fun j : Fin (Fintype.card ι+1) ↦ all j.val
  have dep : ¬ AlgebraicIndependent ℂ jet := by
    intro hi
    have := hi.cardinalMk_le_trdeg
    simp [MvPolynomial.trdeg_of_isDomain,Cardinal.mk_fintype] at this
  rw [algebraicIndependent_iff] at dep
  push Not at dep
  obtain ⟨P,hz,hp⟩ := dep
  refine ⟨P,hp,?_⟩
  filter_upwards [Filter.eventually_all.mpr hj] with p he
  have hh := congrArg (eval (fun i ↦ u i p)) hz
  change (aeval (fun i ↦ u i p)) (bind₁ jet P) = 0 at hh
  rw [aeval_bind₁] at hh
  simpa only [he] using! hh
end
end CubicTheta.Flow
