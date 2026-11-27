module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! A marked family of jets is algebraically independent whenever its
linear coefficient matrix has a unit determinant. The coefficient ring
may have zero divisors, as happens for germs of arbitrary functions. -/
public section
namespace CubicTheta
open MvPolynomial Matrix
noncomputable section

private theorem lower_degree {ι : Type*} (i : ι) (P : MvPolynomial ι ℂ)
    (h : 0 < P.totalDegree) : (pderiv i P).totalDegree < P.totalDegree := by
  classical
  rw [totalDegree_eq]
  apply lt_of_le_of_lt (Finset.sup_le fun m hm ↦ ?_) (Nat.pred_lt h.ne')
  have hn := MvPolynomial.mem_support_iff.mp hm
  rw [coeff_pderiv] at hn
  have hs := le_totalDegree (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn))
  change ((m + Finsupp.single i 1).sum fun _ ↦ id) ≤ _ at hs
  rw [← Finsupp.card_toMultiset,Finsupp.toMultiset_add,Finsupp.toMultiset_single] at hs
  simp at hs
  rw [Finsupp.card_toMultiset,Nat.pred_eq_sub_one]
  omega

private theorem all_partials_zero {ι : Type*} (P : MvPolynomial ι ℂ)
    (h : ∀ i, pderiv i P = 0) : P = C (P.coeff 0) := by
  classical
  apply MvPolynomial.coe_injective (σ := ι) (R := ℂ)
  apply MvPowerSeries.pderiv.ext
  · intro i; simp [MvPowerSeries.pderiv_coe,h]
  · simp; rfl

theorem independent_of_marked_jacobian {R σ ι : Type*} [CommRing R] [Nontrivial R] [Algebra ℂ R]
    [Fintype ι] [DecidableEq ι] (marks : ι → σ) (f : ι → MvPowerSeries σ R)
    (unit : IsUnit (Matrix.of (fun i j ↦ MvPowerSeries.coeff (Finsupp.single (marks i) 1) (f j))).det) :
    AlgebraicIndependent ℂ f := by
  classical
  let A : Matrix ι ι (MvPowerSeries σ R) := Matrix.of fun i j ↦ MvPowerSeries.pderiv (marks i) (f j)
  have hu : IsUnit A.det := by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    rw [RingHom.map_det]
    have he : A.map MvPowerSeries.constantCoeff =
        Matrix.of (fun i j ↦ MvPowerSeries.coeff (Finsupp.single (marks i) 1) (f j)) := by
      ext i j
      simp [A,← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,MvPowerSeries.coeff_pderiv]
    change IsUnit (A.map MvPowerSeries.constantCoeff).det
    rwa [he]
  let ev := MvPolynomial.aeval (R := ℂ) f
  have chain (P : MvPolynomial ι ℂ) (i : ι) :
      MvPowerSeries.pderiv (marks i) (ev P) = ∑ j, A i j * ev (pderiv j P) := by
    induction P using MvPolynomial.induction_on with
    | C c => simp [ev,MvPowerSeries.algebraMap_apply]
    | add p q hp hq => simp only [map_add,hp,hq,mul_add,Finset.sum_add_distrib]
    | mul_X p k hp =>
      simp only [map_mul,Derivation.leibniz,smul_eq_mul,hp,ev,aeval_X, map_add,
        pderiv_X,Pi.single_apply]
      simp only [mul_add,Finset.sum_add_distrib,← mul_assoc]
      simp [A,mul_comm,mul_left_comm,Finset.mul_sum]
  have stable {P : MvPolynomial ι ℂ} (hp : ev P=0) (j : ι) : ev (pderiv j P) = 0 := by
    have hz : A *ᵥ (fun k ↦ ev (pderiv k P)) = 0 := by
      funext i; simpa [hp,Matrix.mulVec,dotProduct] using (chain P i).symm
    exact congrFun (A.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hu.mem_nonZeroDivisors hz) j
  apply algebraicIndependent_iff.mpr
  intro P
  induction P using (measure fun P : MvPolynomial ι ℂ ↦ P.totalDegree).wf.induction with
  | h P ih =>
    intro hp
    have fromConst (hc : P = C (P.coeff 0)) : P = 0 := by
      have hh : algebraMap ℂ (MvPowerSeries σ R) (P.coeff 0) = 0 := by
        rw [← MvPolynomial.aeval_C f,← hc]; exact hp
      exact hc.trans (by rw [(algebraMap ℂ (MvPowerSeries σ R)).injective (hh.trans (map_zero _).symm),C_0])
    rcases Nat.eq_zero_or_pos P.totalDegree with he|he
    · exact fromConst (totalDegree_eq_zero_iff_eq_C.mp he)
    exact fromConst (all_partials_zero P fun i ↦ ih _ (lower_degree i P he) (stable hp i))
end
end CubicTheta
