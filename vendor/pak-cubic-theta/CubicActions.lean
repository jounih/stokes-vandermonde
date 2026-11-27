module

public import Mathlib.FieldTheory.NormalizedTrace
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! Exactly the squarefree indices give indecomposable cubic Stokes actions.
A normalized field trace kills every smaller action after twisting by √d. -/
public section
namespace CubicTheta
open Polynomial Algebra
noncomputable section

def cubicAction (n : ℕ) : ℝ := n * Real.sqrt n

private abbrev AlgReal := algebraicClosure ℚ ℝ

private def sqrtAlg (n : ℕ) : AlgReal :=
  ⟨Real.sqrt n, mem_algebraicClosure_iff'.mpr ⟨X^2 - C (n:ℚ),monic_X_pow_sub_C _ (by decide),
    by simp [Real.sq_sqrt (Nat.cast_nonneg n)]⟩⟩

private theorem trace_sqrt_zero (n : ℕ) (hn : ¬IsSquare n) :
    normalizedTrace ℚ AlgReal (sqrtAlg n) = 0 := by
  have irr : Irreducible (X^2 - C (n:ℚ)) := by
    apply irreducible_X_pow_sub_C_of_prime Nat.prime_two
    intro b hb
    exact hn (Rat.isSquare_natCast_iff.mp ⟨b,by rw [← sq,hb]⟩)
  have root : aeval (sqrtAlg n) (X^2 - C (n:ℚ)) = 0 := by
    apply Subtype.ext
    simp [sqrtAlg,Real.sq_sqrt (Nat.cast_nonneg n)]
  rw [normalizedTrace_minpoly,← minpoly.eq_of_irreducible_of_monic irr root
    (monic_X_pow_sub_C _ (by decide))]
  simp only [nextCoeff,natDegree_X_pow_sub_C]
  norm_num [coeff_sub,coeff_X_pow,coeff_C]

private theorem nonsquare_below {d m : ℕ} (hd : Squarefree d) (hm : 0 < m) (hlt : m < d) :
    ¬IsSquare (d*m) := by
  rintro ⟨b,hb⟩
  have hdiv : d ∣ b^2 := by rw [sq,← hb]; exact dvd_mul_right _ _
  obtain ⟨k,hk⟩ := (hd.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp hdiv
  have heq : d*m = d*(d*(k*k)) := by rw [hb,hk]; ring
  have he := Nat.eq_of_mul_eq_mul_left (by omega : 0 < d) heq
  exact (not_le_of_gt hlt) (Nat.le_of_dvd hm ⟨_,he⟩)

/-- Rational linear combinations of smaller positive actions cannot give the
squarefree target. Indices and coefficients may repeat and have either sign. -/
theorem squarefree_action_separation {ι : Type*} (s : Finset ι) (n : ι → ℕ) (c : ι → ℚ)
    {d : ℕ} (hd : Squarefree d) (hd0 : 0 < d) (hsmall : ∀ i ∈ s, 0 < n i ∧ n i < d) :
    ∑ i ∈ s, (c i:ℝ)*cubicAction (n i) ≠ cubicAction d := by
  intro eqn
  let b (i : ι) : ℚ := c i * (n i : ℚ)
  have eqR : ∑ i ∈ s, ((b i:ℚ):ℝ)*Real.sqrt (d*n i : ℕ) = (d:ℝ)^2 := by
    have h := congrArg (fun x : ℝ ↦ x*Real.sqrt d) eqn
    simp only [Finset.sum_mul,cubicAction] at h
    calc _ = ∑ i ∈ s, (c i:ℝ)*((n i:ℝ)*Real.sqrt (n i))*Real.sqrt d := by
           apply Finset.sum_congr rfl
           intro i _
           rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg d)]
           simp only [b,Rat.cast_mul,Rat.cast_natCast]; ring
         _ = _ := h.trans (by nlinarith [Real.sq_sqrt (Nat.cast_nonneg d)])
  have eqA : ∑ i ∈ s, (b i) • sqrtAlg (d*n i) = algebraMap ℚ AlgReal ((d:ℚ)^2) := by
    apply Subtype.ext
    simpa [Algebra.smul_def,sqrtAlg] using! eqR
  have h := congrArg (normalizedTrace ℚ AlgReal) eqA
  simp only [map_sum,map_smul,normalizedTrace_algebraMap_apply_eq_self] at h
  rw [Finset.sum_eq_zero (fun i hi ↦ by
    rw [trace_sqrt_zero _ (nonsquare_below hd (hsmall i hi).1 (hsmall i hi).2),smul_zero])] at h
  exact (pow_ne_zero 2 (by exact_mod_cast hd0.ne' : (d:ℚ) ≠ 0)) h.symm

/-- Consequently a grouped action has unique coordinates along the
squarefree directions. This permits exact integer keys for nonlinear products. -/
theorem squarefree_actions_independent :
    LinearIndependent ℚ (fun d : {n : ℕ // Squarefree n} ↦ cubicAction d.val) := by
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert d s smaller ih =>
    intro c eqn
    have hd : d ∉ s := fun h ↦ (lt_irrefl d) (smaller d h)
    rw [Finset.sum_insert hd] at eqn
    have cz : c d = 0 := by
      by_contra hn
      apply squarefree_action_separation s Subtype.val (fun i ↦ -(c d)⁻¹*c i)
        d.property (Nat.pos_of_ne_zero d.property.ne_zero)
        (fun i hi ↦ ⟨Nat.pos_of_ne_zero i.property.ne_zero,smaller i hi⟩)
      have hs : ∑ i ∈ s, c i • cubicAction i.val = -(c d • cubicAction d.val) :=
        eq_neg_of_add_eq_zero_right eqn
      calc _ = ((-(c d)⁻¹) • ∑ i ∈ s, c i • cubicAction i.val : ℝ) := by
             rw [Finset.smul_sum]
             apply Finset.sum_congr rfl
             intro i _
             simp [Algebra.smul_def,mul_assoc]
           _ = _ := by rw [hs,smul_neg,smul_smul]; simp [hn]
    rw [cz,zero_smul,zero_add] at eqn
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact cz
    · exact ih c eqn i hi

/-- Every positive index with a nontrivial square factor has an explicit
representation by copies of one strictly smaller action. -/
theorem nonsquarefree_action_repeats {d : ℕ} (hd : 0 < d) (hs : ¬Squarefree d) :
    ∃ m k : ℕ, 0 < m ∧ m < d ∧ 1 < k ∧ cubicAction d = (k:ℝ)^3*cubicAction m := by
  unfold Squarefree at hs
  push Not at hs
  obtain ⟨k,⟨m,he⟩,hk⟩ := hs
  have hk0 : k ≠ 0 := by rintro rfl; simp_all
  have hk2 : 1 < k := by
    have h : k ≠ 1 := by simpa [Nat.isUnit_iff] using hk
    omega
  have hm : 0 < m := by
    apply Nat.pos_of_ne_zero
    rintro rfl
    simp_all
  refine ⟨m,k,hm,?_,hk2,?_⟩
  · rw [he]; nlinarith [Nat.mul_le_mul_right m (show 2 ≤ k*k by nlinarith)]
  · rw [he]; simp only [cubicAction,Nat.cast_mul]
    rw [Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg k)),Real.sqrt_mul_self (Nat.cast_nonneg k)]
    ring

end
end CubicTheta
