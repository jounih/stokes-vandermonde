module

public import PakStokes.AllD.BesicovitchCore
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases

/-! # Wave 14: Square Partitions Split by Number of Parts Modulo `N` — Exact Differential Rank `N` & Periodic-Weight Rank Law

Unconditional Lean 4 formalization from Mathlib (zero placeholders, standard foundations only)
of Theorem 2.4 (`thm:torsion-residues`) and its periodic-weight and multiples-of-`d` corollaries:

1. **Squarefree Decomposition, Dirichlet Primes `p ≡ 1 (mod N)`, & Two-Ray Radicals:**
   - `squarefree_decomp_pos` & `modN_squarefree_rep`: every positive integer `n ≥ 1` decomposes as
     `n = b₀ * k^2` with `Squarefree b₀` and `1 ≤ k ≤ Nat.sqrt n`; every residue `h : Fin N`
     (`N ≥ 1`) is reached as `-b₀ * k^2 (mod N)` with `1 ≤ k ≤ Nat.sqrt N`.
   - `exists_inf_primes_modN_one`: via Dirichlet's theorem (`Nat.forall_exists_prime_gt_and_modEq`),
     for every `N ≥ 1`, squarefree `b₀`, and finite set `S : Finset ℕ`, there exist infinitely
     many primes `p ∉ S` with `p ≡ 1 (mod N)`, `Squarefree (b₀ * p)`, `b₀ * p ≡ b₀ (mod N)`,
     and `(b₀ * p) * k^2 ≡ b₀ * k^2 (mod N)`.
   - `sqrt_core_pos`, `sqrt_core_injective`, `sqrt_core_linearIndependent` (via
     `BesicovitchCore`), and `twoRay_exponent_injective`: unique two-ray exponent vectors for
     any `ℝ`-linearly independent pair of complex ray directions `(a₁, a₂)`.
2. **Formal Two-Ray Coordinate Ring `TwoRayRing K` & Exact `T_b ∂_{T_b}` Strong Induction on `k ≥ 1`:**
   - `eulerDeriv` (`T_b ∂_{T_b}` annihilating `K` and every coordinate `≠ T_b`) and `rayDerivX`
     (`∂_X` extending any `ℂ`-derivation `dK : Derivation ℂ K K`).
   - `squareModNCoeff`, `IsSquareModNWave`, `squareModNWave`: formal two-ray twisted
     square-partition wave series `H_h` (`h : Fin N`) with exact `[T_b^k]` coefficient
     `C * √b * ∑_{d ∣ k, b d² ≡ -h (mod N)} d`.
   - `squareModN_strong_induction` & `squareModN_wave_diff_indep`: strong induction on `k ≥ 1`
     using infinitely many Dirichlet primes `p ≡ 1 (mod N)` and root finiteness over the domain `K`,
     proving joint differential independence of `(H_0, ..., H_{N-1})` over `K`.
3. **General Differential-Algebra Kolchin Log-Derivative Transfer (`diffAlg_kolchin_logDeriv_indep`):**
   - Transcendence-degree proof lifting joint differential independence from `(H_0, ..., H_{N-1})`
     to any nonzero twisted products `(P_0, ..., P_{N-1})` satisfying
     `D (P h) = (c h * H h + B h) * P h` (`c h ≠ 0`) in any `K`-differential domain `(A, D)`.
4. **Invertible `N × N` DFT, Mod-`N` Part-Count Series `(A_0, ..., A_{N-1})`, Periodic-Weight Rank
   Law, & Multiples-of-`d` Corollary:**
   - `dftMatrix`, `dftInvMatrix`, `dftMatrix_mul_dftInvMatrix`, `dftMatrix_det_ne_zero`,
     `rootsOfUnity_filter`, `squareModN_parts_diff_indep`, and explicit `N = 2` Even vs. Odd
     square partitions (`squareEvenOdd_joint_diff_indep`).
   - `squarePeriodicWeights_diff_rank_eq` & `squarePeriodicWeights_linearIndep_diff_indep`: exact
     differential rank `Module.finrank ℂ (Submodule.span ℂ (Set.range w))` for arbitrary periodic
     weight functions `w_1, ..., w_s : ℕ → ℂ` with arbitrary periods.
   - `multInd_evalMatrix_det_eq_one`, `multInd_linearIndependent`, &
     `squareMultiplesOfD_diff_indep`: joint differential independence of the generating functions
     restricting the number of parts to multiples of `d_i` for any finite set of distinct `d_i ≥ 1`. -/

public section

namespace CubicTheta.AllD

open Finset Matrix MvPolynomial Polynomial Set
open scoped BigOperators Classical IntermediateField IntermediateField.algebraAdjoinAdjoin

noncomputable section

/-! ### 1. Squarefree Decomposition, Dirichlet Primes `p ≡ 1 (mod N)`, & Two-Ray Radicals -/

/-- Every positive integer `n ≥ 1` decomposes as `n = b₀ * k^2` with `Squarefree b₀`,
`1 ≤ k`, and `k ≤ Nat.sqrt n`. -/
theorem squarefree_decomp_pos {n : ℕ} (hn : 1 ≤ n) :
    ∃ b₀ k : ℕ, Squarefree b₀ ∧ 1 ≤ b₀ ∧ 1 ≤ k ∧ k ≤ Nat.sqrt n ∧ b₀ * k ^ 2 = n := by
  obtain ⟨c, k, hk_pos, hck⟩ := rfree_factorization (r := 2) (by decide) n hn
  have hsq : Squarefree c.val := (rfree_two_iff_squarefree c.val).mp c.property
  have hc_pos : 1 ≤ c.val := rfree_pos c.property
  have hmul : c.val * k ^ 2 = n := by rw [mul_comm]; exact hck
  have hk_le : k ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]
    calc k * k = k ^ 2 := (sq k).symm
      _ = 1 * k ^ 2 := (one_mul _).symm
      _ ≤ c.val * k ^ 2 := Nat.mul_le_mul_right (k ^ 2) hc_pos
      _ = n := hmul
  exact ⟨c.val, k, hsq, hc_pos, hk_pos, hk_le, hmul⟩

/-- Every residue `h : Fin N` (`N ≥ 1`) is represented as `-b₀ * k^2 (mod N)` with `b₀ : Core 2`
(`Squarefree b₀.val`) and `1 ≤ k ≤ Nat.sqrt N`. -/
theorem modN_squarefree_rep {N : ℕ} (_hN : 1 ≤ N) (h : Fin N) :
    ∃ (b₀ : Core 2) (k : ℕ),
      Squarefree b₀.val ∧ 1 ≤ k ∧ k ≤ Nat.sqrt N ∧
      ((b₀.val * k ^ 2 : ℕ) : ZMod N) = -((h.val : ℕ) : ZMod N) := by
  let n : ℕ := N - h.val
  have hn_pos : 1 ≤ n := by have := h.isLt; omega
  have hn_le : n ≤ N := Nat.sub_le N h.val
  obtain ⟨b₀, k, hsq, _, hk1, hkle, hmul⟩ := squarefree_decomp_pos hn_pos
  have hcore : RFree 2 b₀ := (rfree_two_iff_squarefree b₀).mpr hsq
  refine ⟨⟨b₀, hcore⟩, k, hsq, hk1, hkle.trans (Nat.sqrt_le_sqrt hn_le), ?_⟩
  rw [hmul]
  have hadd : n + h.val = N := Nat.sub_add_cancel (le_of_lt h.isLt)
  have hz : ((n + h.val : ℕ) : ZMod N) = 0 := by rw [hadd, ZMod.natCast_self]
  rw [Nat.cast_add] at hz
  exact eq_neg_of_add_eq_zero_left hz

/-- `ZMod N` version of `modN_squarefree_rep`: every residue class `z : ZMod N` (`N ≥ 1`) is
reached as `-b₀ * k^2` with `Squarefree b₀.val` and `1 ≤ k ≤ Nat.sqrt N`. -/
theorem modN_squarefree_rep_zmod {N : ℕ} (hN : 1 ≤ N) (z : ZMod N) :
    ∃ (b₀ : Core 2) (k : ℕ),
      Squarefree b₀.val ∧ 1 ≤ k ∧ k ≤ Nat.sqrt N ∧
      ((b₀.val * k ^ 2 : ℕ) : ZMod N) = -z := by
  have : NeZero N := ⟨by omega⟩
  let h : Fin N := ⟨z.val, ZMod.val_lt z⟩
  obtain ⟨b₀, k, hsq, hk1, hkle, hcong⟩ := modN_squarefree_rep hN h
  refine ⟨b₀, k, hsq, hk1, hkle, ?_⟩
  simpa [h, ZMod.natCast_zmod_val] using hcong

/-- **Dirichlet Primes `p ≡ 1 (mod N)` Preserving Squarefreeness & Congruence:**
For every `N ≥ 1`, every squarefree `b₀`, and every finite forbidden set `S : Finset ℕ`,
there are infinitely many primes `p ∉ S` with `p ≡ 1 [MOD N]`, `Squarefree (b₀ * p)`,
`b₀ * p ≡ b₀ [MOD N]`, and `(b₀ * p) * k^2 ≡ b₀ * k^2 [MOD N]` for all `k`. -/
theorem exists_inf_primes_modN_one {N : ℕ} (hN : 1 ≤ N) {b₀ : ℕ} (hb₀ : Squarefree b₀)
    (S : Finset ℕ) :
    {p : ℕ | p.Prime ∧ p ∉ S ∧ p ≡ 1 [MOD N] ∧ Squarefree (b₀ * p) ∧
      b₀ * p ≡ b₀ [MOD N] ∧ ∀ k : ℕ, (b₀ * p) * k ^ 2 ≡ b₀ * k ^ 2 [MOD N]}.Infinite := by
  intro hfin
  let B : ℕ := max (max b₀ (S.sup id)) (hfin.toFinset.sup id)
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq B (by omega : N ≠ 0) (Nat.coprime_one_left N)
  have hp_gt_b₀ : b₀ < p := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hp_gt
  have hp_not_S : p ∉ S := by
    intro hpS
    have hle : p ≤ S.sup id := Finset.le_sup (f := id) hpS
    have hleB : S.sup id ≤ B := (le_max_right _ _).trans (le_max_left _ _)
    omega
  have hb₀_pos : 0 < b₀ := Nat.pos_of_ne_zero hb₀.ne_zero
  have hnot_dvd : ¬ p ∣ b₀ := Nat.not_dvd_of_pos_of_lt hb₀_pos hp_gt_b₀
  have hcop : b₀.Coprime p := (hp_prime.coprime_iff_not_dvd.mpr hnot_dvd).symm
  have hsq_bp : Squarefree (b₀ * p) := by
    rw [← rfree_two_iff_squarefree] at hb₀ ⊢
    exact rfree_mul_of_coprime (by decide) hb₀ (rfree_of_prime (by decide) hp_prime) hcop
  have hbp_mod : b₀ * p ≡ b₀ [MOD N] := by
    simpa [mul_one] using Nat.ModEq.mul_left b₀ hp_mod
  have hbpk_mod : ∀ k : ℕ, (b₀ * p) * k ^ 2 ≡ b₀ * k ^ 2 [MOD N] := fun k ↦
    Nat.ModEq.mul_right (k ^ 2) hbp_mod
  have hp_mem : p ∈ hfin.toFinset :=
    hfin.mem_toFinset.mpr ⟨hp_prime, hp_not_S, hp_mod, hsq_bp, hbp_mod, hbpk_mod⟩
  have hp_le : p ≤ hfin.toFinset.sup id := Finset.le_sup (f := id) hp_mem
  have hleB : hfin.toFinset.sup id ≤ B := le_max_right _ _
  omega

/-- Every squarefree core `b : Core 2` has strictly positive square root `√b > 0`. -/
theorem sqrt_core_pos (b : Core 2) : 0 < Real.sqrt (b.val : ℝ) :=
  Real.sqrt_pos.mpr (Nat.cast_pos.mpr (rfree_pos b.property))

/-- Distinct squarefree positive integers have distinct real square roots. -/
theorem sqrt_core_injective : Function.Injective (fun b : Core 2 ↦ Real.sqrt (b.val : ℝ)) := by
  intro b₁ b₂ h
  have hsq := congrArg (· ^ 2) h
  rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
  exact Subtype.ext (by exact_mod_cast hsq)

/-- The square roots `{√b : b ∈ Core 2}` of squarefree positive integers are `ℚ`-linearly
independent in `ℝ` (directly from `BesicovitchCore`). -/
theorem sqrt_core_linearIndependent :
    LinearIndependent ℚ (fun b : Core 2 ↦ Real.sqrt (b.val : ℝ)) := by
  have h0 := besicovitch_rfree_linearIndependent 2 (by decide)
  convert h0 using 1
  funext b
  rw [Real.sqrt_eq_rpow]
  norm_num

/-- Coordinate variables of the two-ray formal transseries ring: `Sum.inl b` represents
`T_b = exp(-a₁ √b X)` on the positive-angle ray, and `Sum.inr b` represents
`S_b = exp(-a₂ √b X)` on the conjugate ray. -/
abbrev TwoRayVar := Core 2 ⊕ Core 2

/-- **Unique Two-Ray Exponent Vectors**: whenever the two ray directions `a₁, a₂ : ℂ` are
`ℝ`-linearly independent (for example `a` and `starRingEnd ℂ a` with `a.re ≠ 0, a.im ≠ 0`),
the additive exponent map `(TwoRayVar →₀ ℕ) → ℂ` sending `μ` to
`∑ b, μ(inl b) a₁ √b + ∑ b, μ(inr b) a₂ √b` is injective! -/
theorem twoRay_exponent_injective {a₁ a₂ : ℂ} (ha : LinearIndependent ℝ ![a₁, a₂]) :
    Function.Injective (fun μ : TwoRayVar →₀ ℕ ↦
      μ.sum fun u k ↦ match u with
        | Sum.inl b => (k : ℂ) * (a₁ * (Real.sqrt (b.val : ℝ) : ℂ))
        | Sum.inr b => (k : ℂ) * (a₂ * (Real.sqrt (b.val : ℝ) : ℂ))) := by
  intro μ₁ μ₂ heq
  let S : Finset TwoRayVar := μ₁.support ∪ μ₂.support
  let S₁ : Finset (Core 2) := S.preimage Sum.inl (fun _ _ _ _ h ↦ Sum.inl.inj h)
  let S₂ : Finset (Core 2) := S.preimage Sum.inr (fun _ _ _ _ h ↦ Sum.inr.inj h)
  let x₁ : ℝ := ∑ b ∈ S₁, (((μ₁ (Sum.inl b) : ℤ) - (μ₂ (Sum.inl b) : ℤ) : ℤ) : ℝ) *
    Real.sqrt (b.val : ℝ)
  let x₂ : ℝ := ∑ b ∈ S₂, (((μ₁ (Sum.inr b) : ℤ) - (μ₂ (Sum.inr b) : ℤ) : ℤ) : ℝ) *
    Real.sqrt (b.val : ℝ)
  have hsum_split (μ : TwoRayVar →₀ ℕ) (hsub : μ.support ⊆ S) :
      (μ.sum fun u k ↦ match u with
        | Sum.inl b => (k : ℂ) * (a₁ * (Real.sqrt (b.val : ℝ) : ℂ))
        | Sum.inr b => (k : ℂ) * (a₂ * (Real.sqrt (b.val : ℝ) : ℂ))) =
      ((∑ b ∈ S₁, (μ (Sum.inl b) : ℝ) * Real.sqrt (b.val : ℝ)) : ℂ) * a₁ +
      ((∑ b ∈ S₂, (μ (Sum.inr b) : ℝ) * Real.sqrt (b.val : ℝ)) : ℂ) * a₂ := by
    rw [Finsupp.sum]
    have hS : (∑ u ∈ μ.support, match u with
        | Sum.inl b => (μ u : ℂ) * (a₁ * (Real.sqrt (b.val : ℝ) : ℂ))
        | Sum.inr b => (μ u : ℂ) * (a₂ * (Real.sqrt (b.val : ℝ) : ℂ))) =
        ∑ u ∈ S, match u with
        | Sum.inl b => (μ u : ℂ) * (a₁ * (Real.sqrt (b.val : ℝ) : ℂ))
        | Sum.inr b => (μ u : ℂ) * (a₂ * (Real.sqrt (b.val : ℝ) : ℂ)) := by
      apply Finset.sum_subset hsub
      intro u _ hu
      have h0 : μ u = 0 := Finsupp.notMem_support_iff.mp hu
      cases u <;> simp [h0]
    rw [hS]
    have hpart : S = S₁.image Sum.inl ∪ S₂.image Sum.inr := by
      ext u
      cases u with
      | inl b => simp [S₁, S₂]
      | inr b => simp [S₁, S₂]
    have hdisj : Disjoint (S₁.image Sum.inl) (S₂.image Sum.inr) := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      obtain ⟨b₁, _, rfl⟩ := Finset.mem_image.mp hu1
      obtain ⟨b₂, _, h⟩ := Finset.mem_image.mp hu2
      cases h
    rw [hpart, Finset.sum_union hdisj,
        Finset.sum_image (fun _ _ _ _ h ↦ Sum.inl.inj h),
        Finset.sum_image (fun _ _ _ _ h ↦ Sum.inr.inj h)]
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    congr 1 <;> (apply Finset.sum_congr rfl; intro b _; ring)
  dsimp only at heq
  rw [hsum_split μ₁ Finset.subset_union_left, hsum_split μ₂ Finset.subset_union_right] at heq
  have hlin0 : x₁ • a₁ + x₂ • a₂ = 0 := by
    have hsub : (x₁ : ℂ) * a₁ + (x₂ : ℂ) * a₂ = 0 := by
      dsimp only [x₁, x₂]
      push_cast
      simp only [sub_mul, Finset.sum_sub_distrib, sub_mul]
      linear_combination heq
    simpa [Complex.real_smul] using hsub
  have hlin_vec : ∑ i : Fin 2, (![x₁, x₂] i) • (![a₁, a₂] i) = 0 := by
    simpa [Fin.sum_univ_two] using hlin0
  have hx := Fintype.linearIndependent_iff.mp ha ![x₁, x₂] hlin_vec
  have hx₁ : x₁ = 0 := hx 0
  have hx₂ : x₂ = 0 := hx 1
  have hq₁ : ∀ b ∈ S₁, μ₁ (Sum.inl b) = μ₂ (Sum.inl b) := by
    have hlinQ : ∑ b ∈ S₁, (((μ₁ (Sum.inl b) : ℤ) - (μ₂ (Sum.inl b) : ℤ) : ℤ) : ℚ) •
        Real.sqrt (b.val : ℝ) = 0 := by
      convert hx₁ using 1
      apply Finset.sum_congr rfl; intro b _
      rw [Rat.smul_def, Rat.cast_intCast]
    intro b hb
    have h0 := linearIndependent_iff'.mp sqrt_core_linearIndependent S₁ _ hlinQ b hb
    have hint : (μ₁ (Sum.inl b) : ℤ) - (μ₂ (Sum.inl b) : ℤ) = 0 := by exact_mod_cast h0
    omega
  have hq₂ : ∀ b ∈ S₂, μ₁ (Sum.inr b) = μ₂ (Sum.inr b) := by
    have hlinQ : ∑ b ∈ S₂, (((μ₁ (Sum.inr b) : ℤ) - (μ₂ (Sum.inr b) : ℤ) : ℤ) : ℚ) •
        Real.sqrt (b.val : ℝ) = 0 := by
      convert hx₂ using 1
      apply Finset.sum_congr rfl; intro b _
      rw [Rat.smul_def, Rat.cast_intCast]
    intro b hb
    have h0 := linearIndependent_iff'.mp sqrt_core_linearIndependent S₂ _ hlinQ b hb
    have hint : (μ₁ (Sum.inr b) : ℤ) - (μ₂ (Sum.inr b) : ℤ) = 0 := by exact_mod_cast h0
    omega
  ext u
  by_cases hu : u ∈ S
  · cases u with
    | inl b => exact hq₁ b (Finset.mem_preimage.mpr hu)
    | inr b => exact hq₂ b (Finset.mem_preimage.mpr hu)
  · have h1 : μ₁ u = 0 := Finsupp.notMem_support_iff.mp (fun h ↦ hu (Finset.mem_union_left _ h))
    have h2 : μ₂ u = 0 := Finsupp.notMem_support_iff.mp (fun h ↦ hu (Finset.mem_union_right _ h))
    rw [h1, h2]

/-- Any complex number `a` with `a.re ≠ 0` and `a.im ≠ 0` (such as `2π √(2π i / N)`) is
`ℝ`-linearly independent from its complex conjugate `starRingEnd ℂ a`. -/
theorem conj_rayDirections_linearIndependent {a : ℂ} (hre : a.re ≠ 0) (him : a.im ≠ 0) :
    LinearIndependent ℝ ![a, starRingEnd ℂ a] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.real_smul] at hc
  have hcre := congrArg Complex.re hc
  have hcim := congrArg Complex.im hc
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.conj_re, Complex.zero_re, Complex.add_im, Complex.mul_im, add_zero,
    Complex.conj_im, mul_neg, Complex.zero_im] at hcre hcim
  have hsum : (c 0 + c 1) * a.re = 0 := by linarith
  have hdiff : (c 0 - c 1) * a.im = 0 := by linarith
  have h1 : c 0 + c 1 = 0 := (mul_eq_zero.mp hsum).resolve_right hre
  have h2 : c 0 - c 1 = 0 := (mul_eq_zero.mp hdiff).resolve_right him
  intro i; fin_cases i <;> dsimp <;> linarith

/-! ### 2. Formal Two-Ray Coordinate Ring `TwoRayRing K` & Exact Derivations `T_b ∂_{T_b}`, `∂_X` -/

/-- Formal two-ray coordinate ring `K[[{T_b, S_b : b ∈ Core 2}]]` over any differential field `K`
containing `ℂ` (modeling convergent meromorphic germs in `X⁻¹` adjoined with all two-ray
squarefree exponentials `T_b = e^{-a₁ √b X}` and `S_b = e^{-a₂ √b X}`). -/
abbrev TwoRayRing (K : Type*) [CommRing K] := MvPowerSeries TwoRayVar K

section TwoRayDerivations

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- **Exact Euler Derivation `T_b ∂_{T_b}`** on `TwoRayRing K`: multiplies the `[μ]` coefficient
by `μ (Sum.inl b)`, annihilating the entire base field `K`, all other `T_{b'}` (`b' ≠ b`),
and the entire conjugate ray `S_{b'}`. -/
def eulerDeriv {K : Type*} [CommRing K] (b : Core 2) :
    Derivation K (TwoRayRing K) (TwoRayRing K) where
  toFun f := (fun μ ↦ ((μ (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff μ f : TwoRayRing K)
  map_add' f g := by
    ext μ
    change ((μ (Sum.inl b) : ℕ) : K) * (MvPowerSeries.coeff μ f + MvPowerSeries.coeff μ g) =
      ((μ (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff μ f +
        ((μ (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff μ g
    ring
  map_smul' c f := by
    ext μ
    change ((μ (Sum.inl b) : ℕ) : K) * (c * MvPowerSeries.coeff μ f) =
      c * (((μ (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff μ f)
    ring
  map_one_eq_zero' := by
    ext μ
    change ((μ (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff μ (1 : TwoRayRing K) = 0
    by_cases hμ : μ = 0
    · subst hμ; simp
    · rw [MvPowerSeries.coeff_one, ite_eq_right (fun h ↦ (hμ h).elim), mul_zero]
  leibniz' f g := by
    ext μ
    let df : TwoRayRing K := fun ν ↦ ((ν (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff ν f
    let dg : TwoRayRing K := fun ν ↦ ((ν (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff ν g
    change ((μ (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff μ (f * g) =
      MvPowerSeries.coeff μ (f * dg) + MvPowerSeries.coeff μ (g * df)
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul,
        Finset.mul_sum]
    have hswap : (∑ p ∈ Finset.antidiagonal μ, MvPowerSeries.coeff p.1 g *
          MvPowerSeries.coeff p.2 df) =
        ∑ p ∈ Finset.antidiagonal μ, MvPowerSeries.coeff p.1 df * MvPowerSeries.coeff p.2 g := by
      refine Finset.sum_nbij Prod.swap (fun p hp ↦ ?_) (fun _ _ _ _ h ↦ Prod.swap_injective h)
        (fun p hp ↦ ⟨p.swap, ?_, Prod.swap_swap p⟩) (fun p _ ↦ by dsimp; ring)
      · rw [Finset.mem_antidiagonal] at hp ⊢; rw [add_comm]; exact hp
      · rw [Finset.mem_coe, Finset.mem_antidiagonal] at hp ⊢; rw [add_comm]; exact hp
    rw [hswap, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hsum : p.1 + p.2 = μ := Finset.mem_antidiagonal.mp hp
    have hb : μ (Sum.inl b) = p.1 (Sum.inl b) + p.2 (Sum.inl b) := by
      rw [← hsum, Finsupp.add_apply]
    change ((μ (Sum.inl b) : ℕ) : K) * (MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) =
      MvPowerSeries.coeff p.1 f * (((p.2 (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff p.2 g) +
      (((p.1 (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff p.1 f) * MvPowerSeries.coeff p.2 g
    rw [hb, Nat.cast_add]
    ring

@[simp]
theorem eulerDeriv_coeff {K : Type*} [CommRing K] (b : Core 2) (f : TwoRayRing K)
    (μ : TwoRayVar →₀ ℕ) :
    MvPowerSeries.coeff μ (eulerDeriv b f) = ((μ (Sum.inl b) : ℕ) : K) * MvPowerSeries.coeff μ f := by
  unfold eulerDeriv; rfl

/-- Exact multivariate polynomial chain rule for any `K`-derivation `D : Derivation K A A`
applied to `MvPolynomial.aeval Y P`. -/
theorem deriv_aeval_eq_sum_pderiv {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [Fintype ι] (D : Derivation R A A) (Y : ι → A) (P : MvPolynomial ι R) :
    D (MvPolynomial.aeval Y P) =
      ∑ i : ι, MvPolynomial.aeval Y (MvPolynomial.pderiv i P) * D (Y i) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp [Derivation.map_algebraMap]
  | add p q hp hq =>
    simp only [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p k hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp, MvPolynomial.aeval_X,
      MvPolynomial.pderiv_X, Pi.single_apply, apply_ite (MvPolynomial.aeval Y),
      map_one, map_zero, map_add, add_mul, Finset.sum_add_distrib]
    have hdiag : (∑ i : ι, (MvPolynomial.aeval Y p * (if k = i then (1 : A) else 0)) * D (Y i)) =
        MvPolynomial.aeval Y p * D (Y k) := by
      have hterm : ∀ i : ι, (MvPolynomial.aeval Y p * (if k = i then (1 : A) else 0)) * D (Y i) =
          if k = i then MvPolynomial.aeval Y p * D (Y k) else 0 := by
        intro i; split_ifs with h <;> simp [h]
      simp_rw [hterm]
      simp
    rw [hdiag, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Coordinate decay rate `-a₁ √b` on the positive ray and `-a₂ √b` on the conjugate ray. -/
def twoRayRate (a₁ a₂ : ℂ) : TwoRayVar → ℂ
  | Sum.inl b => -a₁ * (Real.sqrt (b.val : ℝ) : ℂ)
  | Sum.inr b => -a₂ * (Real.sqrt (b.val : ℝ) : ℂ)

/-- Total additive exponent decay rate on a monomial `μ : TwoRayVar →₀ ℕ`. -/
def monRate (a₁ a₂ : ℂ) (μ : TwoRayVar →₀ ℕ) : ℂ :=
  μ.sum fun u k ↦ (k : ℂ) * twoRayRate a₁ a₂ u

theorem monRate_zero (a₁ a₂ : ℂ) : monRate a₁ a₂ 0 = 0 := by
  simp [monRate]

theorem monRate_single (a₁ a₂ : ℂ) (u : TwoRayVar) (k : ℕ) :
    monRate a₁ a₂ (Finsupp.single u k) = (k : ℂ) * twoRayRate a₁ a₂ u := by
  unfold monRate
  rw [Finsupp.sum_single_index (by simp)]

theorem monRate_add (a₁ a₂ : ℂ) (μ₁ μ₂ : TwoRayVar →₀ ℕ) :
    monRate a₁ a₂ (μ₁ + μ₂) = monRate a₁ a₂ μ₁ + monRate a₁ a₂ μ₂ := by
  unfold monRate
  rw [Finsupp.sum_add_index']
  · intro _; simp
  · intro _ _ _; push_cast; ring

/-- **Formal `X`-Derivation `∂_X` on `TwoRayRing K`** extending an arbitrary `ℂ`-derivation
`dK : Derivation ℂ K K` on the base field `K` and acting by `-a₁ √b` on `T_b` and `-a₂ √b`
on `S_b`. -/
def rayDerivX (dK : Derivation ℂ K K) (a₁ a₂ : ℂ) :
    Derivation ℂ (TwoRayRing K) (TwoRayRing K) where
  toFun f :=
    (fun μ ↦ dK (MvPowerSeries.coeff μ f) +
      algebraMap ℂ K (monRate a₁ a₂ μ) * MvPowerSeries.coeff μ f : TwoRayRing K)
  map_add' f g := by
    ext μ
    change dK (MvPowerSeries.coeff μ f + MvPowerSeries.coeff μ g) +
        algebraMap ℂ K (monRate a₁ a₂ μ) * (MvPowerSeries.coeff μ f + MvPowerSeries.coeff μ g) =
      (dK (MvPowerSeries.coeff μ f) + algebraMap ℂ K (monRate a₁ a₂ μ) * MvPowerSeries.coeff μ f) +
      (dK (MvPowerSeries.coeff μ g) + algebraMap ℂ K (monRate a₁ a₂ μ) * MvPowerSeries.coeff μ g)
    rw [map_add]
    ring
  map_smul' c f := by
    ext μ
    change dK (c • MvPowerSeries.coeff μ f) +
        algebraMap ℂ K (monRate a₁ a₂ μ) * (c • MvPowerSeries.coeff μ f) =
      c • (dK (MvPowerSeries.coeff μ f) +
        algebraMap ℂ K (monRate a₁ a₂ μ) * MvPowerSeries.coeff μ f)
    have hsmul : dK (c • MvPowerSeries.coeff μ f) = c • dK (MvPowerSeries.coeff μ f) :=
      dK.toLinearMap.map_smul c (MvPowerSeries.coeff μ f)
    rw [hsmul, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def]
    ring
  map_one_eq_zero' := by
    ext μ
    change dK (MvPowerSeries.coeff μ (1 : TwoRayRing K)) +
        algebraMap ℂ K (monRate a₁ a₂ μ) * MvPowerSeries.coeff μ (1 : TwoRayRing K) = 0
    by_cases hμ : μ = 0
    · subst hμ
      rw [MvPowerSeries.coeff_zero_one, monRate_zero, map_zero, zero_mul, add_zero,
          Derivation.map_one_eq_zero]
    · rw [MvPowerSeries.coeff_one, ite_eq_right (fun h ↦ (hμ h).elim), map_zero, mul_zero, add_zero]
  leibniz' f g := by
    ext μ
    let df : TwoRayRing K := fun ν ↦
      dK (MvPowerSeries.coeff ν f) + algebraMap ℂ K (monRate a₁ a₂ ν) * MvPowerSeries.coeff ν f
    let dg : TwoRayRing K := fun ν ↦
      dK (MvPowerSeries.coeff ν g) + algebraMap ℂ K (monRate a₁ a₂ ν) * MvPowerSeries.coeff ν g
    change dK (MvPowerSeries.coeff μ (f * g)) +
        algebraMap ℂ K (monRate a₁ a₂ μ) * MvPowerSeries.coeff μ (f * g) =
      MvPowerSeries.coeff μ (f * dg) + MvPowerSeries.coeff μ (g * df)
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul,
        map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    have hswap : (∑ p ∈ Finset.antidiagonal μ, MvPowerSeries.coeff p.1 g *
          MvPowerSeries.coeff p.2 df) =
        ∑ p ∈ Finset.antidiagonal μ, MvPowerSeries.coeff p.1 df * MvPowerSeries.coeff p.2 g := by
      refine Finset.sum_nbij Prod.swap (fun p hp ↦ ?_) (fun _ _ _ _ h ↦ Prod.swap_injective h)
        (fun p hp ↦ ⟨p.swap, ?_, Prod.swap_swap p⟩) (fun p _ ↦ by dsimp; ring)
      · rw [Finset.mem_antidiagonal] at hp ⊢; rw [add_comm]; exact hp
      · rw [Finset.mem_coe, Finset.mem_antidiagonal] at hp ⊢; rw [add_comm]; exact hp
    rw [hswap, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    have hsum : p.1 + p.2 = μ := Finset.mem_antidiagonal.mp hp
    change dK (MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) +
        algebraMap ℂ K (monRate a₁ a₂ μ) *
          (MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g) =
      MvPowerSeries.coeff p.1 f *
          (dK (MvPowerSeries.coeff p.2 g) +
            algebraMap ℂ K (monRate a₁ a₂ p.2) * MvPowerSeries.coeff p.2 g) +
        (dK (MvPowerSeries.coeff p.1 f) +
            algebraMap ℂ K (monRate a₁ a₂ p.1) * MvPowerSeries.coeff p.1 f) *
          MvPowerSeries.coeff p.2 g
    rw [← hsum, monRate_add, map_add, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring

@[simp]
theorem rayDerivX_coeff (dK : Derivation ℂ K K) (a₁ a₂ : ℂ) (f : TwoRayRing K)
    (μ : TwoRayVar →₀ ℕ) :
    MvPowerSeries.coeff μ (rayDerivX dK a₁ a₂ f) =
      dK (MvPowerSeries.coeff μ f) +
        algebraMap ℂ K (monRate a₁ a₂ μ) * MvPowerSeries.coeff μ f := by
  unfold rayDerivX; rfl

/-- `rayDerivX dK a₁ a₂` extends `dK` on the embedded base field `K`. -/
theorem rayDerivX_C (dK : Derivation ℂ K K) (a₁ a₂ : ℂ) (c : K) :
    rayDerivX dK a₁ a₂ (MvPowerSeries.C c) = MvPowerSeries.C (dK c) := by
  ext μ
  rw [rayDerivX_coeff, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  split_ifs with hμ
  · subst hμ; rw [monRate_zero, map_zero, zero_mul, add_zero]
  · simp

/-- `rayDerivX` never enlarges monomial support: if `coeff μ f = 0`, then
`coeff μ ((rayDerivX)^[j] f) = 0` for every `j : ℕ`. -/
theorem rayDerivX_iterate_coeff_eq_zero (dK : Derivation ℂ K K) (a₁ a₂ : ℂ) (f : TwoRayRing K)
    {μ : TwoRayVar →₀ ℕ} (h0 : MvPowerSeries.coeff μ f = 0) (j : ℕ) :
    MvPowerSeries.coeff μ ((rayDerivX dK a₁ a₂)^[j] f) = 0 := by
  induction j with
  | zero => exact h0
  | succ n ih =>
    rw [Function.iterate_succ_apply', rayDerivX_coeff, ih, map_zero, mul_zero, add_zero]

/-- On any monomial `μ` whose coefficient in `f` is a `ℂ`-constant `algebraMap ℂ K c`,
the `j`-th `∂_X`-jet multiplies that coefficient by `(monRate a₁ a₂ μ)^j`. -/
theorem rayDerivX_iterate_coeff_const (dK : Derivation ℂ K K) (a₁ a₂ : ℂ) (f : TwoRayRing K)
    (μ : TwoRayVar →₀ ℕ) (c : ℂ) (hc : MvPowerSeries.coeff μ f = algebraMap ℂ K c) (j : ℕ) :
    MvPowerSeries.coeff μ ((rayDerivX dK a₁ a₂)^[j] f) =
      algebraMap ℂ K ((monRate a₁ a₂ μ) ^ j * c) := by
  induction j with
  | zero => simp [hc]
  | succ n ih =>
    rw [Function.iterate_succ_apply', rayDerivX_coeff, ih, Derivation.map_algebraMap, zero_add,
        ← map_mul]
    congr 1
    rw [pow_succ']
    ring

end TwoRayDerivations

/-! ### 3. Twisted Square-Partition Wave Transseries & Codex's Strong Induction on `k ≥ 1` -/

/-- Exact positive-ray `[T_b^k]` coefficient in the twisted square-partition log-derivative `H_h`:
`c_h(b, k) = C * √b * ∑_{d ∣ k, b d² ≡ -h (mod N)} d`. -/
def squareModNCoeff (N : ℕ) (C : ℂ) (h : Fin N) (b : Core 2) (k : ℕ) : ℂ :=
  C * (Real.sqrt (b.val : ℝ) : ℂ) *
    ((∑ d ∈ k.divisors.filter (fun d ↦ ((b.val * d ^ 2 : ℕ) : ZMod N) = -(h.val : ZMod N)),
      d : ℕ) : ℂ)

/-- Predicate characterizing any formal two-ray family `H : Fin N → TwoRayRing K` carrying the
exact twisted square-partition positive-ray wave coefficients `squareModNCoeff N C h b k`
(allowing arbitrary base-field backgrounds in `K` at `μ = 0` and arbitrary conjugate-ray waves
on `Sum.inr`). -/
structure IsSquareModNWave {K : Type*} [Field K] [Algebra ℂ K] (N : ℕ) (C : ℂ)
    (H : Fin N → TwoRayRing K) : Prop where
  pure_pos_ray : ∀ (h : Fin N) (μ : TwoRayVar →₀ ℕ) (b : Core 2),
    μ (Sum.inl b) ≠ 0 → MvPowerSeries.coeff μ (H h) ≠ 0 →
      μ = Finsupp.single (Sum.inl b) (μ (Sum.inl b))
  coeff_pos_ray : ∀ (h : Fin N) (b : Core 2) (k : ℕ), 1 ≤ k →
    MvPowerSeries.coeff (Finsupp.single (Sum.inl b) k) (H h) =
      algebraMap ℂ K (squareModNCoeff N C h b k)

/-- Explicit canonical two-ray realization `squareModNWave N C bg c2 : Fin N → TwoRayRing K`
with background `bg h ∈ K`, positive-ray `[T_b^k]` amplitude `squareModNCoeff N C h b k`, and
conjugate-ray `[S_b^k]` amplitude `c2 h b k`. -/
def squareModNWave {K : Type*} [Field K] [Algebra ℂ K] (N : ℕ) (C : ℂ)
    (bg : Fin N → K) (c2 : Fin N → Core 2 → ℕ → ℂ) (h : Fin N) : TwoRayRing K :=
  fun μ ↦
    if μ = 0 then bg h
    else if h1 : ∃ b : Core 2, ∃ k : ℕ, 1 ≤ k ∧ μ = Finsupp.single (Sum.inl b) k then
      algebraMap ℂ K (squareModNCoeff N C h h1.choose h1.choose_spec.choose)
    else if h2 : ∃ b : Core 2, ∃ k : ℕ, 1 ≤ k ∧ μ = Finsupp.single (Sum.inr b) k then
      algebraMap ℂ K (c2 h h2.choose h2.choose_spec.choose)
    else 0

theorem isSquareModNWave_squareModNWave {K : Type*} [Field K] [Algebra ℂ K] (N : ℕ) (C : ℂ)
    (bg : Fin N → K) (c2 : Fin N → Core 2 → ℕ → ℂ) :
    IsSquareModNWave N C (squareModNWave N C bg c2) where
  pure_pos_ray := by
    intro h μ b hμb hne
    have hμ0 : μ ≠ 0 := by intro h0; subst h0; simp at hμb
    have hcoeff : MvPowerSeries.coeff μ (squareModNWave N C bg c2 h) =
        squareModNWave N C bg c2 h μ := rfl
    rw [hcoeff] at hne
    dsimp only [squareModNWave] at hne
    rw [ite_eq_right (fun h0 ↦ (hμ0 h0).elim)] at hne
    by_cases h1 : ∃ b' : Core 2, ∃ k : ℕ, 1 ≤ k ∧ μ = Finsupp.single (Sum.inl b') k
    · obtain ⟨b', k, hk1, hμeq⟩ := h1
      have hbb' : b' = b := by
        by_contra hne_b
        have : μ (Sum.inl b) = 0 := by
          rw [hμeq, Finsupp.single_eq_of_ne (fun e ↦ hne_b (Sum.inl.inj e).symm)]
        exact hμb this
      subst hbb'
      rw [hμeq, Finsupp.single_eq_same]
    · rw [dite_eq_right (fun h ↦ (h1 h).elim)] at hne
      by_cases h2 : ∃ b' : Core 2, ∃ k : ℕ, 1 ≤ k ∧ μ = Finsupp.single (Sum.inr b') k
      · obtain ⟨b', k, _, hμeq⟩ := h2
        exfalso
        have : μ (Sum.inl b) = 0 := by rw [hμeq, Finsupp.single_eq_of_ne (by simp)]
        exact hμb this
      · rw [dite_eq_right (fun h ↦ (h2 h).elim)] at hne
        exact (hne rfl).elim
  coeff_pos_ray := by
    intro h b k hk1
    let μ : TwoRayVar →₀ ℕ := Finsupp.single (Sum.inl b) k
    have hμ0 : μ ≠ 0 := by
      intro h0
      have := congrArg (fun f : TwoRayVar →₀ ℕ ↦ f (Sum.inl b)) h0
      simp [μ] at this
      omega
    have h1 : ∃ b' : Core 2, ∃ k' : ℕ, 1 ≤ k' ∧ μ = Finsupp.single (Sum.inl b') k' :=
      ⟨b, k, hk1, rfl⟩
    change squareModNWave N C bg c2 h μ = _
    dsimp only [squareModNWave]
    simp only [hμ0, ↓reduceIte, h1, ↓reduceDIte]
    set b' : Core 2 := h1.choose
    set k' : ℕ := h1.choose_spec.choose
    have hμeq : Finsupp.single (Sum.inl b) k = Finsupp.single (Sum.inl b') k' :=
      h1.choose_spec.choose_spec.2
    have hbb : b' = b := by
      by_contra hne
      have hev := congrArg (fun f : TwoRayVar →₀ ℕ ↦ f (Sum.inl b)) hμeq
      rw [Finsupp.single_eq_same,
          Finsupp.single_eq_of_ne (fun e ↦ hne (Sum.inl.inj e).symm)] at hev
      omega
    have hkk : k' = k := by
      have hev := congrArg (fun f : TwoRayVar →₀ ℕ ↦ f (Sum.inl b)) hμeq
      rw [Finsupp.single_eq_same, hbb, Finsupp.single_eq_same] at hev
      exact hev.symm
    change algebraMap ℂ K (squareModNCoeff N C h b' k') = _
    rw [hbb, hkk]

private theorem lower_totalDegree_field {K ι : Type*} [Field K] [CharZero K]
    (j : ι) (P : MvPolynomial ι K) (h : 0 < P.totalDegree) :
    (MvPolynomial.pderiv j P).totalDegree < P.totalDegree := by
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

private theorem eq_C_of_all_pderiv_zero_field {K ι : Type*} [Field K] [CharZero K]
    (P : MvPolynomial ι K) (h : ∀ j, MvPolynomial.pderiv j P = 0) :
    P = MvPolynomial.C (P.coeff 0) := by
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

/-- **Codex's Exact Strong Induction on `k ≥ 1` (`squareModN_strong_induction`):**
Given any differential polynomial `P` over `K` annihilating the `r`-jets of a twisted
square-partition wave family `H : Fin N → TwoRayRing K` (`C ≠ 0`, `a₁ ≠ 0`), every evaluated
partial derivative `A_{h, j} = ∂P/∂Z_{h, j}(H)` vanishes for every `h : Fin N` represented as
`-b₀ k^2 (mod N)` with `b₀ : Core 2` and `k ≥ 1`. -/
theorem squareModN_strong_induction {K : Type*} [Field K] [Algebra ℂ K]
    (dK : Derivation ℂ K K) {N : ℕ} (hN : 1 ≤ N)
    {C a₁ a₂ : ℂ} (hC : C ≠ 0) (ha₁ : a₁ ≠ 0)
    {H : Fin N → TwoRayRing K} (hH : IsSquareModNWave N C H)
    (r : ℕ) (P : MvPolynomial (Fin N × Fin (r + 1)) K)
    (hP : MvPolynomial.aeval (fun p : Fin N × Fin (r + 1) ↦
      (rayDerivX dK a₁ a₂)^[p.2.val] (H p.1)) P = 0) :
    ∀ k : ℕ, 1 ≤ k → ∀ (b₀ : Core 2) (h₀ : Fin N),
      ((b₀.val * k ^ 2 : ℕ) : ZMod N) = -(h₀.val : ZMod N) →
      ∀ j : Fin (r + 1),
        MvPolynomial.aeval (fun p : Fin N × Fin (r + 1) ↦
          (rayDerivX dK a₁ a₂)^[p.2.val] (H p.1)) (MvPolynomial.pderiv (h₀, j) P) = 0 := by
  have : NeZero N := ⟨by omega⟩
  let Y : Fin N × Fin (r + 1) → TwoRayRing K :=
    fun p ↦ (rayDerivX dK a₁ a₂)^[p.2.val] (H p.1)
  let A : Fin N → Fin (r + 1) → TwoRayRing K :=
    fun h j ↦ MvPolynomial.aeval Y (MvPolynomial.pderiv (h, j) P)
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk1 b₀ h₀ hcong₀
    -- If `h₀` was already reached by some strictly smaller `1 ≤ d < k`, the IH finishes immediately!
    by_cases hprev : ∃ d : ℕ, 1 ≤ d ∧ d < k ∧
        ((b₀.val * d ^ 2 : ℕ) : ZMod N) = -(h₀.val : ZMod N)
    · obtain ⟨d, hd1, hdlt, hcongd⟩ := hprev
      exact ih d hdlt hd1 b₀ h₀ hcongd
    · push Not at hprev
      -- Otherwise, fix an arbitrary monomial `ν` and prove `(A h₀ j).coeff ν = 0` for all `j`.
      suffices hcoeff_zero : ∀ (ν : TwoRayVar →₀ ℕ) (j : Fin (r + 1)),
          MvPowerSeries.coeff ν (A h₀ j) = 0 by
        intro j
        ext ν
        exact hcoeff_zero ν j
      intro ν
      -- Build the univariate polynomial `Q(X) = ∑_j ([ν] A_{h₀, j}) X^j ∈ K[X]`.
      let Q : Polynomial K :=
        ∑ j : Fin (r + 1), Polynomial.C (MvPowerSeries.coeff ν (A h₀ j)) * Polynomial.X ^ j.val
      -- Avoid all coordinates appearing in `ν` by taking `S` covering `b₀` and `ν.support`.
      let Bν : ℕ := ν.support.sup fun u ↦ match u with | Sum.inl c => c.val | Sum.inr _ => 0
      let S : Finset ℕ := Finset.Iic (max b₀.val Bν)
      have hb₀_sq : Squarefree b₀.val := (rfree_two_iff_squarefree b₀.val).mp b₀.property
      have hinf := exists_inf_primes_modN_one hN hb₀_sq S
      -- Every prime `p` in this infinite Dirichlet set yields a root `-a₁ k √(b₀ p)` of `Q`!
      have hroot : ∀ p ∈ {p : ℕ | p.Prime ∧ p ∉ S ∧ p ≡ 1 [MOD N] ∧ Squarefree (b₀.val * p) ∧
          b₀.val * p ≡ b₀.val [MOD N] ∧ ∀ m : ℕ, (b₀.val * p) * m ^ 2 ≡ b₀.val * m ^ 2 [MOD N]},
          Q.IsRoot (algebraMap ℂ K (-a₁ * (k : ℂ) * (Real.sqrt ((b₀.val * p : ℕ) : ℝ) : ℂ))) := by
        intro p hp
        rcases hp with ⟨hp_prime, hp_not_S, _, hsq_bp, hbp_mod, hbpk_mod⟩
        let b : Core 2 := ⟨b₀.val * p, (rfree_two_iff_squarefree _).mpr hsq_bp⟩
        have hp_gt : max b₀.val Bν < p := by
          by_contra hle
          exact hp_not_S (Finset.mem_Iic.mpr (not_lt.mp hle))
        have hνb : ν (Sum.inl b) = 0 := by
          by_contra hne
          have hmem : Sum.inl b ∈ ν.support := Finsupp.mem_support_iff.mpr hne
          have hle : b.val ≤ Bν := Finset.le_sup (f := fun u ↦ match u with
            | Sum.inl c => c.val | Sum.inr _ => 0) hmem
          have hb₀_pos : 1 ≤ b₀.val := rfree_pos b₀.property
          have hge : p ≤ b.val := by
            change p ≤ b₀.val * p
            nlinarith
          omega
        -- Apply `eulerDeriv b` (`T_b ∂_{T_b}`) to `aeval Y P = 0` and extract `[ν + k • e_b]`!
        have hchain : (∑ q : Fin N × Fin (r + 1),
            MvPolynomial.aeval Y (MvPolynomial.pderiv q P) * eulerDeriv b (Y q)) = 0 := by
          have h0 := deriv_aeval_eq_sum_pderiv (eulerDeriv b) Y P
          rw [hP, map_zero] at h0
          exact h0.symm
        let μ : TwoRayVar →₀ ℕ := ν + Finsupp.single (Sum.inl b) k
        have hsum0 : ∑ h : Fin N, ∑ j : Fin (r + 1),
            MvPowerSeries.coeff μ (A h j * eulerDeriv b (Y (h, j))) = 0 := by
          have hc := congrArg (MvPowerSeries.coeff μ) hchain
          rw [map_sum, map_zero, Fintype.sum_prod_type] at hc
          exact hc
        -- Helper: every pair `(μ₁, μ₂)` with `μ₁ + μ₂ = μ` collapses unless `h = h₀, μ₁ = ν, μ₂ = k e_b`!
        have hterm_eq (h : Fin N) (j : Fin (r + 1)) :
            MvPowerSeries.coeff μ (A h j * eulerDeriv b (Y (h, j))) =
            if h = h₀ then
              MvPowerSeries.coeff ν (A h₀ j) *
                (((k : ℕ) : K) * algebraMap ℂ K
                  ((-a₁ * (k : ℂ) * (Real.sqrt (b.val : ℝ) : ℂ)) ^ j.val *
                    (C * (Real.sqrt (b.val : ℝ) : ℂ) * (k : ℂ))))
            else 0 := by
          rw [MvPowerSeries.coeff_mul]
          have hvanish : ∀ pair ∈ Finset.antidiagonal μ,
              (h ≠ h₀ ∨ pair ≠ (ν, Finsupp.single (Sum.inl b) k)) →
              MvPowerSeries.coeff pair.1 (A h j) *
                MvPowerSeries.coeff pair.2 (eulerDeriv b (Y (h, j))) = 0 := by
            rintro ⟨μ₁, μ₂⟩ hpair hnot
            by_cases hE0 : MvPowerSeries.coeff μ₂ (eulerDeriv b (Y (h, j))) = 0
            · rw [hE0, mul_zero]
            · rw [eulerDeriv_coeff] at hE0
              have hμ₂b : μ₂ (Sum.inl b) ≠ 0 := by
                intro h0; exact hE0 (by simp [h0])
              have hY₂ : MvPowerSeries.coeff μ₂ (Y (h, j)) ≠ 0 := right_ne_zero_of_mul hE0
              have hH₂ : MvPowerSeries.coeff μ₂ (H h) ≠ 0 := fun h0 ↦
                hY₂ (rayDerivX_iterate_coeff_eq_zero dK a₁ a₂ (H h) h0 j.val)
              set s : ℕ := μ₂ (Sum.inl b)
              have hs1 : 1 ≤ s := Nat.pos_of_ne_zero hμ₂b
              have hμ₂_eq : μ₂ = Finsupp.single (Sum.inl b) s :=
                hH.pure_pos_ray h μ₂ b hμ₂b hH₂
              have hsum_pair : μ₁ + μ₂ = μ := Finset.mem_antidiagonal.mp hpair
              have hs_le : s ≤ k := by
                have hb_val := congrArg (fun f : TwoRayVar →₀ ℕ ↦ f (Sum.inl b)) hsum_pair
                simp only [μ, Finsupp.add_apply, hνb, zero_add, Finsupp.single_eq_same] at hb_val
                omega
              -- Since `coeff (single (inl b) s) (H h) ≠ 0`, some divisor `d ∣ s` satisfies `b d² ≡ -h`!
              rw [hμ₂_eq, hH.coeff_pos_ray h b s hs1] at hH₂
              have hc_ne : squareModNCoeff N C h b s ≠ 0 := fun h0 ↦ hH₂ (by simp [h0])
              have hfilt_ne : (s.divisors.filter (fun d ↦
                  ((b.val * d ^ 2 : ℕ) : ZMod N) = -(h.val : ZMod N))).Nonempty := by
                by_contra hemp
                rw [Finset.not_nonempty_iff_eq_empty] at hemp
                apply hc_ne
                unfold squareModNCoeff
                rw [hemp]
                simp
              obtain ⟨d, hd_mem⟩ := hfilt_ne
              obtain ⟨hd_div, hd_cong⟩ := Finset.mem_filter.mp hd_mem
              have hd_dvd : d ∣ s := (Nat.mem_divisors.mp hd_div).1
              have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd_dvd hs1
              have hd_le_s : d ≤ s := Nat.le_of_dvd hs1 hd_dvd
              have hd_cong0 : ((b₀.val * d ^ 2 : ℕ) : ZMod N) = -(h.val : ZMod N) := by
                have hm : ((b.val * d ^ 2 : ℕ) : ZMod N) = ((b₀.val * d ^ 2 : ℕ) : ZMod N) :=
                  (ZMod.natCast_eq_natCast_iff _ _ N).mpr (hbpk_mod d)
                rw [← hm, hd_cong]
              by_cases hlt : s < k
              · have hA0 : A h j = 0 := ih d (lt_of_le_of_lt hd_le_s hlt) hd_pos b₀ h hd_cong0 j
                rw [hA0, map_zero, zero_mul]
              · have hs_eq : s = k := by omega
                have hμ₂_k : μ₂ = Finsupp.single (Sum.inl b) k := hs_eq ▸ hμ₂_eq
                have hμ₁_eq : μ₁ = ν := by
                  have h1 : μ₁ + Finsupp.single (Sum.inl b) k = ν + Finsupp.single (Sum.inl b) k :=
                    calc μ₁ + Finsupp.single (Sum.inl b) k
                        = μ₁ + μ₂ := by rw [hμ₂_k]
                      _ = ν + Finsupp.single (Sum.inl b) k := hsum_pair
                  exact add_right_cancel h1
                have hh_ne : h ≠ h₀ := by
                  rcases hnot with hh | hpair_ne
                  · exact hh
                  · exact (hpair_ne (Prod.ext hμ₁_eq hμ₂_k)).elim
                have hd_lt_k : d < k := by
                  by_contra hge
                  have hdk : d = k := by omega
                  rw [hdk] at hd_cong0
                  have hz_eq : (h.val : ZMod N) = (h₀.val : ZMod N) := by
                    have := hd_cong0.symm.trans hcong₀
                    exact neg_inj.mp this
                  have hmod_eq : h.val % N = h₀.val % N :=
                    (ZMod.natCast_eq_natCast_iff _ _ N).mp hz_eq
                  rw [Nat.mod_eq_of_lt h.isLt, Nat.mod_eq_of_lt h₀.isLt] at hmod_eq
                  exact hh_ne (Fin.ext hmod_eq)
                have hA0 : A h j = 0 := ih d hd_lt_k hd_pos b₀ h hd_cong0 j
                rw [hA0, map_zero, zero_mul]
          by_cases hh : h = h₀
          · subst hh
            simp only [↓reduceIte]
            have hmem : (ν, Finsupp.single (Sum.inl b) k) ∈ Finset.antidiagonal μ :=
              Finset.mem_antidiagonal.mpr rfl
            rw [Finset.sum_eq_single (ν, Finsupp.single (Sum.inl b) k)
              (fun pair hp hne ↦ hvanish pair hp (Or.inr hne))
              (fun hnot ↦ absurd hmem hnot)]
            rw [eulerDeriv_coeff, Finsupp.single_eq_same]
            have hYj : MvPowerSeries.coeff (Finsupp.single (Sum.inl b) k) (Y (h, j)) =
                algebraMap ℂ K ((-a₁ * (k : ℂ) * (Real.sqrt (b.val : ℝ) : ℂ)) ^ j.val *
                  squareModNCoeff N C h b k) := by
              have h1 := rayDerivX_iterate_coeff_const dK a₁ a₂ (H h)
                (Finsupp.single (Sum.inl b) k) (squareModNCoeff N C h b k)
                (hH.coeff_pos_ray h b k hk1) j.val
              rw [monRate_single, twoRayRate] at h1
              convert h1 using 3
              ring
            -- At `h = h₀`, the divisor filter `{d ∣ k | b d² ≡ -h₀}` is the singleton `{k}`!
            have hfilt_eq : k.divisors.filter
                (fun d ↦ ((b.val * d ^ 2 : ℕ) : ZMod N) = -(h.val : ZMod N)) = {k} := by
              ext d
              simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
              constructor
              · rintro ⟨⟨hdvd, hk0⟩, hcd⟩
                have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos hdvd hk1
                have hdle : d ≤ k := Nat.le_of_dvd hk1 hdvd
                by_contra hne
                have hm : ((b.val * d ^ 2 : ℕ) : ZMod N) = ((b₀.val * d ^ 2 : ℕ) : ZMod N) :=
                  (ZMod.natCast_eq_natCast_iff _ _ N).mpr (hbpk_mod d)
                exact hprev d hd1 (lt_of_le_of_ne hdle hne) (hm.symm.trans hcd)
              · intro hdk
                subst hdk
                refine ⟨⟨dvd_refl d, by omega⟩, ?_⟩
                have hm : ((b.val * d ^ 2 : ℕ) : ZMod N) = ((b₀.val * d ^ 2 : ℕ) : ZMod N) :=
                  (ZMod.natCast_eq_natCast_iff _ _ N).mpr (hbpk_mod d)
                exact hm.trans hcong₀
            have hsqC : squareModNCoeff N C h b k = C * (Real.sqrt (b.val : ℝ) : ℂ) * (k : ℂ) := by
              unfold squareModNCoeff
              rw [hfilt_eq]
              simp
            rw [hYj, hsqC]
          · simp only [hh, ↓reduceIte]
            exact Finset.sum_eq_zero fun pair hp ↦ hvanish pair hp (Or.inl hh)
        simp_rw [hterm_eq] at hsum0
        rw [Finset.sum_eq_single h₀
          (fun h _ hne ↦ Finset.sum_eq_zero fun j _ ↦ by simp [hne])
          (fun hnot ↦ (hnot (Finset.mem_univ h₀)).elim)] at hsum0
        simp only [↓reduceIte] at hsum0
        -- Factor out `C * k^2 * √b ≠ 0`!
        let factor : K := algebraMap ℂ K (C * (Real.sqrt (b.val : ℝ) : ℂ) * ((k : ℂ) ^ 2))
        have hfactor_ne : factor ≠ 0 := by
          have hc0 : C * (Real.sqrt (b.val : ℝ) : ℂ) * ((k : ℂ) ^ 2) ≠ 0 := by
            refine mul_ne_zero (mul_ne_zero hC ?_) (pow_ne_zero 2 (Nat.cast_ne_zero.mpr (by omega)))
            exact Complex.ofReal_ne_zero.mpr (sqrt_core_pos b).ne'
          exact (map_ne_zero_iff (algebraMap ℂ K) (RingHom.injective _)).mpr hc0
        have hfac_sum : factor *
            Q.eval (algebraMap ℂ K (-a₁ * (k : ℂ) * (Real.sqrt (b.val : ℝ) : ℂ))) = 0 := by
          rw [← hsum0]
          dsimp only [Q, factor]
          rw [← Polynomial.coe_evalRingHom, map_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C,
            Polynomial.eval_X, map_mul, map_pow, map_natCast]
          ring
        exact (mul_eq_zero.mp hfac_sum).resolve_left hfactor_ne
      -- The root map `p ↦ algebraMap ℂ K (-a₁ k √(b₀ p))` is injective on `ℕ`, giving infinitely
      -- many roots of `Q` in the field `K`, forcing `Q = 0`!
      let rootOf : ℕ → K := fun p ↦
        algebraMap ℂ K (-a₁ * (k : ℂ) * (Real.sqrt ((b₀.val * p : ℕ) : ℝ) : ℂ))
      have hrootOf_inj : Function.Injective rootOf := by
        intro p₁ p₂ h
        have hC_eq : -a₁ * (k : ℂ) * (Real.sqrt ((b₀.val * p₁ : ℕ) : ℝ) : ℂ) =
            -a₁ * (k : ℂ) * (Real.sqrt ((b₀.val * p₂ : ℕ) : ℝ) : ℂ) :=
          (RingHom.injective (algebraMap ℂ K)) h
        have hscale : -a₁ * (k : ℂ) ≠ 0 :=
          mul_ne_zero (neg_ne_zero.mpr ha₁) (Nat.cast_ne_zero.mpr (by omega))
        have hsqrtC := mul_left_cancel₀ hscale hC_eq
        have hsqrtR : Real.sqrt ((b₀.val * p₁ : ℕ) : ℝ) = Real.sqrt ((b₀.val * p₂ : ℕ) : ℝ) :=
          Complex.ofReal_injective hsqrtC
        have hsq := congrArg (· ^ 2) hsqrtR
        rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
        have hnat : b₀.val * p₁ = b₀.val * p₂ := by exact_mod_cast hsq
        exact Nat.eq_of_mul_eq_mul_left (rfree_pos b₀.property) hnat
      have hQ0 : Q = 0 := by
        by_contra hQne
        have hsub : rootOf '' {p : ℕ | p.Prime ∧ p ∉ S ∧ p ≡ 1 [MOD N] ∧ Squarefree (b₀.val * p) ∧
            b₀.val * p ≡ b₀.val [MOD N] ∧ ∀ m : ℕ, (b₀.val * p) * m ^ 2 ≡ b₀.val * m ^ 2 [MOD N]} ⊆
            (Q.roots.toFinset : Set K) := by
          rintro x ⟨p, hp, rfl⟩
          exact Finset.mem_coe.mpr (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQne).mpr (hroot p hp)))
        exact (hinf.image hrootOf_inj.injOn) ((Q.roots.toFinset.finite_toSet).subset hsub)
      intro j
      have hcj := congrArg (Polynomial.lcoeff K j.val) hQ0
      rw [map_zero] at hcj
      dsimp only [Q] at hcj
      rw [map_sum] at hcj
      simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow] at hcj
      rw [Finset.sum_eq_single j] at hcj
      · simpa using hcj
      · intro j' _ hne
        exact ite_eq_right (fun e ↦ (hne (Fin.ext e.symm)).elim)
      · intro hnot; exact (hnot (Finset.mem_univ j)).elim

/-- **Bounded-Order Joint Differential Independence of Twisted Square-Partition Waves**
(`Fin N × Fin (r + 1)` over `K`). -/
theorem squareModN_wave_diff_indep_fin {K : Type*} [Field K] [Algebra ℂ K]
    (dK : Derivation ℂ K K) {N : ℕ} (hN : 1 ≤ N)
    {C a₁ a₂ : ℂ} (hC : C ≠ 0) (ha₁ : a₁ ≠ 0)
    {H : Fin N → TwoRayRing K} (hH : IsSquareModNWave N C H) (r : ℕ) :
    AlgebraicIndependent K
      (fun p : Fin N × Fin (r + 1) ↦ (rayDerivX dK a₁ a₂)^[p.2.val] (H p.1)) := by
  have : CharZero K := charZero_of_injective_algebraMap (RingHom.injective (algebraMap ℂ K))
  let Y : Fin N × Fin (r + 1) → TwoRayRing K :=
    fun p ↦ (rayDerivX dK a₁ a₂)^[p.2.val] (H p.1)
  have hstable : ∀ P : MvPolynomial (Fin N × Fin (r + 1)) K,
      MvPolynomial.aeval Y P = 0 →
      ∀ q : Fin N × Fin (r + 1), MvPolynomial.aeval Y (MvPolynomial.pderiv q P) = 0 := by
    intro P hP ⟨h₀, j⟩
    obtain ⟨b₀, k, _, hk1, _, hcong⟩ := modN_squarefree_rep hN h₀
    exact squareModN_strong_induction dK hN hC ha₁ hH r P hP k hk1 b₀ h₀ hcong j
  apply algebraicIndependent_iff.mpr
  intro P
  induction P using (measure fun P : MvPolynomial (Fin N × Fin (r + 1)) K ↦ P.totalDegree).wf.induction with
  | h P ih =>
    intro hP
    have fromConst (hc : P = MvPolynomial.C (P.coeff 0)) : P = 0 := by
      have h1 : MvPolynomial.aeval Y (MvPolynomial.C (P.coeff 0)) = 0 := hc ▸ hP
      have h2 : MvPowerSeries.C (P.coeff 0) = (0 : TwoRayRing K) := by
        simpa [MvPowerSeries.algebraMap_apply] using h1
      have hc0 : P.coeff 0 = 0 := by
        have := congrArg (MvPowerSeries.coeff 0) h2
        simpa using this
      rw [hc, hc0, MvPolynomial.C_0]
    rcases Nat.eq_zero_or_pos P.totalDegree with he | he
    · exact fromConst (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp he)
    · exact fromConst (eq_C_of_all_pderiv_zero_field P fun q ↦
        ih _ (lower_totalDegree_field q P he) (hstable P hP q))

/-- Helper lifting bounded-order differential independence (`∀ r, Fin N × Fin (r + 1)`) to
unbounded-order differential independence (`Fin N × ℕ`). -/
theorem lift_diff_indep_all_orders {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
    {N : ℕ} (Y : Fin N × ℕ → A)
    (hfin : ∀ r : ℕ, AlgebraicIndependent K (fun p : Fin N × Fin (r + 1) ↦ Y (p.1, p.2.val))) :
    AlgebraicIndependent K Y := by
  rw [algebraicIndependent_iff]
  intro P hP
  let r : ℕ := P.vars.sup Prod.snd
  let emb : Fin N × Fin (r + 1) → Fin N × ℕ := fun p ↦ (p.1, p.2.val)
  let proj : Fin N × ℕ → Fin N × Fin (r + 1) := fun p ↦
    if h : p.2 < r + 1 then (p.1, ⟨p.2, h⟩) else (p.1, ⟨0, Nat.succ_pos r⟩)
  let Q : MvPolynomial (Fin N × Fin (r + 1)) K := MvPolynomial.rename proj P
  have hQP : MvPolynomial.rename emb Q = P := by
    rw [MvPolynomial.rename_rename, MvPolynomial.rename_eq_aeval]
    have hcongr : ∀ u ∈ P.vars, emb (proj u) = u := by
      rintro ⟨h, j⟩ hu
      have hj : j < r + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := Prod.snd) hu)
      dsimp only [emb, proj]
      simp only [hj, ↓reduceDIte]
    have h1 : MvPolynomial.aeval (MvPolynomial.X (R := K) ∘ (emb ∘ proj)) P =
        MvPolynomial.aeval (MvPolynomial.X (R := K)) P := by
      simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
      apply Finset.sum_congr rfl; intro mon hmon; congr 1
      apply Finsupp.prod_congr; intro u hu
      simp only [Function.comp_apply,
        hcongr u ((MvPolynomial.mem_vars_iff_mem_support u).mpr ⟨mon, hmon, hu⟩)]
    rw [h1]
    exact congrFun (congrArg DFunLike.coe (MvPolynomial.aeval_X_left (R := K) (σ := Fin N × ℕ))) P
  have hQ0 : MvPolynomial.aeval (fun p : Fin N × Fin (r + 1) ↦ Y (p.1, p.2.val)) Q = 0 := by
    have heq : MvPolynomial.aeval Y (MvPolynomial.rename emb Q) =
        MvPolynomial.aeval (fun p : Fin N × Fin (r + 1) ↦ Y (p.1, p.2.val)) Q := by
      rw [MvPolynomial.aeval_rename]; rfl
    rw [← heq, hQP, hP]
  have hQzero : Q = 0 := algebraicIndependent_iff.mp (hfin r) Q hQ0
  rw [← hQP, hQzero, map_zero]

/-- **Main Wave Independence Theorem (`squareModN_wave_diff_indep`):**
For every `N ≥ 1`, nonzero `C, a₁ : ℂ`, arbitrary `a₂ : ℂ`, and any `ℂ`-differential field
`(K, dK)`, the `N` twisted square-partition wave series `(H_0, ..., H_{N-1})` in `TwoRayRing K`
are **jointly differentially independent over `K`** across all derivative orders `Fin N × ℕ`! -/
theorem squareModN_wave_diff_indep {K : Type*} [Field K] [Algebra ℂ K]
    (dK : Derivation ℂ K K) {N : ℕ} (hN : 1 ≤ N)
    {C a₁ a₂ : ℂ} (hC : C ≠ 0) (ha₁ : a₁ ≠ 0)
    {H : Fin N → TwoRayRing K} (hH : IsSquareModNWave N C H) :
    AlgebraicIndependent K
      (fun p : Fin N × ℕ ↦ (rayDerivX dK a₁ a₂)^[p.2] (H p.1)) :=
  lift_diff_indep_all_orders _ fun r ↦ squareModN_wave_diff_indep_fin dK hN hC ha₁ hH r

/-! ### 4. Exact Iterated Leibniz Rule & Kolchin Log-Derivative Transfer -/

section KolchinLogDeriv

/-- Exact iterated Leibniz formula for any `ℂ`-derivation `D : Derivation ℂ A A`:
`D^[n] (f * g) = ∑ k ∈ range (n + 1), (n.choose k : ℂ) • (D^[k] f * D^[n - k] g)`. -/
theorem deriv_iterate_mul {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) (f g : A) (n : ℕ) :
    D^[n] (f * g) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℕ) • (D^[k] f * D^[n - k] g) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    have hstep : (∑ k ∈ Finset.range (m + 1),
          D ((m.choose k : ℕ) • (D^[k] f * D^[m - k] g))) =
        (∑ k ∈ Finset.range (m + 1),
          (m.choose k : ℕ) • (D^[k + 1] f * D^[m - k] g)) +
        (∑ k ∈ Finset.range (m + 1),
          (m.choose k : ℕ) • (D^[k] f * D^[m - k + 1] g)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k _
      rw [map_nsmul, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
          ← Function.iterate_succ_apply' D k f, ← Function.iterate_succ_apply' D (m - k) g,
          mul_comm (D^[k] f), mul_comm (D^[m - k] g), add_comm, nsmul_add]
    rw [hstep]
    have h1 : (∑ k ∈ Finset.range (m + 1),
          (m.choose k : ℕ) • (D^[k + 1] f * D^[m - k] g)) =
        ∑ k ∈ Finset.Ico 1 (m + 2), (m.choose (k - 1) : ℕ) • (D^[k] f * D^[m + 1 - k] g) := by
      refine Finset.sum_nbij (· + 1) (fun k hk ↦ ?_) (fun _ _ _ _ h ↦ by dsimp at h; omega)
        (fun k hk ↦ ⟨k - 1, ?_, by
          have hk1 : 1 ≤ k := (Finset.mem_Ico.mp (Finset.mem_coe.mp hk)).1
          dsimp; omega⟩) (fun k _ ↦ ?_)
      · rw [Finset.mem_range] at hk
        rw [Finset.mem_Ico]; omega
      · rw [Finset.mem_coe, Finset.mem_Ico] at hk
        rw [Finset.mem_coe, Finset.mem_range]; omega
      · have hsub : m + 1 - (k + 1) = m - k := by omega
        simp only [Nat.add_sub_cancel, hsub]
    have h2 : (∑ k ∈ Finset.range (m + 1),
          (m.choose k : ℕ) • (D^[k] f * D^[m - k + 1] g)) =
        (m.choose 0 : ℕ) • (D^[0] f * D^[m + 1] g) +
        ∑ k ∈ Finset.Ico 1 (m + 1), (m.choose k : ℕ) • (D^[k] f * D^[m + 1 - k] g) := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos m)]
      congr 1
      apply Finset.sum_congr rfl; intro k hk
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hk).2
      rw [show m - k + 1 = m + 1 - k by omega]
    have h1_split : (∑ k ∈ Finset.Ico 1 (m + 2),
          (m.choose (k - 1) : ℕ) • (D^[k] f * D^[m + 1 - k] g)) =
        (∑ k ∈ Finset.Ico 1 (m + 1),
          (m.choose (k - 1) : ℕ) • (D^[k] f * D^[m + 1 - k] g)) +
        (m.choose m : ℕ) • (D^[m + 1] f * D^[0] g) := by
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1)]
      simp
    rw [h1, h1_split, h2]
    have hrhs : (∑ k ∈ Finset.range (m + 2),
          ((m + 1).choose k : ℕ) • (D^[k] f * D^[m + 1 - k] g)) =
        ((m + 1).choose 0 : ℕ) • (D^[0] f * D^[m + 1] g) +
        (∑ k ∈ Finset.Ico 1 (m + 1), ((m + 1).choose k : ℕ) • (D^[k] f * D^[m + 1 - k] g)) +
        ((m + 1).choose (m + 1) : ℕ) • (D^[m + 1] f * D^[0] g) := by
      rw [Finset.range_eq_Ico, Finset.sum_Ico_succ_top (by omega : 0 ≤ m + 1),
          Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos m)]
      simp
    rw [hrhs]
    have hmid : (∑ k ∈ Finset.Ico 1 (m + 1),
          (m.choose (k - 1) : ℕ) • (D^[k] f * D^[m + 1 - k] g)) +
        (∑ k ∈ Finset.Ico 1 (m + 1),
          (m.choose k : ℕ) • (D^[k] f * D^[m + 1 - k] g)) =
        ∑ k ∈ Finset.Ico 1 (m + 1), ((m + 1).choose k : ℕ) • (D^[k] f * D^[m + 1 - k] g) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
      rw [← add_nsmul]
      congr 1
      have hch := Nat.choose_succ_succ m (k - 1)
      rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, Nat.sub_add_cancel hk1] at hch
      omega
    simp only [Nat.choose_zero_right, Nat.choose_self]
    rw [← hmid]
    abel

/-- Helper: in `FractionRing A`, every derivative `D^[j] (F h)` belongs to the intermediate field
generated over `K` by `{D^[i] (P h) : i ≤ j + 1}` whenever `D (P h) = (c h * F h + B h) * P h`
with `P h ≠ 0` and `c h ≠ 0`. -/
private theorem logDeriv_mem_intermediateField {K A : Type*} [Field K] [Algebra ℂ K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra ℂ A] [IsScalarTower ℂ K A]
    (dK : Derivation ℂ K K) (D : Derivation ℂ A A)
    (hDK : ∀ c : K, D (algebraMap K A c) = algebraMap K A (dK c))
    {P F : A} {c B : K} (hP : P ≠ 0) (hc : c ≠ 0)
    (hlog : D P = (algebraMap K A c * F + algebraMap K A B) * P)
    (M : IntermediateField K (FractionRing A))
    {T : ℕ} (hPM : ∀ i ≤ T + 1, algebraMap A (FractionRing A) (D^[i] P) ∈ M) :
    ∀ j ≤ T, algebraMap A (FractionRing A) (D^[j] F) ∈ M := by
  let ι : A →+* FractionRing A := algebraMap A (FractionRing A)
  have hι_inj : Function.Injective ι := IsFractionRing.injective A (FractionRing A)
  have hιP_ne : ι P ≠ 0 := fun h0 ↦ hP (hι_inj (h0.trans (map_zero ι).symm))
  let G : A := algebraMap K A c * F + algebraMap K A B
  have hG_mem : ∀ j ≤ T, ι (D^[j] G) ∈ M := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      have hleib := deriv_iterate_mul D G P j
      have hDj1 : D^[j] (G * P) = D^[j + 1] P := by
        rw [← hlog, ← Function.iterate_succ_apply D j P]
      rw [hDj1, Finset.sum_range_succ, Nat.choose_self, one_nsmul, Nat.sub_self,
          Function.iterate_zero_apply] at hleib
      have hι_eq := congrArg ι hleib
      simp only [map_add, map_mul, map_sum, map_nsmul] at hι_eq
      have hsum_mem : (∑ l ∈ Finset.range j,
          (j.choose l : ℕ) • (ι (D^[l] G) * ι (D^[j - l] P))) ∈ M := by
        refine sum_mem fun l hl ↦ nsmul_mem (mul_mem ?_ ?_) _
        · have hlt : l < j := Finset.mem_range.mp hl
          exact ih l hlt (le_of_lt (lt_of_lt_of_le hlt hj))
        · exact hPM (j - l) (by omega)
      have hprod_mem : ι (D^[j] G) * ι P ∈ M := by
        have hdiff : ι (D^[j] G) * ι P =
            ι (D^[j + 1] P) - ∑ l ∈ Finset.range j,
              (j.choose l : ℕ) • (ι (D^[l] G) * ι (D^[j - l] P)) :=
          eq_sub_of_add_eq' hι_eq.symm
        rw [hdiff]
        exact sub_mem (hPM (j + 1) (by omega)) hsum_mem
      have hdiv : ι (D^[j] G) = (ι (D^[j] G) * ι P) / ι P := by
        rw [mul_div_cancel_right₀ _ hιP_ne]
      rw [hdiv]
      exact div_mem hprod_mem (hPM 0 (Nat.zero_le _))
  -- Now recover `ι (D^[j] F) ∈ M` from `D^[j] G = D^[j] (c * F) + D^[j] B`!
  have hDK_iter : ∀ n (a : K), D^[n] (algebraMap K A a) = algebraMap K A (dK^[n] a) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ m ih =>
      intro a
      rw [Function.iterate_succ_apply' D m, ih, hDK, ← Function.iterate_succ_apply' dK m]
  have hι_K : ∀ a : K, ι (algebraMap K A a) ∈ M := fun a ↦ by
    rw [← IsScalarTower.algebraMap_apply K A (FractionRing A)]
    exact M.algebraMap_mem a
  have hιc_ne : ι (algebraMap K A c) ≠ 0 := by
    rw [← IsScalarTower.algebraMap_apply K A (FractionRing A)]
    exact (map_ne_zero_iff (algebraMap K (FractionRing A)) (RingHom.injective _)).mpr hc
  have hD_add : ∀ n (x y : A), D^[n] (x + y) = D^[n] x + D^[n] y := by
    intro n; induction n with
    | zero => intro _ _; rfl
    | succ m ihm =>
      intro x y
      rw [Function.iterate_succ_apply' D m, ihm, map_add,
          ← Function.iterate_succ_apply' D m x, ← Function.iterate_succ_apply' D m y]
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj
    have hDjG' : D^[j] G =
        (∑ l ∈ Finset.range j, (j.choose l : ℕ) • (D^[l] F * algebraMap K A (dK^[j - l] c))) +
        D^[j] F * algebraMap K A c + algebraMap K A (dK^[j] B) := by
      have hcomm : G = F * algebraMap K A c + algebraMap K A B := by dsimp [G]; ring
      rw [hcomm, hD_add, hDK_iter, deriv_iterate_mul, Finset.sum_range_succ, Nat.choose_self,
          one_nsmul, Nat.sub_self, Function.iterate_zero_apply]
      congr 2
      apply Finset.sum_congr rfl; intro l _
      rw [hDK_iter]
    have hι_eq := congrArg ι hDjG'
    simp only [map_add, map_mul, map_sum, map_nsmul] at hι_eq
    have hsum_mem : (∑ l ∈ Finset.range j,
        (j.choose l : ℕ) • (ι (D^[l] F) * ι (algebraMap K A (dK^[j - l] c)))) ∈ M := by
      refine sum_mem fun l hl ↦ nsmul_mem (mul_mem ?_ (hι_K _)) _
      have hlt : l < j := Finset.mem_range.mp hl
      exact ih l hlt (le_of_lt (lt_of_lt_of_le hlt hj))
    have hprod_mem : ι (D^[j] F) * ι (algebraMap K A c) ∈ M := by
      have heq : ι (D^[j] F) * ι (algebraMap K A c) =
          ι (D^[j] G) - (∑ l ∈ Finset.range j,
            (j.choose l : ℕ) • (ι (D^[l] F) * ι (algebraMap K A (dK^[j - l] c)))) -
            ι (algebraMap K A (dK^[j] B)) := by
        linear_combination -hι_eq
      rw [heq]
      exact sub_mem (sub_mem (hG_mem j hj) hsum_mem) (hι_K _)
    have hdiv : ι (D^[j] F) = (ι (D^[j] F) * ι (algebraMap K A c)) / ι (algebraMap K A c) := by
      rw [mul_div_cancel_right₀ _ hιc_ne]
    rw [hdiv]
    exact div_mem hprod_mem (hι_K c)

/-- **General Kolchin Log-Derivative Transfer (`diffAlg_kolchin_logDeriv_indep`):**
In ANY `K`-differential integral domain `(A, D)` over a `ℂ`-differential field `(K, dK)`,
if `P : Fin N → A` are nonzero elements satisfying `D (P h) = (c h * F h + B h) * P h`
(`c h ≠ 0` in `K`) and `(F_0, ..., F_{N-1})` are jointly differentially independent over `K`,
then `(P_0, ..., P_{N-1})` are **jointly differentially independent over `K`**! -/
theorem diffAlg_kolchin_logDeriv_indep {K A : Type*} [Field K] [Algebra ℂ K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra ℂ A] [IsScalarTower ℂ K A]
    (dK : Derivation ℂ K K) (D : Derivation ℂ A A)
    (hDK : ∀ c : K, D (algebraMap K A c) = algebraMap K A (dK c))
    {N : ℕ} (F P : Fin N → A) (c B : Fin N → K)
    (hP : ∀ h, P h ≠ 0) (hc : ∀ h, c h ≠ 0)
    (hlog : ∀ h, D (P h) = (algebraMap K A (c h) * F h + algebraMap K A (B h)) * P h)
    (hF : AlgebraicIndependent K (fun p : Fin N × ℕ ↦ D^[p.2] (F p.1))) :
    AlgebraicIndependent K (fun p : Fin N × ℕ ↦ D^[p.2] (P p.1)) := by
  have : CharZero K := charZero_of_injective_algebraMap (RingHom.injective (algebraMap ℂ K))
  by_cases hN0 : N = 0
  · subst hN0
    exact algebraicIndependent_empty_type
  have hN : 1 ≤ N := Nat.pos_of_ne_zero hN0
  rw [algebraicIndependent_iff]
  intro Q_init hQ_init
  by_contra hQ_ne
  -- Choose a nonzero differential relation `Q` of MINIMAL `totalDegree`!
  let Y : Fin N × ℕ → A := fun p ↦ D^[p.2] (P p.1)
  have hex : ∃ d : ℕ, ∃ Q : MvPolynomial (Fin N × ℕ) K,
      Q ≠ 0 ∧ MvPolynomial.aeval Y Q = 0 ∧ Q.totalDegree = d :=
    ⟨Q_init.totalDegree, Q_init, hQ_ne, hQ_init, rfl⟩
  let dMin : ℕ := Nat.find hex
  obtain ⟨Q, hQne, hQ0, hQdeg⟩ := Nat.find_spec hex
  have hQmin : ∀ R : MvPolynomial (Fin N × ℕ) K,
      R.totalDegree < Q.totalDegree → MvPolynomial.aeval Y R = 0 → R = 0 := by
    intro R hRlt hR0
    by_contra hRne
    exact Nat.find_min hex (hQdeg ▸ hRlt) ⟨R, hRne, hR0, rfl⟩
  have hQdeg_pos : 0 < Q.totalDegree := by
    by_contra h0
    have hdeg0 : Q.totalDegree = 0 := by omega
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg0
    rw [hC, MvPolynomial.aeval_C] at hQ0
    have hc0 : Q.coeff 0 = 0 := (RingHom.injective (algebraMap K A)) (hQ0.trans (map_zero _).symm)
    exact hQne (by rw [hC, hc0, MvPolynomial.C_0])
  have hQvars_ne : Q.vars.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hall : ∀ u, MvPolynomial.pderiv u Q = 0 := fun u ↦ by
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars]
      rw [hemp]; exact Finset.notMem_empty u
    have hC := eq_C_of_all_pderiv_zero_field Q hall
    have : Q.totalDegree = 0 := by rw [hC]; simp
    omega
  -- Let `m₀` be the maximum derivative order appearing in `Q`, attained at some `(h₀, m₀) ∈ Q.vars`!
  obtain ⟨⟨h₀, m₀⟩, hm₀_mem, hm₀_max⟩ := Q.vars.exists_max_image Prod.snd hQvars_ne
  -- Partial derivative in `(h₀, m₀)` is nonzero and has strictly smaller degree, hence evaluates ≠ 0!
  have hpderiv_ne : MvPolynomial.aeval Y (MvPolynomial.pderiv (h₀, m₀) Q) ≠ 0 := by
    intro h0
    have hpd0 : MvPolynomial.pderiv (h₀, m₀) Q = 0 :=
      hQmin _ (lower_totalDegree_field (h₀, m₀) Q hQdeg_pos) h0
    have hdeg_pos : 0 < Q.degreeOf (h₀, m₀) := by
      rw [MvPolynomial.mem_vars_iff_mem_support] at hm₀_mem
      obtain ⟨m, hm, hmu⟩ := hm₀_mem
      have hpos : 0 < m (h₀, m₀) := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmu)
      rw [MvPolynomial.degreeOf_eq_sup]
      exact lt_of_lt_of_le hpos (Finset.le_sup (f := fun m : (Fin N × ℕ) →₀ ℕ ↦ m (h₀, m₀)) hm)
    -- `pderiv u Q = 0` in `CharZero` contradicts `0 < degreeOf u Q`!
    obtain ⟨m, hm, hm_eq⟩ :=
      Finset.exists_mem_eq_sup Q.support (MvPolynomial.support_nonempty.mpr hQne)
        (fun m : (Fin N × ℕ) →₀ ℕ ↦ m (h₀, m₀))
    rw [← MvPolynomial.degreeOf_eq_sup] at hm_eq
    have hmu_ne : m (h₀, m₀) ≠ 0 := by omega
    have hc := congrArg (fun f : MvPolynomial (Fin N × ℕ) K ↦
      f.coeff (m - Finsupp.single (h₀, m₀) (1 : ℕ))) hpd0
    simp only [AddMonoidAlgebra.coeff_zero, MvPolynomial.coeff_pderiv,
      Finsupp.sub_add_single_one_cancel hmu_ne] at hc
    have hnat : (((m - Finsupp.single (h₀, m₀) (1 : ℕ)) (h₀, m₀) : K) + 1) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero ((m - Finsupp.single (h₀, m₀) (1 : ℕ)) (h₀, m₀))
    exact MvPolynomial.mem_support_iff.mp hm ((mul_eq_zero.mp hc).resolve_right hnat)
  -- Restrict `Q` to `Q₀ : MvPolynomial (Fin N × Fin (m₀ + 1)) K`!
  let emb : Fin N × Fin (m₀ + 1) → Fin N × ℕ := fun p ↦ (p.1, p.2.val)
  let proj : Fin N × ℕ → Fin N × Fin (m₀ + 1) := fun p ↦
    if h : p.2 < m₀ + 1 then (p.1, ⟨p.2, h⟩) else (p.1, ⟨0, Nat.succ_pos m₀⟩)
  let Q₀ : MvPolynomial (Fin N × Fin (m₀ + 1)) K := MvPolynomial.rename proj Q
  let Y₀ : Fin N × Fin (m₀ + 1) → A := fun p ↦ D^[p.2.val] (P p.1)
  have hQ₀_eq : MvPolynomial.rename emb Q₀ = Q := by
    rw [MvPolynomial.rename_rename, MvPolynomial.rename_eq_aeval]
    have hcongr : ∀ u ∈ Q.vars, emb (proj u) = u := by
      rintro ⟨h, j⟩ hu
      have hj : j < m₀ + 1 := Nat.lt_succ_of_le (hm₀_max (h, j) hu)
      dsimp only [emb, proj]
      simp only [hj, ↓reduceDIte]
    have h1 : MvPolynomial.aeval (MvPolynomial.X (R := K) ∘ (emb ∘ proj)) Q =
        MvPolynomial.aeval (MvPolynomial.X (R := K)) Q := by
      simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
      apply Finset.sum_congr rfl; intro mon hmon; congr 1
      apply Finsupp.prod_congr; intro u hu
      simp only [Function.comp_apply,
        hcongr u ((MvPolynomial.mem_vars_iff_mem_support u).mpr ⟨mon, hmon, hu⟩)]
    rw [h1]
    exact congrFun (congrArg DFunLike.coe (MvPolynomial.aeval_X_left (R := K) (σ := Fin N × ℕ))) Q
  have hQ₀_eval : MvPolynomial.aeval Y₀ Q₀ = 0 := by
    have heq : MvPolynomial.aeval Y (MvPolynomial.rename emb Q₀) = MvPolynomial.aeval Y₀ Q₀ := by
      rw [MvPolynomial.aeval_rename]; rfl
    rw [← heq, hQ₀_eq, hQ0]
  have hQ₀_pderiv (h : Fin N) :
      MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) Q₀) =
      MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q) := by
    have hemb_inj : Function.Injective emb := fun a b hab ↦ by
      rcases a with ⟨ha, ja⟩; rcases b with ⟨hb, jb⟩
      have h1 : ha = hb := congrArg Prod.fst hab
      have h2 : ja.val = jb.val := congrArg Prod.snd hab
      exact Prod.ext h1 (Fin.ext h2)
    have hren : MvPolynomial.rename emb (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) Q₀) =
        MvPolynomial.pderiv (emb (h, ⟨m₀, Nat.lt_succ_self m₀⟩)) (MvPolynomial.rename emb Q₀) :=
      (MvPolynomial.pderiv_rename hemb_inj _ _).symm
    have h1 : MvPolynomial.aeval Y (MvPolynomial.rename emb
        (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) Q₀)) =
        MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) Q₀) := by
      rw [MvPolynomial.aeval_rename]; rfl
    rw [← h1, hren, hQ₀_eq]
  -- Define `jetSubalg m = K[D^[j] (P h) : h < N, j ≤ m] ⊆ A`.
  let jetSubalg (m : ℕ) : Subalgebra K A :=
    Algebra.adjoin K {x : A | ∃ (h : Fin N) (j : ℕ), j ≤ m ∧ x = D^[j] (P h)}
  have hjet_mono : ∀ {m₁ m₂}, m₁ ≤ m₂ → jetSubalg m₁ ≤ jetSubalg m₂ := fun hle ↦
    Algebra.adjoin_mono fun _ ⟨h, j, hj, hx⟩ ↦ ⟨h, j, hj.trans hle, hx⟩
  have hjet_D : ∀ {m} {x : A}, x ∈ jetSubalg m → D x ∈ jetSubalg (m + 1) := by
    intro m x hx
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨h, j, hj, rfl⟩
      rw [← Function.iterate_succ_apply' D j (P h)]
      exact Algebra.subset_adjoin ⟨h, j + 1, Nat.succ_le_succ hj, rfl⟩
    · intro r
      rw [hDK r]
      exact (jetSubalg (m + 1)).algebraMap_mem (dK r)
    · intro u v _ _ hu hv
      rw [map_add]
      exact add_mem hu hv
    · intro u v hu0 hv0 hu hv
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact add_mem (mul_mem (hjet_mono (Nat.le_succ m) hu0) hv)
        (mul_mem (hjet_mono (Nat.le_succ m) hv0) hu)
  have haeval_mem_jet (f : MvPolynomial (Fin N × Fin (m₀ + 1)) K) :
      MvPolynomial.aeval Y₀ f ∈ jetSubalg m₀ := by
    induction f using MvPolynomial.induction_on with
    | C r => rw [MvPolynomial.aeval_C]; exact (jetSubalg m₀).algebraMap_mem r
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p u hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (Algebra.subset_adjoin ⟨u.1, u.2.val, Nat.lt_succ_iff.mp u.2.isLt, rfl⟩)
  -- First derivative decomposition of `D (aeval Y₀ f)` for any `f : MvPolynomial (Fin N × Fin (m₀ + 1)) K`!
  have hD_aeval_first : ∀ f : MvPolynomial (Fin N × Fin (m₀ + 1)) K,
      ∃ R₁ ∈ jetSubalg m₀,
        D (MvPolynomial.aeval Y₀ f) =
          (∑ h : Fin N, MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) f) *
            D^[m₀ + 1] (P h)) + R₁ := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r =>
      refine ⟨algebraMap K A (dK r), (jetSubalg m₀).algebraMap_mem _, ?_⟩
      simp [hDK]
    | add p q hp hq =>
      obtain ⟨Rp, hRp, hep⟩ := hp
      obtain ⟨Rq, hRq, heq⟩ := hq
      refine ⟨Rp + Rq, add_mem hRp hRq, ?_⟩
      simp only [map_add, add_mul, Finset.sum_add_distrib, hep, heq]
      ring
    | mul_X p u hp =>
      obtain ⟨Rp, hRp, hep⟩ := hp
      have hu_mem : Y₀ u ∈ jetSubalg m₀ :=
        Algebra.subset_adjoin ⟨u.1, u.2.val, Nat.lt_succ_iff.mp u.2.isLt, rfl⟩
      by_cases hum : u.2.val < m₀
      · have hDu_mem : D (Y₀ u) ∈ jetSubalg m₀ := by
          change D (D^[u.2.val] (P u.1)) ∈ jetSubalg m₀
          rw [← Function.iterate_succ_apply' D u.2.val (P u.1)]
          exact Algebra.subset_adjoin ⟨u.1, u.2.val + 1, hum, rfl⟩
        refine ⟨Rp * Y₀ u + MvPolynomial.aeval Y₀ p * D (Y₀ u),
          add_mem (mul_mem hRp hu_mem) (mul_mem (haeval_mem_jet p) hDu_mem), ?_⟩
        rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPolynomial.aeval_X, hep]
        have hpd : ∀ h : Fin N,
            MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) (p * MvPolynomial.X u) =
            MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) p * MvPolynomial.X u := by
          intro h
          have hne : (u : Fin N × Fin (m₀ + 1)) ≠ (h, ⟨m₀, Nat.lt_succ_self m₀⟩) := fun e ↦ by
            have := congrArg (fun x : Fin N × Fin (m₀ + 1) ↦ x.2.val) e
            dsimp at this; omega
          rw [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply,
              ite_eq_right (fun e ↦ (hne e).elim)]
          simp [mul_comm]
        simp_rw [hpd, map_mul, MvPolynomial.aeval_X]
        rw [mul_add, Finset.mul_sum]
        have hsum_eq : (∑ h : Fin N, Y₀ u *
              (MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) p) *
                D^[m₀ + 1] (P h))) =
            ∑ h : Fin N, MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) p) *
              Y₀ u * D^[m₀ + 1] (P h) := by
          apply Finset.sum_congr rfl; intro h _; ring
        rw [hsum_eq]; ring
      · have hu_eq : u = (u.1, ⟨m₀, Nat.lt_succ_self m₀⟩) :=
          Prod.ext rfl (Fin.ext (le_antisymm (Nat.lt_succ_iff.mp u.2.isLt) (not_lt.mp hum)))
        refine ⟨Rp * Y₀ u, mul_mem hRp hu_mem, ?_⟩
        rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPolynomial.aeval_X, hep]
        have hpd : ∀ h : Fin N,
            MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) (p * MvPolynomial.X u)) =
            MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) p) * Y₀ u +
              if h = u.1 then MvPolynomial.aeval Y₀ p else 0 := by
          intro h
          rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPolynomial.pderiv_X, Pi.single_apply,
              map_add, map_mul, map_mul, MvPolynomial.aeval_X]
          have hiff : (u = (h, ⟨m₀, Nat.lt_succ_self m₀⟩)) ↔ (h = u.1) := by
            constructor
            · intro e; exact (congrArg Prod.fst e).symm
            · intro e; rw [hu_eq, e]
          rw [if_congr hiff rfl rfl]
          split_ifs <;> simp [mul_comm, add_comm]
        simp_rw [hpd, add_mul, Finset.sum_add_distrib]
        have hdelta : (∑ h : Fin N, (if h = u.1 then MvPolynomial.aeval Y₀ p else 0) * D^[m₀ + 1] (P h)) =
            MvPolynomial.aeval Y₀ p * D (Y₀ u) := by
          have hterm : ∀ h : Fin N, (if h = u.1 then MvPolynomial.aeval Y₀ p else 0) * D^[m₀ + 1] (P h) =
              if h = u.1 then MvPolynomial.aeval Y₀ p * D^[m₀ + 1] (P u.1) else 0 := by
            intro h; split_ifs with e <;> simp [e]
          simp_rw [hterm, Finset.sum_ite_eq']
          simp only [Finset.mem_univ, ↓reduceIte]
          rw [hu_eq]
          change MvPolynomial.aeval Y₀ p * D^[m₀ + 1] (P u.1) = MvPolynomial.aeval Y₀ p * D (D^[m₀] (P u.1))
          rw [Function.iterate_succ_apply']
        rw [hdelta, mul_add, Finset.mul_sum]
        have hsum_eq : (∑ h : Fin N, Y₀ u *
              (MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) p) *
                D^[m₀ + 1] (P h))) =
            ∑ h : Fin N, MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h, ⟨m₀, Nat.lt_succ_self m₀⟩) p) *
              Y₀ u * D^[m₀ + 1] (P h) := by
          apply Finset.sum_congr rfl; intro h _; ring
        rw [hsum_eq]; ring
  -- Iterate `s ≥ 1` times on `aeval Y₀ Q₀ = 0`!
  have hD_iter_Q : ∀ s : ℕ, 1 ≤ s →
      ∃ Rs ∈ jetSubalg (m₀ + s - 1),
        (∑ h : Fin N, MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q) * D^[m₀ + s] (P h)) +
          Rs = 0 := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base =>
      obtain ⟨R₁, hR₁, hEq⟩ := hD_aeval_first Q₀
      refine ⟨R₁, by simpa using hR₁, ?_⟩
      rw [hQ₀_eval, map_zero] at hEq
      simp_rw [← hQ₀_pderiv]
      exact hEq.symm
    | succ s hs ih =>
      obtain ⟨Rs, hRs, hEq⟩ := ih
      have hD0 := congrArg D hEq
      rw [map_zero, map_add, map_sum] at hD0
      let Rnext : A :=
        (∑ h : Fin N, D (MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q)) * D^[m₀ + s] (P h)) +
        D Rs
      have hRnext_mem : Rnext ∈ jetSubalg (m₀ + (s + 1) - 1) := by
        rw [show m₀ + (s + 1) - 1 = m₀ + s by omega]
        refine add_mem (sum_mem fun h _ ↦ mul_mem ?_ ?_) ?_
        · have hAh : MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q) ∈ jetSubalg m₀ := by
            rw [← hQ₀_pderiv]; exact haeval_mem_jet _
          exact hjet_mono (by omega : m₀ + 1 ≤ m₀ + s) (hjet_D hAh)
        · exact Algebra.subset_adjoin ⟨h, m₀ + s, le_rfl, rfl⟩
        · have hRs' : Rs ∈ jetSubalg (m₀ + s - 1) := hRs
          have hDRs := hjet_D hRs'
          rw [show m₀ + s - 1 + 1 = m₀ + s by omega] at hDRs
          exact hDRs
      refine ⟨Rnext, hRnext_mem, ?_⟩
      have hleib_sum : (∑ h : Fin N, D (MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q) *
            D^[m₀ + s] (P h))) =
          (∑ h : Fin N, MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q) *
            D^[m₀ + (s + 1)] (P h)) +
          (∑ h : Fin N, D (MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q)) *
            D^[m₀ + s] (P h)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro h _
        rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
            ← Function.iterate_succ_apply' D (m₀ + s) (P h),
            show (m₀ + s).succ = m₀ + (s + 1) by omega]
        ring
      rw [hleib_sum] at hD0
      dsimp only [Rnext]
      linear_combination hD0
  -- Now work in `E = FractionRing A`!
  let E := FractionRing A
  let ι : A →ₐ[K] E := IsScalarTower.toAlgHom K A E
  have hι_inj : Function.Injective ι := IsFractionRing.injective A E
  -- Set `Sidx` = all `(h, j) ∈ Fin N × Fin (m₀ + N + 1)` EXCEPT `(h₀, m₀), ..., (h₀, m₀ + N)`!
  let Tfin : Finset (Fin N × Fin (m₀ + N + 1)) := Finset.univ
  let drop : Finset (Fin N × Fin (m₀ + N + 1)) :=
    Finset.univ.filter fun p ↦ p.1 = h₀ ∧ m₀ ≤ p.2.val
  let Sfin : Finset (Fin N × Fin (m₀ + N + 1)) := Tfin \ drop
  have hdrop_card : drop.card = N + 1 := by
    let f : Fin (N + 1) → Fin N × Fin (m₀ + N + 1) :=
      fun s ↦ (h₀, ⟨m₀ + s.val, by omega⟩)
    have hdrop_eq : drop = Finset.univ.image f := by
      ext ⟨h, j⟩
      simp only [drop, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨rfl, hj⟩
        refine ⟨⟨j.val - m₀, by omega⟩, ?_⟩
        exact Prod.ext rfl (Fin.ext (by dsimp [f]; omega))
      · rintro ⟨s, hs⟩
        have h1 : h₀ = h := congrArg Prod.fst hs
        have h2 : m₀ + s.val = j.val := congrArg (fun p ↦ p.2.val) hs
        exact ⟨h1.symm, by omega⟩
    rw [hdrop_eq, Finset.card_image_of_injective _ (fun s₁ s₂ h ↦ by
      have := congrArg (fun p : Fin N × Fin (m₀ + N + 1) ↦ p.2.val) h
      dsimp [f] at this; exact Fin.ext (by omega)), Finset.card_fin]
  have hSfin_card : Sfin.card = N * (m₀ + N) - 1 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin, hdrop_card]
    have : N * (m₀ + N + 1) = N * (m₀ + N) + N := by ring
    omega
  let SfinE : Finset E := Sfin.image (fun p : Fin N × Fin (m₀ + N + 1) ↦ ι (D^[p.2.val] (P p.1)))
  let Sset : Set E := (SfinE : Set E)
  let x₀ : E := ι (D^[m₀] (P h₀))
  let M₀ : IntermediateField K E := IntermediateField.adjoin K Sset
  let M : IntermediateField K E := IntermediateField.adjoin K (insert x₀ Sset)
  -- Step A: `x₀` is algebraic (hence integral) over `M₀`!
  have hx₀_int : IsIntegral M₀ x₀ := by
    rw [← isAlgebraic_iff_isIntegral]
    -- View `Q₀` as a univariate polynomial in `(h₀, m₀)` with coefficients in `M₀`!
    let evM₀ : Fin N × Fin (m₀ + 1) → Polynomial M₀ := fun p ↦
      if hp : p = (h₀, ⟨m₀, Nat.lt_succ_self m₀⟩) then Polynomial.X
      else Polynomial.C ⟨ι (Y₀ p), IntermediateField.subset_adjoin K Sset
        (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(p.1, ⟨p.2.val, by have := p.2.isLt; omega⟩),
          by
            simp only [Sfin, Tfin, drop, Finset.mem_sdiff, Finset.mem_univ,
              Finset.mem_filter, true_and, not_and_or, not_le]
            by_cases hh : p.1 = h₀
            · right
              have hlt : p.2.val < m₀ := by
                have hle : p.2.val ≤ m₀ := Nat.lt_succ_iff.mp p.2.isLt
                by_contra hge
                exact hp (Prod.ext hh (Fin.ext (le_antisymm hle (not_lt.mp hge))))
              exact hlt
            · exact Or.inl hh, rfl⟩))⟩
    let f : Polynomial M₀ := MvPolynomial.aeval (R := K) evM₀ Q₀
    -- Show `Polynomial.aeval x₀ f = ι (aeval Y₀ Q₀) = 0`, and `Polynomial.aeval x₀ f.derivative = ι (aeval Y₀ (pderiv (h₀, m₀) Q₀)) ≠ 0`!
    have hcomp_eval : ∀ g : MvPolynomial (Fin N × Fin (m₀ + 1)) K,
        Polynomial.aeval x₀ (MvPolynomial.aeval (R := K) evM₀ g) = ι (MvPolynomial.aeval Y₀ g) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C r =>
        rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C,
            IsScalarTower.algebraMap_apply K M₀ (Polynomial M₀), Polynomial.algebraMap_eq,
            Polynomial.aeval_C]
        rfl
      | add p q hp hq => simp only [map_add, hp, hq]
      | mul_X p u hp =>
        simp only [map_mul, hp, MvPolynomial.aeval_X]
        congr 1
        dsimp only [evM₀]
        by_cases hu : u = (h₀, ⟨m₀, Nat.lt_succ_self m₀⟩)
        · simp only [hu, ↓reduceDIte, Polynomial.aeval_X]; rfl
        · simp only [hu, ↓reduceDIte, Polynomial.aeval_C]; rfl
    have hcomp_deriv : ∀ g : MvPolynomial (Fin N × Fin (m₀ + 1)) K,
        Polynomial.aeval x₀ (MvPolynomial.aeval (R := K) evM₀ g).derivative =
          ι (MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h₀, ⟨m₀, Nat.lt_succ_self m₀⟩) g)) := by
      intro g
      induction g using MvPolynomial.induction_on with
      | C r =>
        rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply K M₀ (Polynomial M₀),
            Polynomial.algebraMap_eq, Polynomial.derivative_C, map_zero, MvPolynomial.pderiv_C,
            map_zero, map_zero]
      | add p q hp hq =>
        simp only [map_add, hp, hq]
      | mul_X p u hp =>
        simp only [map_mul, MvPolynomial.aeval_X, Polynomial.derivative_mul, Derivation.leibniz,
          smul_eq_mul, map_add, hp, hcomp_eval p, MvPolynomial.pderiv_X, Pi.single_apply]
        dsimp only [evM₀]
        by_cases hu : u = (h₀, ⟨m₀, Nat.lt_succ_self m₀⟩)
        · subst hu
          simp only [↓reduceDIte, ↓reduceIte, Polynomial.aeval_X, Polynomial.derivative_X,
            map_one, mul_one]
          change ι (MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h₀, ⟨m₀, Nat.lt_succ_self m₀⟩) p)) * x₀ +
              ι (MvPolynomial.aeval Y₀ p) =
            ι (MvPolynomial.aeval Y₀ p) +
              x₀ * ι (MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h₀, ⟨m₀, Nat.lt_succ_self m₀⟩) p))
          ring
        · simp only [hu, ↓reduceDIte, ↓reduceIte, Polynomial.derivative_C, Polynomial.aeval_C,
            map_zero, mul_zero, add_zero, zero_add]
          change ι (MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h₀, ⟨m₀, Nat.lt_succ_self m₀⟩) p)) * ι (Y₀ u) =
            ι (Y₀ u) * ι (MvPolynomial.aeval Y₀ (MvPolynomial.pderiv (h₀, ⟨m₀, Nat.lt_succ_self m₀⟩) p))
          ring
    have hf0 : Polynomial.aeval x₀ f = 0 := by
      rw [hcomp_eval Q₀, hQ₀_eval, map_zero]
    have hfne : f ≠ 0 := by
      intro h0
      have hd0 : Polynomial.aeval x₀ f.derivative = 0 := by rw [h0, Polynomial.derivative_zero, map_zero]
      rw [hcomp_deriv Q₀, hQ₀_pderiv h₀] at hd0
      exact hpderiv_ne (hι_inj (hd0.trans (map_zero ι).symm))
    exact ⟨f, hfne, hf0⟩
  -- Step B: Every `ι (D^[j] (P h))` for `j ≤ m₀ + N` belongs to `M`!
  have hM_contains_P : ∀ (j : ℕ), j ≤ m₀ + N → ∀ (h : Fin N), ι (D^[j] (P h)) ∈ M := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj h
      by_cases hcond : h = h₀ ∧ m₀ ≤ j
      · rcases hcond with ⟨rfl, hjm⟩
        by_cases hjeq : j = m₀
        · subst hjeq
          exact IntermediateField.subset_adjoin K (insert x₀ Sset) (Set.mem_insert x₀ Sset)
        · let s : ℕ := j - m₀
          have hs1 : 1 ≤ s := by omega
          have hjs : m₀ + s = j := by omega
          obtain ⟨Rs, hRs_mem, hEq⟩ := hD_iter_Q s hs1
          have hjet_sub : ∀ x ∈ jetSubalg (m₀ + s - 1), ι x ∈ M := by
            intro x hx
            refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
            · rintro _ ⟨h', i, hi, rfl⟩
              exact ih i (by omega) (by omega) h'
            · intro r
              change algebraMap K E r ∈ M
              exact M.algebraMap_mem r
            · intro u v _ _ hu hv; rw [map_add]; exact add_mem hu hv
            · intro u v _ _ hu hv; rw [map_mul]; exact mul_mem hu hv
          have hAh_mem (h' : Fin N) : ι (MvPolynomial.aeval Y (MvPolynomial.pderiv (h', m₀) Q)) ∈ M := by
            rw [← hQ₀_pderiv]
            exact hjet_sub _ (hjet_mono (by omega : m₀ ≤ m₀ + s - 1) (haeval_mem_jet _))
          have hι_eq := congrArg ι hEq
          rw [map_zero, map_add, map_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ h)] at hι_eq
          have hother_mem : (∑ h' ∈ Finset.univ.erase h,
              ι (MvPolynomial.aeval Y (MvPolynomial.pderiv (h', m₀) Q) * D^[m₀ + s] (P h'))) ∈ M := by
            refine sum_mem fun h' hh' ↦ ?_
            rw [map_mul]
            refine mul_mem (hAh_mem h') ?_
            have hh'ne : h' ≠ h := Finset.ne_of_mem_erase hh'
            exact IntermediateField.subset_adjoin K (insert x₀ Sset) (Set.mem_insert_of_mem x₀
              (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(h', ⟨m₀ + s, by omega⟩), by
                simp only [Sfin, Tfin, drop, Finset.mem_sdiff, Finset.mem_univ,
                  Finset.mem_filter, true_and, not_and_or]
                exact Or.inl hh'ne, rfl⟩)))
          have hprod_mem : ι (MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q)) *
              ι (D^[m₀ + s] (P h)) ∈ M := by
            have heq : ι (MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q)) *
                ι (D^[m₀ + s] (P h)) =
                -(∑ h' ∈ Finset.univ.erase h,
                  ι (MvPolynomial.aeval Y (MvPolynomial.pderiv (h', m₀) Q) * D^[m₀ + s] (P h'))) -
                ι Rs := by
              rw [map_mul] at hι_eq
              linear_combination hι_eq
            rw [heq]
            exact sub_mem (neg_mem hother_mem) (hjet_sub Rs hRs_mem)
          have hlead_ne : ι (MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q)) ≠ 0 :=
            fun h0 ↦ hpderiv_ne (hι_inj (h0.trans (map_zero ι).symm))
          have hdiv : ι (D^[m₀ + s] (P h)) =
              (ι (MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q)) * ι (D^[m₀ + s] (P h))) /
                ι (MvPolynomial.aeval Y (MvPolynomial.pderiv (h, m₀) Q)) := by
            rw [mul_div_cancel_left₀ _ hlead_ne]
          rw [← hjs, hdiv]
          exact div_mem hprod_mem (hAh_mem h)
      · exact IntermediateField.subset_adjoin K (insert x₀ Sset) (Set.mem_insert_of_mem x₀
          (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(h, ⟨j, by omega⟩), by
            simp only [Sfin, Tfin, drop, Finset.mem_sdiff, Finset.mem_univ,
              Finset.mem_filter, true_and]
            exact hcond, rfl⟩)))
  -- Step C: All `N * (m₀ + N)` elements `ι (D^[j] (F h))` (`j < m₀ + N`) lie in `M`!
  have hM_contains_F : ∀ (p : Fin N × Fin (m₀ + N)), ι (D^[p.2.val] (F p.1)) ∈ M := by
    rintro ⟨h, j⟩
    have hj_lt : j.val < m₀ + N := j.isLt
    exact logDeriv_mem_intermediateField dK D hDK (hP h) (hc h) (hlog h) M (T := m₀ + N - 1)
      (fun i hi ↦ hM_contains_P i (by omega) h) j.val (by omega)
  -- Step D: `M` is algebraic over `Algebra.adjoin K S_M` where `S_M ⊆ M` has `#S_M ≤ N*(m₀+N) - 1`!
  let S_M : Set M := {y : M | y.val ∈ Sset}
  have hSM_card : Cardinal.mk S_M ≤ ((N * (m₀ + N) - 1 : ℕ) : Cardinal) := by
    have hsub : Subtype.val '' S_M ⊆ Sset := fun _ ⟨y, hy, he⟩ ↦ he ▸ hy
    have h1 : Cardinal.mk S_M = Cardinal.mk (Subtype.val '' S_M) :=
      (Cardinal.mk_image_eq Subtype.val_injective).symm
    rw [h1]
    calc Cardinal.mk (Subtype.val '' S_M)
        ≤ Cardinal.mk (SfinE : Set E) := Cardinal.mk_le_mk_of_subset hsub
      _ = (SfinE.card : Cardinal) := Cardinal.mk_coe_finset
      _ ≤ (Sfin.card : Cardinal) := Nat.cast_le.mpr Finset.card_image_le
      _ = ((N * (m₀ + N) - 1 : ℕ) : Cardinal) := by rw [hSfin_card]
  -- Every element of `M` is algebraic over `M₀_M := IntermediateField.adjoin K S_M`!
  let M₀_M : IntermediateField K M := IntermediateField.adjoin K S_M
  let x₀_M : M := ⟨x₀, IntermediateField.subset_adjoin K (insert x₀ Sset) (Set.mem_insert x₀ Sset)⟩
  have hx₀M_int : IsIntegral M₀_M x₀_M := by
    -- Pull back the minimal integral polynomial of `x₀` over `M₀` along `M₀ →ₐ[K] M₀_M`!
    obtain ⟨p, hp_mon, hp_eval⟩ := hx₀_int
    have hM₀_le_M : M₀ ≤ M :=
      IntermediateField.adjoin_le_iff.mpr ((Set.subset_insert x₀ Sset).trans
        (IntermediateField.subset_adjoin K (insert x₀ Sset)))
    have hM₀_le_map : M₀ ≤ IntermediateField.map (IsScalarTower.toAlgHom K M E) M₀_M :=
      IntermediateField.adjoin_le_iff.mpr fun e he ↦
        ⟨⟨e, IntermediateField.subset_adjoin K (insert x₀ Sset) (Set.mem_insert_of_mem x₀ he)⟩,
          IntermediateField.subset_adjoin K S_M he, rfl⟩
    let liftM₀ : M₀ →ₐ[K] M₀_M :=
      { toFun := fun z ↦ ⟨⟨z.val, hM₀_le_M z.property⟩, by
          obtain ⟨w, hw, hw_eq⟩ := hM₀_le_map z.property
          have hweq : w = ⟨z.val, hM₀_le_M z.property⟩ := Subtype.ext hw_eq
          exact hweq ▸ hw⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl
        commutes' := fun _ ↦ rfl }
    refine ⟨p.map liftM₀.toRingHom, hp_mon.map liftM₀.toRingHom, ?_⟩
    apply Subtype.ext
    have hval : ((Polynomial.eval₂ (algebraMap M₀_M M) x₀_M (p.map liftM₀.toRingHom) : M) : E) =
        Polynomial.eval₂ (algebraMap M₀ E) x₀ p := by
      rw [Polynomial.eval₂_map]
      have heq : (M.val.toRingHom).comp ((algebraMap M₀_M M).comp liftM₀.toRingHom) =
          algebraMap M₀ E := by ext z; rfl
      simpa [← heq] using Polynomial.hom_eval₂ p ((algebraMap M₀_M M).comp liftM₀.toRingHom)
        M.val.toRingHom x₀_M
    simpa [Polynomial.aeval_def, hp_eval] using hval
  have hM_alg_M₀M : Algebra.IsAlgebraic M₀_M M := by
    have htop : (⊤ : IntermediateField M₀_M M) = IntermediateField.adjoin M₀_M ({x₀_M} : Set M) := by
      rw [eq_comm, eq_top_iff]
      rintro y _
      have hy : y.val ∈ M := y.property
      -- `y.val ∈ IntermediateField.adjoin K (insert x₀ Sset)` lies in the image of `adjoin M₀_M {x₀_M}`!
      let Ksub : IntermediateField K M :=
        (IntermediateField.adjoin M₀_M ({x₀_M} : Set M)).restrictScalars K
      have hKsub : insert x₀ Sset ⊆ (IntermediateField.map (IsScalarTower.toAlgHom K M E) Ksub : Set E) := by
        rintro e (rfl | he)
        · exact ⟨x₀_M, IntermediateField.subset_adjoin M₀_M {x₀_M} rfl, rfl⟩
        · let y_e : M := ⟨e, IntermediateField.subset_adjoin K (insert x₀ Sset) (Set.mem_insert_of_mem x₀ he)⟩
          have hy_e : y_e ∈ M₀_M := IntermediateField.subset_adjoin K S_M he
          exact ⟨y_e, IntermediateField.algebraMap_mem (IntermediateField.adjoin M₀_M {x₀_M}) ⟨y_e, hy_e⟩, rfl⟩
      have hM_le : M ≤ IntermediateField.map (IsScalarTower.toAlgHom K M E) Ksub :=
        IntermediateField.adjoin_le_iff.mpr hKsub
      obtain ⟨w, hw, hw_eq⟩ := hM_le hy
      have hwy : w = y := Subtype.ext hw_eq
      exact hwy ▸ hw
    have halg_adjoin : Algebra.IsAlgebraic M₀_M (IntermediateField.adjoin M₀_M ({x₀_M} : Set M)) :=
      IntermediateField.isAlgebraic_adjoin (fun x hx ↦ by rw [Set.mem_singleton_iff.mp hx]; exact hx₀M_int)
    constructor
    intro y
    have hy : y ∈ (IntermediateField.adjoin M₀_M ({x₀_M} : Set M)) := htop ▸ trivial
    obtain ⟨q, hqne, hq0⟩ := halg_adjoin.isAlgebraic ⟨y, hy⟩
    refine ⟨q, hqne, ?_⟩
    have hval := congrArg (IntermediateField.adjoin M₀_M ({x₀_M} : Set M)).val hq0
    rw [← Polynomial.aeval_algHom_apply, map_zero] at hval
    exact hval
  -- Chain `Algebra.IsAlgebraic (Algebra.adjoin K S_M) M₀_M` and `Algebra.IsAlgebraic M₀_M M`!
  have : Algebra.IsAlgebraic (Algebra.adjoin K S_M) M :=
    Algebra.IsAlgebraic.trans (Algebra.adjoin K S_M) M₀_M M
  have htrdeg_le : Algebra.trdeg K M ≤ ((N * (m₀ + N) - 1 : ℕ) : Cardinal) :=
    (Algebra.IsAlgebraic.trdeg_le_cardinalMk K S_M).trans hSM_card
  -- Step E: `N * (m₀ + N) ≤ trdeg K M`, contradiction!
  let F_M : Fin N × Fin (m₀ + N) → M := fun p ↦ ⟨ι (D^[p.2.val] (F p.1)), hM_contains_F p⟩
  have hFM_indep : AlgebraicIndependent K F_M := by
    have h1 : AlgebraicIndependent K (fun p : Fin N × Fin (m₀ + N) ↦ D^[p.2.val] (F p.1)) :=
      hF.comp (fun p : Fin N × Fin (m₀ + N) ↦ (p.1, p.2.val)) (fun a b hab ↦ by
        rcases a with ⟨ha, ja⟩; rcases b with ⟨hb, jb⟩
        dsimp only at hab
        rcases Prod.mk.inj hab with ⟨h1, h2⟩
        exact Prod.ext h1 (Fin.ext h2))
    have h2 : AlgebraicIndependent K (ι ∘ fun p : Fin N × Fin (m₀ + N) ↦ D^[p.2.val] (F p.1)) :=
      h1.map' (f := ι) hι_inj
    have hcomp : (M.val ∘ F_M) = ι ∘ fun p : Fin N × Fin (m₀ + N) ↦ D^[p.2.val] (F p.1) := rfl
    exact AlgebraicIndependent.of_comp M.val (hcomp ▸ h2)
  have htrdeg_ge : ((N * (m₀ + N) : ℕ) : Cardinal) ≤ Algebra.trdeg K M := by
    have hlift := hFM_indep.lift_cardinalMk_le_trdeg
    simp only [Cardinal.mk_fintype, Fintype.card_prod, Fintype.card_fin, Cardinal.lift_natCast,
      Cardinal.lift_id'] at hlift
    exact hlift
  have hcontra : N * (m₀ + N) ≤ N * (m₀ + N) - 1 :=
    Nat.cast_le.mp (htrdeg_ge.trans htrdeg_le)
  have hpos : 1 ≤ N * (m₀ + N) := Nat.mul_pos hN (by omega)
  omega

/-- **Twisted Products Joint Differential Independence (`squareModN_twistedProd_diff_indep`):**
Combining `squareModN_wave_diff_indep` with `diffAlg_kolchin_logDeriv_indep`, any nonzero
twisted products `P : Fin N → TwoRayRing K` satisfying `∂_X P_h = (c_h H_h + B_h) P_h`
(`c_h ≠ 0` in `K`, e.g., `c_h = 2` for `P_2(ζ^h; e^{-X^{-2}})`) are **jointly differentially
independent over `K`**! -/
theorem squareModN_twistedProd_diff_indep {K : Type*} [Field K] [Algebra ℂ K]
    (dK : Derivation ℂ K K) {N : ℕ} (hN : 1 ≤ N)
    {C a₁ a₂ : ℂ} (hC : C ≠ 0) (ha₁ : a₁ ≠ 0)
    {H P : Fin N → TwoRayRing K} (hH : IsSquareModNWave N C H)
    (c B : Fin N → K) (hP : ∀ h, P h ≠ 0) (hc : ∀ h, c h ≠ 0)
    (hlog : ∀ h, rayDerivX dK a₁ a₂ (P h) =
      (MvPowerSeries.C (c h) * H h + MvPowerSeries.C (B h)) * P h) :
    AlgebraicIndependent K
      (fun p : Fin N × ℕ ↦ (rayDerivX dK a₁ a₂)^[p.2] (P p.1)) := by
  have : IsDomain (TwoRayRing K) := NoZeroDivisors.to_isDomain _
  exact diffAlg_kolchin_logDeriv_indep dK (rayDerivX dK a₁ a₂) (rayDerivX_C dK a₁ a₂)
    H P c B hP hc hlog (squareModN_wave_diff_indep dK hN hC ha₁ hH)

end KolchinLogDeriv

/-! ### 5. Invertible `N × N` DFT, Mod-`N` Part-Count Series `(A_0, ..., A_{N-1})`,
Periodic-Weight Rank Law, & Multiples-of-`d` Corollary -/

section DFTAndPeriodicWeights

/-- Primitive `N`-th root of unity `ζ_N = exp(2π i / N) ∈ ℂ`. -/
def rootOfUnity (N : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))

theorem rootOfUnity_ne_zero (N : ℕ) : rootOfUnity N ≠ 0 :=
  Complex.exp_ne_zero _

theorem rootOfUnity_two : rootOfUnity 2 = -1 := by
  unfold rootOfUnity
  have harg : (2 : ℂ) * Real.pi * Complex.I / ((2 : ℕ) : ℂ) = Real.pi * Complex.I := by
    push_cast; field_simp
  rw [harg, Complex.exp_pi_mul_I]

/-- Normalized `N × N` inverse-DFT matrix `(N⁻¹ · ζ_N^{-r h})_{r, h}` extracting mod-`N`
part-count series `A_r = N⁻¹ ∑_h ζ_N^{-r h} P_2(ζ_N^h; q)`. -/
def dftMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun r h ↦
    (N : ℂ)⁻¹ * Complex.exp (-(2 * Real.pi * Complex.I * ((r.val * h.val : ℕ) : ℂ) / (N : ℂ)))

/-- Forward `N × N` Fourier evaluation matrix `(ζ_N^{h r})_{h, r}` reconstructing
`P_2(ζ_N^h; q) = ∑_r ζ_N^{h r} A_r(q)`. -/
def dftInvMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun h r ↦
    Complex.exp (2 * Real.pi * Complex.I * ((h.val * r.val : ℕ) : ℂ) / (N : ℂ))

/-- **Exact Roots-of-Unity Filter Identity (`rootsOfUnity_filter`):**
For every `N ≥ 1`, `r : Fin N`, and `ℓ : ℕ`,
`N⁻¹ ∑_{h : Fin N} exp(-2π i r h / N) * exp(2π i h ℓ / N)` equals `1` if `ℓ % N = r.val`
and `0` otherwise. -/
theorem rootsOfUnity_filter {N : ℕ} (hN : 1 ≤ N) (r : Fin N) (ℓ : ℕ) :
    (N : ℂ)⁻¹ * (∑ h : Fin N,
      Complex.exp (-(2 * Real.pi * Complex.I * ((r.val * h.val : ℕ) : ℂ) / (N : ℂ))) *
      Complex.exp (2 * Real.pi * Complex.I * ((h.val * ℓ : ℕ) : ℂ) / (N : ℂ))) =
    if ℓ % N = r.val then 1 else 0 := by
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((ℓ : ℤ) - (r.val : ℤ) : ℤ) : ℂ) / (N : ℂ))
  have hterm (h : Fin N) :
      Complex.exp (-(2 * Real.pi * Complex.I * ((r.val * h.val : ℕ) : ℂ) / (N : ℂ))) *
        Complex.exp (2 * Real.pi * Complex.I * ((h.val * ℓ : ℕ) : ℂ) / (N : ℂ)) =
      ω ^ h.val := by
    rw [← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp [hNne]
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun h : ℕ ↦ ω ^ h) N]
  by_cases hmod : ℓ % N = r.val
  · simp only [hmod, ↓reduceIte]
    have hdiv : ((N : ℤ)) ∣ ((ℓ : ℤ) - (r.val : ℤ)) := by
      refine ⟨(ℓ / N : ℕ), ?_⟩
      have h1 := Nat.div_add_mod ℓ N
      have h2 : (ℓ : ℤ) = (N : ℤ) * ((ℓ / N : ℕ) : ℤ) + (r.val : ℤ) := by
        rw [← hmod]; exact_mod_cast h1.symm
      linarith
    obtain ⟨m, hm⟩ := hdiv
    have hω1 : ω = 1 := by
      dsimp only [ω]
      have harg : 2 * Real.pi * Complex.I * (((ℓ : ℤ) - (r.val : ℤ) : ℤ) : ℂ) / (N : ℂ) =
          (m : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hm]; push_cast; field_simp [hNne]
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    simp [hω1, hNne]
  · rw [ite_eq_right (fun h ↦ (hmod h).elim)]
    have hω_ne : ω ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨m, hm⟩ := h1
      have hmul : (((ℓ : ℤ) - (r.val : ℤ) : ℤ) : ℂ) = (m : ℂ) * (N : ℂ) := by
        have hstep := congrArg (· * (N : ℂ)) hm
        field_simp [hNne] at hstep
        rw [mul_comm] at hstep
        exact hstep
      have hint : (ℓ : ℤ) - (r.val : ℤ) = m * (N : ℤ) := by exact_mod_cast hmul
      have heq_mod : (ℓ : ℤ) % (N : ℤ) = (r.val : ℤ) % (N : ℤ) := by
        have hadd : (ℓ : ℤ) = (r.val : ℤ) + m * (N : ℤ) := by linarith
        rw [hadd, Int.add_mul_emod_self_right]
      have hnat_mod : ℓ % N = r.val % N := by exact_mod_cast heq_mod
      rw [Nat.mod_eq_of_lt r.isLt] at hnat_mod
      exact hmod hnat_mod
    have hωN : ω ^ N = 1 := by
      dsimp only [ω]
      rw [← Complex.exp_nat_mul]
      have harg : (N : ℂ) * (2 * Real.pi * Complex.I * (((ℓ : ℤ) - (r.val : ℤ) : ℤ) : ℂ) / (N : ℂ)) =
          (((ℓ : ℤ) - (r.val : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        field_simp [hNne]
      rw [harg, Complex.exp_int_mul_two_pi_mul_I]
    have hgeom := geom_sum_mul ω N
    rw [hωN, sub_self] at hgeom
    have hsum0 : ∑ i ∈ Finset.range N, ω ^ i = 0 :=
      (mul_eq_zero.mp hgeom).resolve_right (sub_ne_zero.mpr hω_ne)
    rw [hsum0, mul_zero]

/-- Exact right-inverse identity `dftMatrix N * dftInvMatrix N = 1` for every `N ≥ 1`. -/
theorem dftMatrix_mul_dftInvMatrix {N : ℕ} (hN : 1 ≤ N) :
    dftMatrix N * dftInvMatrix N = 1 := by
  ext r r'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hpull : (∑ h : Fin N, dftMatrix N r h * dftInvMatrix N h r') =
      (N : ℂ)⁻¹ * (∑ h : Fin N,
        Complex.exp (-(2 * Real.pi * Complex.I * ((r.val * h.val : ℕ) : ℂ) / (N : ℂ))) *
        Complex.exp (2 * Real.pi * Complex.I * ((h.val * r'.val : ℕ) : ℂ) / (N : ℂ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro h _
    simp only [dftMatrix, dftInvMatrix, Matrix.of_apply]
    ring
  rw [hpull, rootsOfUnity_filter hN r r'.val, Nat.mod_eq_of_lt r'.isLt]
  by_cases h : r = r'
  · subst h; simp
  · have hne : r'.val ≠ r.val := fun e ↦ h (Fin.ext e.symm)
    simp [h, hne]

/-- Exact left-inverse identity `dftInvMatrix N * dftMatrix N = 1` for every `N ≥ 1`. -/
theorem dftInvMatrix_mul_dftMatrix {N : ℕ} (hN : 1 ≤ N) :
    dftInvMatrix N * dftMatrix N = 1 := by
  ext h h'
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hpull : (∑ r : Fin N, dftInvMatrix N h r * dftMatrix N r h') =
      (N : ℂ)⁻¹ * (∑ r : Fin N,
        Complex.exp (-(2 * Real.pi * Complex.I * ((h'.val * r.val : ℕ) : ℂ) / (N : ℂ))) *
        Complex.exp (2 * Real.pi * Complex.I * ((r.val * h.val : ℕ) : ℂ) / (N : ℂ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro r _
    simp only [dftMatrix, dftInvMatrix, Matrix.of_apply]
    have hcomm1 : h.val * r.val = r.val * h.val := mul_comm _ _
    have hcomm2 : r.val * h'.val = h'.val * r.val := mul_comm _ _
    rw [hcomm1, hcomm2]
    ring
  rw [hpull, rootsOfUnity_filter hN h' h.val, Nat.mod_eq_of_lt h.isLt]
  by_cases heq : h = h'
  · subst heq; simp
  · have hne : h.val ≠ h'.val := fun e ↦ heq (Fin.ext e)
    simp [heq, hne]

/-- The `N × N` DFT matrix has nonzero determinant for every `N ≥ 1`. -/
theorem dftMatrix_det_ne_zero {N : ℕ} (hN : 1 ≤ N) :
    (dftMatrix N).det ≠ 0 := by
  intro h0
  have h1 := congrArg Matrix.det (dftMatrix_mul_dftInvMatrix hN)
  rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h1
  exact zero_ne_one h1

/-- Any `ℂ`-derivation `D` on a `ℂ`-algebra `A` commutes with arbitrary `ℂ`-linear combinations
at every derivative order `k : ℕ`. -/
theorem deriv_iter_linearComb {A : Type*} [CommRing A] [Algebra ℂ A]
    (D : Derivation ℂ A A) {n : ℕ} (a : Fin n → ℂ) (Y : Fin n → A) (k : ℕ) :
    D^[k] (∑ j : Fin n, algebraMap ℂ A (a j) * Y j) =
      ∑ j : Fin n, algebraMap ℂ A (a j) * D^[k] (Y j) := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply' D m, ih, map_sum]
    apply Finset.sum_congr rfl; intro j _
    rw [Derivation.leibniz, Derivation.map_algebraMap, smul_eq_mul, smul_eq_mul,
        mul_zero, add_zero, ← Function.iterate_succ_apply' D m (Y j)]

/-- **Linear Change of Coordinates Preserving Joint Differential Independence:**
If `M : Matrix (Fin r) (Fin n) ℂ` has a right inverse `B : Matrix (Fin n) (Fin r) ℂ` (`M * B = 1`),
then `(Y_0, ..., Y_{n-1})` jointly differentially independent over `K` implies
`(Z_i = ∑_j M_{ij} Y_j)_{i < r}` are **jointly differentially independent over `K`**! -/
theorem linearComb_diff_indep_of_rightInv {K A : Type*} [Field K] [Algebra ℂ K]
    [CommRing A] [Algebra K A] [Algebra ℂ A] [IsScalarTower ℂ K A]
    (D : Derivation ℂ A A) {r n : ℕ} (Y : Fin n → A)
    (hY : AlgebraicIndependent K (fun p : Fin n × ℕ ↦ D^[p.2] (Y p.1)))
    (M : Matrix (Fin r) (Fin n) ℂ) (B : Matrix (Fin n) (Fin r) ℂ)
    (hMB : M * B = 1) :
    AlgebraicIndependent K (fun p : Fin r × ℕ ↦
      D^[p.2] (∑ j : Fin n, algebraMap ℂ A (M p.1 j) * Y j)) := by
  let Z : Fin r → A := fun i ↦ ∑ j : Fin n, algebraMap ℂ A (M i j) * Y j
  let Φ : MvPolynomial (Fin r × ℕ) K →ₐ[K] MvPolynomial (Fin n × ℕ) K :=
    MvPolynomial.aeval fun p ↦
      ∑ j : Fin n, MvPolynomial.C (algebraMap ℂ K (M p.1 j)) * MvPolynomial.X (j, p.2)
  let Ψ : MvPolynomial (Fin n × ℕ) K →ₐ[K] MvPolynomial (Fin r × ℕ) K :=
    MvPolynomial.aeval fun p ↦
      ∑ i : Fin r, MvPolynomial.C (algebraMap ℂ K (B p.1 i)) * MvPolynomial.X (i, p.2)
  have hΨΦ : ∀ P : MvPolynomial (Fin r × ℕ) K, Ψ (Φ P) = P := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C c => simp [Φ, Ψ]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p u hp =>
      rw [map_mul, map_mul, hp]
      congr 1
      rcases u with ⟨i, k⟩
      simp only [Φ, MvPolynomial.aeval_X, map_sum, map_mul, Ψ, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_eq, Finset.mul_sum]
      rw [Finset.sum_comm]
      have hinner (i' : Fin r) :
          (∑ j : Fin n, MvPolynomial.C (algebraMap ℂ K (M i j)) *
            (MvPolynomial.C (algebraMap ℂ K (B j i')) * MvPolynomial.X (i', k))) =
          MvPolynomial.C (algebraMap ℂ K ((M * B) i i')) * MvPolynomial.X (i', k) := by
        rw [Matrix.mul_apply, map_sum, map_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _
        rw [map_mul, map_mul]; ring
      simp_rw [hinner, hMB, Matrix.one_apply]
      rw [Finset.sum_eq_single i]
      · simp
      · intro i' _ hne; simp [hne.symm]
      · intro h; exact (h (Finset.mem_univ i)).elim
  have hΦ_inj : Function.Injective Φ := Function.LeftInverse.injective hΨΦ
  have hcomp : MvPolynomial.aeval (fun p : Fin r × ℕ ↦ D^[p.2] (Z p.1)) =
      (MvPolynomial.aeval (fun p : Fin n × ℕ ↦ D^[p.2] (Y p.1))).comp Φ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, k⟩
    simp only [AlgHom.comp_apply, Φ, MvPolynomial.aeval_X, map_sum, map_mul, MvPolynomial.aeval_C,
      Z, deriv_iter_linearComb]
    apply Finset.sum_congr rfl; intro j _
    rw [IsScalarTower.algebraMap_apply ℂ K A]
  rw [algebraicIndependent_iff_injective_aeval, hcomp]
  exact (algebraicIndependent_iff_injective_aeval.mp hY).comp hΦ_inj

/-- Row-linear-independence version of `linearComb_diff_indep_of_rightInv`: any `r` linearly
independent `ℂ`-linear combinations of `n` jointly differentially independent elements are
jointly differentially independent over `K`. -/
theorem linearComb_diff_indep_of_linearIndependent {K A : Type*} [Field K] [Algebra ℂ K]
    [CommRing A] [Algebra K A] [Algebra ℂ A] [IsScalarTower ℂ K A]
    (D : Derivation ℂ A A) {r n : ℕ} (Y : Fin n → A)
    (hY : AlgebraicIndependent K (fun p : Fin n × ℕ ↦ D^[p.2] (Y p.1)))
    (M : Matrix (Fin r) (Fin n) ℂ)
    (hM : LinearIndependent ℂ (fun i : Fin r ↦ fun j : Fin n ↦ M i j)) :
    AlgebraicIndependent K (fun p : Fin r × ℕ ↦
      D^[p.2] (∑ j : Fin n, algebraMap ℂ A (M p.1 j) * Y j)) := by
  let rowMap : (Fin r → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Matrix.vecMulLinear M
  have hrow_inj : Function.Injective rowMap := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hlin : ∑ i : Fin r, v i • (fun j : Fin n ↦ M i j) = 0 := by
      ext j
      have hj := congrFun hv j
      simpa only [rowMap, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hj
    have h0 := (Fintype.linearIndependent_iff.mp hM) v hlin
    ext i; exact h0 i
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective rowMap (LinearMap.ker_eq_bot.mpr hrow_inj)
  let B : Matrix (Fin n) (Fin r) ℂ := Matrix.of fun j i ↦ L (Pi.single j 1) i
  have hMB : M * B = 1 := by
    ext i i'
    have hev : L (rowMap (Pi.single i 1)) = Pi.single i 1 := by
      simpa using LinearMap.congr_fun hL (Pi.single i 1)
    have hrow_single : rowMap (Pi.single i 1) = ∑ j : Fin n, M i j • Pi.single j 1 := by
      ext j; simp [rowMap, Matrix.vecMul, dotProduct, Pi.single_apply]
    have hlhs : L (rowMap (Pi.single i 1)) i' = (M * B) i i' := by
      rw [hrow_single, map_sum]
      simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, B,
        Matrix.of_apply]
    rw [← hlhs, hev, Matrix.one_apply, Pi.single_apply]
    by_cases h : i = i' <;> simp [h, eq_comm]
  exact linearComb_diff_indep_of_rightInv D Y hY M B hMB

/-- Mod-`N` part-count series `A_r = N⁻¹ ∑_h ζ_N^{-r h} P_h` obtained from twisted products `P`. -/
def modNPartSeries {A : Type*} [CommRing A] [Algebra ℂ A] (N : ℕ) (P : Fin N → A) (r : Fin N) : A :=
  ∑ h : Fin N, algebraMap ℂ A (dftMatrix N r h) * P h

/-- **Theorem 2.4 (`squareModN_parts_diff_indep`):**
For every `N ≥ 1`, whenever the `N` twisted square-partition products `(P_0, ..., P_{N-1})` are
jointly differentially independent over `K`, the `N` unweighted mod-`N` part-count series
`(A_0, ..., A_{N-1})` (`A_r = N⁻¹ ∑_h ζ_N^{-r h} P_h`) are **jointly differentially independent
over `K`** (exact differential rank `N`)! -/
theorem squareModN_parts_diff_indep {K A : Type*} [Field K] [Algebra ℂ K]
    [CommRing A] [Algebra K A] [Algebra ℂ A] [IsScalarTower ℂ K A]
    (D : Derivation ℂ A A) {N : ℕ} (hN : 1 ≤ N) (P : Fin N → A)
    (hP : AlgebraicIndependent K (fun p : Fin N × ℕ ↦ D^[p.2] (P p.1))) :
    AlgebraicIndependent K (fun p : Fin N × ℕ ↦ D^[p.2] (modNPartSeries N P p.1)) :=
  linearComb_diff_indep_of_rightInv D P hP (dftMatrix N) (dftInvMatrix N)
    (dftMatrix_mul_dftInvMatrix hN)

/-- **End-to-End Theorem 2.4 in `TwoRayRing K` (`squareModN_parts_diff_indep_of_wave`):**
Chaining Codex's `T_b ∂_{T_b}` strong induction (`squareModN_wave_diff_indep`), Kolchin's
log-derivative transfer (`squareModN_twistedProd_diff_indep`), and invertible `N × N` DFT
(`squareModN_parts_diff_indep`): starting directly from `IsSquareModNWave N C H` and
`∂_X P_h = (c_h H_h + B_h) P_h`, the `N` mod-`N` part-count series `(A_0, ..., A_{N-1})` are
**unconditionally jointly differentially independent over `K`**! -/
theorem squareModN_parts_diff_indep_of_wave {K : Type*} [Field K] [Algebra ℂ K]
    (dK : Derivation ℂ K K) {N : ℕ} (hN : 1 ≤ N)
    {C a₁ a₂ : ℂ} (hC : C ≠ 0) (ha₁ : a₁ ≠ 0)
    {H P : Fin N → TwoRayRing K} (hH : IsSquareModNWave N C H)
    (c B : Fin N → K) (hP : ∀ h, P h ≠ 0) (hc : ∀ h, c h ≠ 0)
    (hlog : ∀ h, rayDerivX dK a₁ a₂ (P h) =
      (MvPowerSeries.C (c h) * H h + MvPowerSeries.C (B h)) * P h) :
    AlgebraicIndependent K
      (fun p : Fin N × ℕ ↦ (rayDerivX dK a₁ a₂)^[p.2] (modNPartSeries N P p.1)) :=
  squareModN_parts_diff_indep (rayDerivX dK a₁ a₂) hN P
    (squareModN_twistedProd_diff_indep dK hN hC ha₁ hH c B hP hc hlog)

/-- Explicit `N = 2` formulas: `A_0 = (1/2)(P_0 + P_1)` (even number of square parts) and
`A_1 = (1/2)(P_0 - P_1)` (odd number of square parts). -/
theorem squareEvenOdd_formulas {A : Type*} [CommRing A] [Algebra ℂ A] (P : Fin 2 → A) :
    modNPartSeries 2 P 0 = algebraMap ℂ A (1 / 2 : ℂ) * (P 0 + P 1) ∧
    modNPartSeries 2 P 1 = algebraMap ℂ A (1 / 2 : ℂ) * (P 0 - P 1) := by
  have h00 : dftMatrix 2 0 0 = (1 / 2 : ℂ) := by
    simp [dftMatrix]
  have h01 : dftMatrix 2 0 1 = (1 / 2 : ℂ) := by
    simp [dftMatrix]
  have h10 : dftMatrix 2 1 0 = (1 / 2 : ℂ) := by
    simp [dftMatrix]
  have h11 : dftMatrix 2 1 1 = -(1 / 2 : ℂ) := by
    simp only [dftMatrix, Matrix.of_apply, Fin.val_one, mul_one, Nat.cast_one, Nat.cast_ofNat]
    have harg : -((2 : ℂ) * Real.pi * Complex.I / (2 : ℂ)) = -(Real.pi * Complex.I) := by
      field_simp
    rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I]
    ring
  constructor
  · simp only [modNPartSeries, Fin.sum_univ_two, h00, h01]
    ring
  · simp only [modNPartSeries, Fin.sum_univ_two, h10, h11, map_neg]
    ring

/-- **Explicit `N = 2` Even vs. Odd Square Partitions Corollary (`squareEvenOdd_joint_diff_indep`):**
The two generating functions `A_even = (1/2)(P_2(1; q) + P_2(-1; q))` and
`A_odd = (1/2)(P_2(1; q) - P_2(-1; q))` counting partitions into squares with an even vs. odd
number of parts are **jointly differentially independent over `K`**! -/
theorem squareEvenOdd_joint_diff_indep {K A : Type*} [Field K] [Algebra ℂ K]
    [CommRing A] [Algebra K A] [Algebra ℂ A] [IsScalarTower ℂ K A]
    (D : Derivation ℂ A A) (P : Fin 2 → A)
    (hP : AlgebraicIndependent K (fun p : Fin 2 × ℕ ↦ D^[p.2] (P p.1))) :
    AlgebraicIndependent K (fun p : Fin 2 × ℕ ↦
      D^[p.2] (![algebraMap ℂ A (1 / 2 : ℂ) * (P 0 + P 1),
                 algebraMap ℂ A (1 / 2 : ℂ) * (P 0 - P 1)] p.1)) := by
  have hind := squareModN_parts_diff_indep D (by decide : 1 ≤ 2) P hP
  have hfor := squareEvenOdd_formulas P
  have heq : (fun r : Fin 2 ↦ modNPartSeries 2 P r) =
      ![algebraMap ℂ A (1 / 2 : ℂ) * (P 0 + P 1),
        algebraMap ℂ A (1 / 2 : ℂ) * (P 0 - P 1)] := by
    funext r; fin_cases r
    · exact hfor.1
    · exact hfor.2
  convert hind using 1
  funext p
  rw [← congrFun heq p.1]

/-- A function `f : ℕ → ℂ` with positive period `T` (`∀ n, f (n + T) = f n`) is also periodic with
period any multiple `N` of `T`, and satisfies `f n = f (n % N)` for all `n : ℕ`. -/
theorem periodic_mod_eq {f : ℕ → ℂ} {T N : ℕ} (_hT : 1 ≤ T) (hdvd : T ∣ N)
    (hper : ∀ n : ℕ, f (n + T) = f n) (n : ℕ) :
    f n = f (n % N) := by
  have hper_mul : ∀ m k : ℕ, f (m + k * T) = f m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [show m + (k + 1) * T = (m + k * T) + T by ring, hper, ih]
  obtain ⟨q, rfl⟩ := hdvd
  have hN_eq : n = n % (T * q) + (n / (T * q) * q) * T := by
    have hdiv := Nat.div_add_mod n (T * q)
    linarith [show T * q * (n / (T * q)) = (n / (T * q) * q) * T by ring]
  conv_lhs => rw [hN_eq]
  exact hper_mul (n % (T * q)) (n / (T * q) * q)

/-- Common period `∏ i, T i` of a finite family of positive periods `T : Fin s → ℕ`. -/
def commonPeriod {s : ℕ} (T : Fin s → ℕ) : ℕ :=
  ∏ i : Fin s, T i

theorem commonPeriod_pos {s : ℕ} {T : Fin s → ℕ} (hT : ∀ i, 1 ≤ T i) :
    1 ≤ commonPeriod T :=
  Finset.one_le_prod fun i _ ↦ hT i

/-- Weighted generating function associated to a periodic weight `w : ℕ → ℂ` of period dividing `N`
given the mod-`N` part-count series `A_parts : Fin N → A`:
`weightedPartSeries N A_parts w = ∑_{r : Fin N} w(r) · A_r`. -/
def weightedPartSeries {A : Type*} [CommRing A] [Algebra ℂ A] (N : ℕ)
    (A_parts : Fin N → A) (w : ℕ → ℂ) : A :=
  ∑ r : Fin N, algebraMap ℂ A (w r.val) * A_parts r

/-- Restriction map `(ℕ → ℂ) →ₗ[ℂ] (Fin N → ℂ)` is injective on the span of `N`-periodic weights. -/
private lemma restrictModN_injOn_span {s : ℕ} {w : Fin s → (ℕ → ℂ)} {T : Fin s → ℕ}
    (hT : ∀ i, 1 ≤ T i) (hper : ∀ i n, w i (n + T i) = w i n) :
    let N := commonPeriod T
    let res : (ℕ → ℂ) →ₗ[ℂ] (Fin N → ℂ) :=
      { toFun := fun f r ↦ f r.val
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    Function.Injective (res.domRestrict (Submodule.span ℂ (Set.range w))) := by
  intro N res
  have hN : 1 ≤ N := commonPeriod_pos hT
  have hperN : ∀ f ∈ Submodule.span ℂ (Set.range w), ∀ n : ℕ, f n = f (n % N) := by
    intro f hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨i, rfl⟩ n
      exact periodic_mod_eq (hT i) (Finset.dvd_prod_of_mem T (Finset.mem_univ i)) (hper i) n
    · intro _; rfl
    · intro x y _ _ hx hy n; simp [hx n, hy n]
    · intro c x _ hx n; simp [hx n]
  rw [injective_iff_map_eq_zero]
  rintro ⟨f, hf⟩ h0
  apply Subtype.ext
  funext n
  have hlt : n % N < N := Nat.mod_lt n hN
  change f n = 0
  rw [hperN f hf n]
  exact congrFun h0 ⟨n % N, hlt⟩

/-- **Linearly Independent Periodic Weights Yield Jointly Differentially Independent Series:**
If `w : Fin s → (ℕ → ℂ)` are `ℂ`-linearly independent periodic weight functions with positive
periods `T i ≥ 1` and common period `N = ∏ i, T i`, then the `s` weighted square-partition
generating functions `W_i = ∑_{r < N} w_i(r) A_r` are **jointly differentially independent over `K`**! -/
theorem squarePeriodicWeights_linearIndep_diff_indep {K A : Type*} [Field K] [Algebra ℂ K]
    [CommRing A] [Algebra K A] [Algebra ℂ A] [IsScalarTower ℂ K A]
    (D : Derivation ℂ A A) {s : ℕ} (w : Fin s → (ℕ → ℂ)) (T : Fin s → ℕ)
    (hT : ∀ i, 1 ≤ T i) (hper : ∀ i n, w i (n + T i) = w i n)
    (hw_indep : LinearIndependent ℂ w)
    (A_parts : Fin (commonPeriod T) → A)
    (hA : AlgebraicIndependent K (fun p : Fin (commonPeriod T) × ℕ ↦ D^[p.2] (A_parts p.1))) :
    AlgebraicIndependent K
      (fun p : Fin s × ℕ ↦ D^[p.2] (weightedPartSeries (commonPeriod T) A_parts (w p.1))) := by
  let N := commonPeriod T
  let M : Matrix (Fin s) (Fin N) ℂ := Matrix.of fun i r ↦ w i r.val
  have hM : LinearIndependent ℂ (fun i : Fin s ↦ fun r : Fin N ↦ M i r) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hspan : ∑ i : Fin s, c i • w i ∈ Submodule.span ℂ (Set.range w) :=
      Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have h0 : (⟨∑ i : Fin s, c i • w i, hspan⟩ : Submodule.span ℂ (Set.range w)) = 0 := by
      apply restrictModN_injOn_span hT hper
      ext r
      simpa [M, Finset.sum_apply] using congrFun hc r
    exact Fintype.linearIndependent_iff.mp hw_indep c (congrArg Subtype.val h0)
  exact linearComb_diff_indep_of_linearIndependent D A_parts hA M hM

/-- **Exact Periodic-Weight Differential Rank Theorem (`squarePeriodicWeights_diff_rank_eq`):**
For ANY `s` periodic weight functions `w : Fin s → (ℕ → ℂ)` with positive periods `T : Fin s → ℕ`,
common period `N = ∏ i, T i`, and mod-`N` part-count series `A_parts : Fin N → A` jointly
differentially independent over `K`, let `W i = ∑_{r < N} w_i(r) A_r` and
`d = Module.finrank ℂ (Submodule.span ℂ (Set.range w))`. Then:
1. There exists a `d`-element subset `idx : Fin d → Fin s` whose weighted series
   `(W (idx 0), ..., W (idx (d - 1)))` are **jointly differentially independent over `K`**, and
   every `D^[k] (W i)` is a `ℂ`-linear combination of `{D^[k] (W (idx a)) : a : Fin d}` with the
   exact same constant coefficients for every `k : ℕ`;
2. Every `ℂ`-linear relation `∑ i, c_i w_i = 0` among the weights gives the exact same linear
   relation `∑ i, c_i D^[k] (W i) = 0` for every `k : ℕ`;
3. For every jet order `J : ℕ`, the algebraic transcendence degree of the jet algebra
   `K[D^[k] (W i) : i < s, k < J]` over `K` is **EXACTLY `d * J`**! -/
theorem squarePeriodicWeights_diff_rank_eq {K A : Type*} [Field K] [Algebra ℂ K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra ℂ A] [IsScalarTower ℂ K A]
    (D : Derivation ℂ A A) {s : ℕ} (w : Fin s → (ℕ → ℂ)) (T : Fin s → ℕ)
    (hT : ∀ i, 1 ≤ T i) (hper : ∀ i n, w i (n + T i) = w i n)
    (A_parts : Fin (commonPeriod T) → A)
    (hA : AlgebraicIndependent K (fun p : Fin (commonPeriod T) × ℕ ↦ D^[p.2] (A_parts p.1))) :
    let N := commonPeriod T
    let W : Fin s → A := fun i ↦ weightedPartSeries N A_parts (w i)
    let d : ℕ := Module.finrank ℂ (Submodule.span ℂ (Set.range w))
    (∃ idx : Fin d → Fin s,
      Function.Injective idx ∧
      AlgebraicIndependent K (fun p : Fin d × ℕ ↦ D^[p.2] (W (idx p.1))) ∧
      ∀ i : Fin s, ∃ coeffs : Fin d → ℂ, ∀ k : ℕ,
        D^[k] (W i) = ∑ a : Fin d, algebraMap ℂ A (coeffs a) * D^[k] (W (idx a))) ∧
    (∀ c : Fin s → ℂ, (∑ i : Fin s, c i • w i = 0) →
      ∀ k : ℕ, ∑ i : Fin s, algebraMap ℂ A (c i) * D^[k] (W i) = 0) ∧
    (∀ J : ℕ,
      Algebra.trdeg K (Algebra.adjoin K (Set.range (fun p : Fin s × Fin J ↦ D^[p.2.val] (W p.1)))) =
        ((d * J : ℕ) : Cardinal)) := by
  intro N W d
  -- Extract a basis subset `t ⊆ Set.range w` of cardinality `d`!
  obtain ⟨t, ht_sub, ht_span, ht_indep⟩ := exists_linearIndependent ℂ (Set.range w)
  have ht_fin : t.Finite := (Set.finite_range w).subset ht_sub
  let : Fintype t := ht_fin.fintype
  have ht_card : Fintype.card t = d := by
    have h1 := finrank_span_eq_card ht_indep
    rw [Subtype.range_coe, ht_span] at h1
    exact h1.symm
  let e : Fin d ≃ t := (Fintype.equivFinOfCardEq ht_card).symm
  let idx : Fin d → Fin s := fun a ↦ (ht_sub (e a).property).choose
  have hidx_eq (a : Fin d) : w (idx a) = (e a).val := (ht_sub (e a).property).choose_spec
  have hidx_inj : Function.Injective idx := fun a b hab ↦ by
    have : (e a).val = (e b).val := by rw [← hidx_eq a, ← hidx_eq b, hab]
    exact e.injective (Subtype.ext this)
  have hw_idx_indep : LinearIndependent ℂ (w ∘ idx) := by
    have h1 : (w ∘ idx) = (fun x : t ↦ (x : ℕ → ℂ)) ∘ e := by
      funext a; exact hidx_eq a
    rw [h1]
    exact ht_indep.comp e e.injective
  have hW_idx_indep : AlgebraicIndependent K (fun p : Fin d × ℕ ↦ D^[p.2] (W (idx p.1))) := by
    -- Directly apply `linearComb_diff_indep_of_linearIndependent` at the common period `N`!
    let M : Matrix (Fin d) (Fin N) ℂ := Matrix.of fun a r ↦ w (idx a) r.val
    have hM : LinearIndependent ℂ (fun a : Fin d ↦ fun r : Fin N ↦ M a r) := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have hspan : ∑ a : Fin d, c a • w (idx a) ∈ Submodule.span ℂ (Set.range w) :=
        Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨idx a, rfl⟩)
      have h0 : (⟨∑ a : Fin d, c a • w (idx a), hspan⟩ : Submodule.span ℂ (Set.range w)) = 0 := by
        apply restrictModN_injOn_span hT hper
        ext r
        simpa [M, Finset.sum_apply] using congrFun hc r
      exact Fintype.linearIndependent_iff.mp hw_idx_indep c (congrArg Subtype.val h0)
    exact linearComb_diff_indep_of_linearIndependent D A_parts hA M hM
  -- Linear relation transfer lemma!
  have hlin_rel : ∀ c : Fin s → ℂ, (∑ i : Fin s, c i • w i = 0) →
      ∀ k : ℕ, ∑ i : Fin s, algebraMap ℂ A (c i) * D^[k] (W i) = 0 := by
    intro c hc k
    have h0 : ∑ i : Fin s, algebraMap ℂ A (c i) * W i = 0 := by
      simp only [W, weightedPartSeries, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_eq_zero; intro r _
      have hcr : ∑ i : Fin s, c i * w i r.val = 0 := by
        simpa [Finset.sum_apply] using congrFun hc r.val
      have hsum : (∑ i : Fin s, algebraMap ℂ A (c i) * (algebraMap ℂ A (w i r.val) * A_parts r)) =
          algebraMap ℂ A (∑ i : Fin s, c i * w i r.val) * A_parts r := by
        rw [map_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro i _
        rw [map_mul, mul_assoc]
      rw [hsum, hcr, map_zero, zero_mul]
    rw [← deriv_iter_linearComb D c W k, h0]
    clear hc h0
    induction k with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', ih, map_zero]
  -- Every `w i` lies in `span_ℂ (range (w ∘ idx))`!
  have hspan_idx : Submodule.span ℂ (Set.range (w ∘ idx)) = Submodule.span ℂ (Set.range w) := by
    have hrange : Set.range (w ∘ idx) = t := by
      ext f
      simp only [Set.mem_range, Function.comp_apply]
      constructor
      · rintro ⟨a, rfl⟩; rw [hidx_eq a]; exact (e a).property
      · intro hf; exact ⟨e.symm ⟨f, hf⟩, by rw [hidx_eq]; simp⟩
    rw [hrange, ht_span]
  have hex_coeffs : ∀ i : Fin s, ∃ coeffs : Fin d → ℂ, ∀ k : ℕ,
      D^[k] (W i) = ∑ a : Fin d, algebraMap ℂ A (coeffs a) * D^[k] (W (idx a)) := by
    intro i
    have hmem : w i ∈ Submodule.span ℂ (Set.range (w ∘ idx)) := by
      rw [hspan_idx]; exact Submodule.subset_span ⟨i, rfl⟩
    rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
    obtain ⟨cF, hcF⟩ := hmem
    let coeffs : Fin d → ℂ := fun a ↦ cF a
    have hcoeffs : ∑ a : Fin d, coeffs a • w (idx a) = w i := by
      rw [← hcF, Finsupp.sum_fintype]
      · rfl
      · intro a; simp
    refine ⟨coeffs, fun k ↦ ?_⟩
    have hW0 : W i = ∑ a : Fin d, algebraMap ℂ A (coeffs a) * W (idx a) := by
      simp only [W, weightedPartSeries, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro r _
      have hwr : w i r.val = ∑ a : Fin d, coeffs a * w (idx a) r.val := by
        simpa [Finset.sum_apply] using (congrFun hcoeffs r.val).symm
      rw [hwr, map_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro a _
      rw [map_mul, mul_assoc]
    rw [hW0, deriv_iter_linearComb]
  refine ⟨⟨idx, hidx_inj, hW_idx_indep, hex_coeffs⟩, hlin_rel, ?_⟩
  -- Part 3: Exact transcendence degree `trdeg K K[W_i^{(k)} : i < s, k < J] = d * J`!
  intro J
  let S_all : Set A := Set.range (fun p : Fin s × Fin J ↦ D^[p.2.val] (W p.1))
  let S_bas : Set A := Set.range (fun p : Fin d × Fin J ↦ D^[p.2.val] (W (idx p.1)))
  have hadj_eq : Algebra.adjoin K S_all = Algebra.adjoin K S_bas := by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff]
      rintro _ ⟨⟨i, k⟩, rfl⟩
      obtain ⟨coeffs, hcoeffs⟩ := hex_coeffs i
      change D^[k.val] (W i) ∈ Algebra.adjoin K S_bas
      rw [hcoeffs k.val]
      refine sum_mem fun a _ ↦ mul_mem ?_ (Algebra.subset_adjoin ⟨(a, k), rfl⟩)
      rw [IsScalarTower.algebraMap_apply ℂ K A]
      exact (Algebra.adjoin K S_bas).algebraMap_mem _
    · exact Algebra.adjoin_mono fun _ ⟨⟨a, k⟩, h⟩ ↦ ⟨(idx a, k), h⟩
  rw [hadj_eq]
  let Alg := Algebra.adjoin K S_bas
  let S_sub_fin : Finset Alg :=
    Finset.univ.image (fun p : Fin d × Fin J ↦
      (⟨D^[p.2.val] (W (idx p.1)), Algebra.subset_adjoin ⟨p, rfl⟩⟩ : Alg))
  let S_sub : Set Alg := (S_sub_fin : Set Alg)
  have hadj_top : Algebra.adjoin K S_sub = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ _
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨p, rfl⟩
      exact Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩))
    · intro r
      exact (Algebra.adjoin K S_sub).algebraMap_mem r
    · intro u v hu hv ihu ihv
      exact add_mem ihu ihv
    · intro u v hu hv ihu ihv
      exact mul_mem ihu ihv
  have : Algebra.IsAlgebraic (Algebra.adjoin K S_sub) Alg := by
    constructor; intro y
    have hy : y ∈ Algebra.adjoin K S_sub := hadj_top ▸ trivial
    exact isAlgebraic_algebraMap (⟨y, hy⟩ : Algebra.adjoin K S_sub)
  have hle : Algebra.trdeg K Alg ≤ ((d * J : ℕ) : Cardinal) := by
    calc Algebra.trdeg K Alg
        ≤ Cardinal.mk (S_sub_fin : Set Alg) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K S_sub
      _ = (S_sub_fin.card : Cardinal) := Cardinal.mk_coe_finset
      _ ≤ ((Finset.univ : Finset (Fin d × Fin J)).card : Cardinal) := Nat.cast_le.mpr Finset.card_image_le
      _ = ((d * J : ℕ) : Cardinal) := by simp
  have hge : ((d * J : ℕ) : Cardinal) ≤ Algebra.trdeg K Alg := by
    let gen : Fin d × Fin J → Alg := fun p ↦
      ⟨D^[p.2.val] (W (idx p.1)), Algebra.subset_adjoin ⟨p, rfl⟩⟩
    have hgen_indep : AlgebraicIndependent K gen := by
      have h1 : AlgebraicIndependent K (fun p : Fin d × Fin J ↦ D^[p.2.val] (W (idx p.1))) :=
        hW_idx_indep.comp (fun p : Fin d × Fin J ↦ (p.1, p.2.val)) (fun a b hab ↦ by
          rcases a with ⟨ha, ja⟩; rcases b with ⟨hb, jb⟩
          dsimp only at hab
          rcases Prod.mk.inj hab with ⟨h1, h2⟩
          exact Prod.ext h1 (Fin.ext h2))
      exact AlgebraicIndependent.of_comp Alg.val h1
    have hlift := hgen_indep.lift_cardinalMk_le_trdeg
    simp only [Cardinal.mk_fintype, Fintype.card_prod, Fintype.card_fin, Cardinal.lift_natCast,
      Cardinal.lift_id'] at hlift
    exact hlift
  exact le_antisymm hle hge

/-! ### 6. Countably Many Multiples-of-`d` Corollary (`squareMultiplesOfD_diff_indep`) -/

/-- Indicator weight `1_{d ∣ ℓ} : ℕ → ℂ` restricting the number of parts to multiples of `d`. -/
def multInd (d : ℕ) : ℕ → ℂ :=
  fun ℓ ↦ if d ∣ ℓ then 1 else 0

theorem multInd_periodic (d ℓ : ℕ) : multInd d (ℓ + d) = multInd d ℓ := by
  simp [multInd, Nat.dvd_add_self_right]

/-- **Triangular Evaluation Matrix Determinant `= 1`:**
For any strictly increasing sequence of positive integers `d_0 < d_1 < ... < d_{m-1}`, the
`m × m` matrix `E_{i, j} = 1_{d_i ∣ d_j}` is upper triangular with `1`s on the diagonal, hence
has determinant `1 ≠ 0`! -/
theorem multInd_evalMatrix_det_eq_one {m : ℕ} {d : Fin m → ℕ}
    (hd_pos : ∀ i, 1 ≤ d i) (hd_mono : StrictMono d) :
    (Matrix.of fun i j : Fin m ↦ multInd (d i) (d j)).det = 1 := by
  let E : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j ↦ multInd (d i) (d j)
  have htri : E.IsUpperTriangular := by
    intro i j hij
    change multInd (d i) (d j) = 0
    have hlt : d j < d i := hd_mono hij
    have hnd : ¬ d i ∣ d j := Nat.not_dvd_of_pos_of_lt (hd_pos j) hlt
    simp [multInd, hnd]
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_eq_one
  intro i _
  simp [E, multInd]

/-- For ANY finite injective family of positive integers `d : Fin m → ℕ`, the indicator functions
`{1_{d_i ∣ ·} : i : Fin m}` are `ℂ`-linearly independent in `ℕ → ℂ`. -/
theorem multInd_linearIndependent {m : ℕ} {d : Fin m → ℕ}
    (hd_pos : ∀ i, 1 ≤ d i) (hd_inj : Function.Injective d) :
    LinearIndependent ℂ (fun i : Fin m ↦ multInd (d i)) := by
  -- Sort `d` via a permutation `σ` into strictly increasing order `d ∘ σ`!
  let S : Finset ℕ := Finset.univ.image d
  have hScard : S.card = m := by rw [Finset.card_image_of_injective _ hd_inj, Finset.card_fin]
  let emb : Fin m ↪o ℕ := S.orderEmbOfFin hScard
  have hmem (i : Fin m) : emb i ∈ S := Finset.orderEmbOfFin_mem S hScard i
  let toIdx : Fin m → Fin m := fun i ↦ (Finset.mem_image.mp (hmem i)).choose
  have htoIdx_eq (i : Fin m) : d (toIdx i) = emb i := (Finset.mem_image.mp (hmem i)).choose_spec.2
  have htoIdx_inj : Function.Injective toIdx := fun i₁ i₂ h ↦ by
    have : emb i₁ = emb i₂ := by rw [← htoIdx_eq i₁, ← htoIdx_eq i₂, h]
    exact emb.injective this
  let σ : Equiv.Perm (Fin m) := Equiv.ofBijective toIdx (Finite.injective_iff_bijective.mp htoIdx_inj)
  have hmono : StrictMono (d ∘ σ) := fun i j hij ↦ by
    change d (toIdx i) < d (toIdx j)
    rw [htoIdx_eq i, htoIdx_eq j]
    exact emb.strictMono hij
  have hsorted : LinearIndependent ℂ (fun i : Fin m ↦ multInd ((d ∘ σ) i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    let E : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j ↦ multInd ((d ∘ σ) i) ((d ∘ σ) j)
    have hdet : E.det ≠ 0 := by
      have h1 : E.det = 1 := multInd_evalMatrix_det_eq_one (d := d ∘ σ) (fun i ↦ hd_pos (σ i)) hmono
      rw [h1]
      exact one_ne_zero
    have hEt : Eᵀ *ᵥ c = 0 := by
      funext j
      have hj := congrFun hc ((d ∘ σ) j)
      simpa [Matrix.mulVec, dotProduct, E, Finset.sum_apply, mul_comm] using hj
    have hdet_t : Eᵀ.det ≠ 0 := by rw [Matrix.det_transpose]; exact hdet
    have hc0 : c = 0 :=
      Eᵀ.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
        (mem_nonZeroDivisors_of_ne_zero hdet_t) hEt
    intro i; exact congrFun hc0 i
  have hcomp := hsorted.comp σ.symm σ.symm.injective
  convert hcomp using 1
  funext i
  simp [Function.comp_apply]

/-- **Countably Many Multiples-of-`d` Corollary (`squareMultiplesOfD_diff_indep`):**
For ANY finite set of pairwise distinct positive integers `d_0, ..., d_{m-1} ≥ 1` with common
period `N = ∏ i, d_i`, the `m` generating functions restricting the number of square parts to
multiples of `d_i` (`weightedPartSeries N A_parts (multInd (d i))`) are **jointly differentially
independent over `K`** (exact differential rank `m`)! -/
theorem squareMultiplesOfD_diff_indep {K A : Type*} [Field K] [Algebra ℂ K]
    [CommRing A] [Algebra K A] [Algebra ℂ A] [IsScalarTower ℂ K A]
    (D : Derivation ℂ A A) {m : ℕ} (d : Fin m → ℕ)
    (hd_pos : ∀ i, 1 ≤ d i) (hd_inj : Function.Injective d)
    (A_parts : Fin (commonPeriod d) → A)
    (hA : AlgebraicIndependent K (fun p : Fin (commonPeriod d) × ℕ ↦ D^[p.2] (A_parts p.1))) :
    AlgebraicIndependent K (fun p : Fin m × ℕ ↦
      D^[p.2] (weightedPartSeries (commonPeriod d) A_parts (multInd (d p.1)))) :=
  squarePeriodicWeights_linearIndep_diff_indep D (fun i ↦ multInd (d i)) d hd_pos
    (fun i ℓ ↦ multInd_periodic (d i) ℓ) (multInd_linearIndependent hd_pos hd_inj) A_parts hA

end DFTAndPeriodicWeights

end
end CubicTheta.AllD
