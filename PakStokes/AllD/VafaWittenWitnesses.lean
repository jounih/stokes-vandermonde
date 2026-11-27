module

public import PakStokes.AllD.DepthTwoCommutator
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases

/-! # Arithmetic Theta Witnesses for Depth-2 Vafa–Witten `SU(3)` on `ℂℙ²`

Unconditional Lean 4 formalization from Mathlib (zero placeholders, standard foundations only,
pure exact `ℤ`/`ℚ` arithmetic) of the Bringmann–Nazaroglu (3.2) theta representation counts,
antisymmetric commutator pairings, infinite all-`n` witness families, flux symmetry, equal-total
collision witness, and all-order shifted Vandermonde nonvanishing:

1. **Exact Theta Quadratic Forms & Multiplicity Counts (`vwOuterForm`, `vwInnerForm`,
   `vwThetaSet`, `vwThetaCount`, `vwPairing`):**
   Formalizes the outer forms `3(j + (2ν + 3α)/6)²` and inner forms `(k + α/2)²` for channels
   `α ∈ {0, 1}` and flux sectors `ν ∈ ℤ`, verifies the exact table for `ν = 0, 1`, proves finiteness
   (`vwThetaSet_finite_and_card_le_two`), and links `vwPairing` directly to `commutatorPairing`.
2. **All-`n` Infinite Witness Families (`n ≥ 1`):**
   - `vwPairing_flux1_witness`: `vwPairing 1 (1/3) (n^2) = 2`
   - `vwPairing_flux0_vanishes_on_flux1_witness`: `vwPairing 0 (1/3) (n^2) = 0`
   - `vwPairing_flux0_witness`: `vwPairing 0 3 (n^2) = 4`
   - `vwPairing_flux1_vanishes_on_flux0_witness`: `vwPairing 1 3 (n^2) = 0`
   - `vwPairing_flux_neg1_eq_flux1`: `vwPairing (-1) a b = vwPairing 1 a b` for all `a, b : ℚ`.
3. **All-Order Vandermonde & Block-Diagonal Elimination (`vwWitness_vandermonde_ne_zero`,
   `vwWitness_blockMatrix_det_ne_zero`, `vwWitness_twoSector_minimal_degree_contradiction`):**
   Proves strictly nonzero determinants for BOTH witness Vandermonde families
   `((1/3 + (n+1)^2)^j)` and `((3 + (n+1)^2)^j)` and for the `2(r+1) × 2(r+1)` coupled
   two-sector block matrix at every jet order `r : ℕ`, connecting directly to the minimal-degree
   elimination engine in `PakStokes.AllD.DepthTwoCommutator`.
4. **Equal-Total Collision Witness (`vwCollision_equal_total`, `vwCollision_both_flux1_eq_two`):**
   Proves `1/3 + 9 = 16/3 + 4` with distinct ordered addresses `(1/3, 9) ≠ (16/3, 4)`, both
   having `vwPairing 1 = 2` and `vwPairing 0 = 0`.
-/

public section

namespace CubicTheta.AllD

open Finset Matrix Set
open scoped BigOperators

/-! ### 1. Exact Quadratic Forms, Theta Multiplicities & Antisymmetric Pairing -/

/-- Outer shift `(2ν + 3α) / 6` for flux sector `ν : ℤ` and channel `α : Fin 2`. -/
def vwOuterShift (ν : ℤ) (α : Fin 2) : ℚ :=
  ((2 * ν + 3 * (α.val : ℤ) : ℤ) : ℚ) / 6

/-- Inner shift `α / 2` for channel `α : Fin 2`. -/
def vwInnerShift (α : Fin 2) : ℚ :=
  ((α.val : ℤ) : ℚ) / 2

/-- Outer quadratic form `3 * (j + (2ν + 3α)/6)²` in units of `2π`. -/
def vwOuterForm (ν : ℤ) (α : Fin 2) (j : ℤ) : ℚ :=
  3 * ((j : ℚ) + vwOuterShift ν α) ^ 2

/-- Inner quadratic form `(k + α/2)²` in units of `2π`. -/
def vwInnerForm (α : Fin 2) (k : ℤ) : ℚ :=
  ((k : ℚ) + vwInnerShift α) ^ 2

theorem vwOuterForm_flux1_ch0 (j : ℤ) :
    vwOuterForm 1 0 j = ((3 * j + 1 : ℤ) : ℚ) ^ 2 / 3 := by
  simp only [vwOuterForm, vwOuterShift, Fin.val_zero]
  push_cast; ring

theorem vwOuterForm_flux1_ch1 (j : ℤ) :
    vwOuterForm 1 1 j = ((6 * j + 5 : ℤ) : ℚ) ^ 2 / 12 := by
  simp only [vwOuterForm, vwOuterShift, Fin.val_one]
  push_cast; ring

theorem vwOuterForm_flux0_ch0 (j : ℤ) :
    vwOuterForm 0 0 j = 3 * (j : ℚ) ^ 2 := by
  simp only [vwOuterForm, vwOuterShift, Fin.val_zero]
  push_cast; ring

theorem vwOuterForm_flux0_ch1 (j : ℤ) :
    vwOuterForm 0 1 j = 3 * ((j : ℚ) + 1 / 2) ^ 2 := by
  simp only [vwOuterForm, vwOuterShift, Fin.val_one]
  push_cast; ring

theorem vwInnerForm_ch0 (k : ℤ) : vwInnerForm 0 k = (k : ℚ) ^ 2 := by
  simp [vwInnerForm, vwInnerShift]

theorem vwInnerForm_ch1 (k : ℤ) : vwInnerForm 1 k = ((k : ℚ) + 1 / 2) ^ 2 := by
  simp [vwInnerForm, vwInnerShift]

/-- Set of integers `j : ℤ` realizing frequency `q : ℚ` under `scale * (j + shift)² = q`. -/
def vwThetaSet (shift scale q : ℚ) : Set ℤ :=
  {j : ℤ | scale * ((j : ℚ) + shift) ^ 2 = q}

/-- Exact representation multiplicity of frequency `q : ℚ` in `{j : ℤ | scale * (j + shift)² = q}`. -/
noncomputable def vwThetaCount (shift scale q : ℚ) : ℕ :=
  (vwThetaSet shift scale q).ncard

/-- Every nondegenerate (`scale ≠ 0`) quadratic theta representation set has at most `2` elements,
and in particular is finite. -/
theorem vwThetaSet_finite_and_card_le_two {shift scale q : ℚ} (hscale : scale ≠ 0) :
    (vwThetaSet shift scale q).Finite ∧ vwThetaCount shift scale q ≤ 2 := by
  let f : ℤ → ℚ := fun j => (j : ℚ) + shift
  have hf : Function.Injective f := fun a b hab => by
    have : (a : ℚ) = (b : ℚ) := by linarith
    exact Int.cast_injective this
  by_cases hne : (vwThetaSet shift scale q).Nonempty
  · obtain ⟨j₀, hj₀⟩ := hne
    have hsub : f '' vwThetaSet shift scale q ⊆ {f j₀, -f j₀} := by
      rintro x ⟨j, hj, rfl⟩
      have hsq : (f j) ^ 2 = (f j₀) ^ 2 :=
        mul_left_cancel₀ hscale (hj.trans hj₀.symm)
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · exact Or.inl h
      · exact Or.inr h
    have hfin_img : (f '' vwThetaSet shift scale q).Finite :=
      (Set.toFinite ({f j₀, -f j₀} : Set ℚ)).subset hsub
    have hfin : (vwThetaSet shift scale q).Finite := hfin_img.of_finite_image hf.injOn
    have hcard : vwThetaCount shift scale q ≤ 2 := by
      unfold vwThetaCount
      rw [← Set.ncard_image_of_injective (vwThetaSet shift scale q) hf]
      calc (f '' vwThetaSet shift scale q).ncard
          ≤ ({f j₀, -f j₀} : Set ℚ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
            by_cases h0 : f j₀ = -f j₀
            · rw [← h0, Set.pair_eq_singleton, Set.ncard_singleton]; omega
            · rw [Set.ncard_pair h0]
    exact ⟨hfin, hcard⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [vwThetaCount, hne]

/-- Antisymmetric commutator pairing across channels `α ∈ {0, 1}` for flux sector `ν : ℤ` and
ordered rational frequency pair `(a, b)`:
`vwPairing ν a b = ∑_{α = 0, 1} (outer_{ν, α}(a) * inner_α(b) - outer_{ν, α}(b) * inner_α(a))`. -/
noncomputable def vwPairing (ν : ℤ) (a b : ℚ) : ℤ :=
  ∑ α : Fin 2,
    ((vwThetaCount (vwOuterShift ν α) 3 a : ℤ) * (vwThetaCount (vwInnerShift α) 1 b : ℤ) -
      (vwThetaCount (vwOuterShift ν α) 3 b : ℤ) * (vwThetaCount (vwInnerShift α) 1 a : ℤ))

theorem vwPairing_eq_commutatorPairing (ν : ℤ) (a b : ℚ) :
    vwPairing ν a b =
      commutatorPairing
        (fun α : Fin 2 => (vwThetaCount (vwOuterShift ν α) 3 b : ℤ))
        (fun α : Fin 2 => (vwThetaCount (vwInnerShift α) 1 b : ℤ))
        (fun α : Fin 2 => (vwThetaCount (vwOuterShift ν α) 3 a : ℤ))
        (fun α : Fin 2 => (vwThetaCount (vwInnerShift α) 1 a : ℤ)) := by
  rw [vwPairing, commutatorPairing_eq]

theorem vwPairing_antisymm (ν : ℤ) (a b : ℚ) : vwPairing ν b a = -vwPairing ν a b := by
  rw [vwPairing_eq_commutatorPairing, vwPairing_eq_commutatorPairing, commutatorPairing_antisymm]

theorem vwPairing_self_zero (ν : ℤ) (a : ℚ) : vwPairing ν a a = 0 := by
  rw [vwPairing_eq_commutatorPairing, commutatorPairing_self_zero]

/-! ### 2. Flux Symmetry `ν = -1` vs `ν = 1` -/

theorem vwThetaCount_outer_neg1_eq_flux1 (α : Fin 2) (q : ℚ) :
    vwThetaCount (vwOuterShift (-1) α) 3 q = vwThetaCount (vwOuterShift 1 α) 3 q := by
  unfold vwThetaCount
  fin_cases α
  · change (vwThetaSet (vwOuterShift (-1) 0) 3 q).ncard =
      (vwThetaSet (vwOuterShift 1 0) 3 q).ncard
    have himg : vwThetaSet (vwOuterShift (-1) 0) 3 q =
        (fun j : ℤ => -j) '' vwThetaSet (vwOuterShift 1 0) 3 q := by
      ext j
      simp only [Set.mem_image, vwThetaSet, Set.mem_ofPred_eq, vwOuterShift, Fin.val_zero]
      constructor
      · intro hj
        refine ⟨-j, ?_, neg_neg j⟩
        convert hj using 1
        push_cast; ring
      · rintro ⟨j', hj', rfl⟩
        convert hj' using 1
        push_cast; ring
    rw [himg, Set.ncard_image_of_injective _ neg_injective]
  · change (vwThetaSet (vwOuterShift (-1) 1) 3 q).ncard =
      (vwThetaSet (vwOuterShift 1 1) 3 q).ncard
    have hbij : Function.Injective (fun j : ℤ => -j - 1) := fun a b h => by
      dsimp only at h; omega
    have himg : vwThetaSet (vwOuterShift (-1) 1) 3 q =
        (fun j : ℤ => -j - 1) '' vwThetaSet (vwOuterShift 1 1) 3 q := by
      ext j
      simp only [Set.mem_image, vwThetaSet, Set.mem_ofPred_eq, vwOuterShift, Fin.val_one]
      constructor
      · intro hj
        refine ⟨-j - 1, ?_, by omega⟩
        convert hj using 1
        push_cast; ring
      · rintro ⟨j', hj', rfl⟩
        convert hj' using 1
        push_cast; ring
    rw [himg, Set.ncard_image_of_injective _ hbij]

/-- Exact flux reflection symmetry: sectors `ν = -1` and `ν = 1` have identical pairings at every
rational frequency pair `(a, b)`. -/
theorem vwPairing_flux_neg1_eq_flux1 (a b : ℚ) :
    vwPairing (-1) a b = vwPairing 1 a b := by
  unfold vwPairing
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [vwThetaCount_outer_neg1_eq_flux1, vwThetaCount_outer_neg1_eq_flux1]

/-! ### 3. Core Modular & 3-Adic Non-Representation Lemmas -/

/-- Infinite descent via `Nat.prime_three.dvd_mul`: no positive square equals `3 j²`. -/
theorem three_mul_sq_ne_sq_nat : ∀ {k : ℕ}, 1 ≤ k → ∀ j : ℕ, 3 * j ^ 2 ≠ k ^ 2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk j h
    have h3k2 : 3 ∣ k * k := ⟨j ^ 2, by nlinarith⟩
    have h3k : 3 ∣ k := (Nat.prime_three.dvd_mul.mp h3k2).elim id id
    obtain ⟨k', rfl⟩ := h3k
    have h3j2 : 3 ∣ j * j := ⟨k' ^ 2, by nlinarith⟩
    have h3j : 3 ∣ j := (Nat.prime_three.dvd_mul.mp h3j2).elim id id
    obtain ⟨j', rfl⟩ := h3j
    have hlt : k' < 3 * k' := by omega
    have hk' : 1 ≤ k' := by omega
    exact ih k' hlt hk' j' (by nlinarith)

theorem three_mul_sq_ne_sq_int {k : ℕ} (hk : 1 ≤ k) (j : ℤ) :
    3 * j ^ 2 ≠ (k : ℤ) ^ 2 := by
  intro h
  have hnat : 3 * j.natAbs ^ 2 = k ^ 2 := by
    have h' : ((3 * j.natAbs ^ 2 : ℕ) : ℤ) = ((k ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [sq_abs]; exact h
    exact Int.ofNat.inj h'
  exact three_mul_sq_ne_sq_nat hk j.natAbs hnat

private lemma rat_eq_of_int_cast {a b : ℤ} (h : (a : ℚ) = (b : ℚ)) : a = b :=
  Int.cast_injective h

/-! ### 4. Exact Theta Counts for Both Channels and Both Witnesses -/

/-- Inner `α = 0` (`k² = n²`) has multiplicity `2` (`k = ±n`) for every `n ≥ 1`. -/
theorem vwThetaCount_inner0_sq (n : ℕ) (hn : 1 ≤ n) :
    vwThetaCount (vwInnerShift 0) 1 ((n : ℚ) ^ 2) = 2 := by
  have hset : vwThetaSet (vwInnerShift 0) 1 ((n : ℚ) ^ 2) = {(n : ℤ), -(n : ℤ)} := by
    ext k
    simp only [vwThetaSet, vwInnerShift, Fin.val_zero, Nat.cast_zero, Int.cast_zero, zero_div,
      add_zero, one_mul, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rw [sq_eq_sq_iff_eq_or_eq_neg]
    constructor
    · rintro (h | h)
      · exact Or.inl (rat_eq_of_int_cast (by simpa using h))
      · exact Or.inr (rat_eq_of_int_cast (by simpa using h))
    · rintro (rfl | rfl) <;> simp
  rw [vwThetaCount, hset, Set.ncard_pair]
  omega

/-- Inner `α = 0` vanishes at `m / 3` whenever `¬ 3 ∣ m` (covers `1/3` and `16/3`). -/
theorem vwThetaCount_inner0_div_three {m : ℤ} (hm : ¬ 3 ∣ m) :
    vwThetaCount (vwInnerShift 0) 1 ((m : ℚ) / 3) = 0 := by
  have hset : vwThetaSet (vwInnerShift 0) 1 ((m : ℚ) / 3) = ∅ := by
    ext k
    simp only [vwThetaSet, vwInnerShift, Fin.val_zero, Nat.cast_zero, Int.cast_zero, zero_div,
      add_zero, one_mul, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hz : 3 * k ^ 2 = m := rat_eq_of_int_cast (by push_cast; linarith)
    exact hm ⟨k ^ 2, hz.symm⟩
  rw [vwThetaCount, hset, Set.ncard_empty]

/-- Inner `α = 0` vanishes at `3` (since `3` is not a square). -/
theorem vwThetaCount_inner0_three : vwThetaCount (vwInnerShift 0) 1 3 = 0 := by
  have hset : vwThetaSet (vwInnerShift 0) 1 3 = ∅ := by
    ext k
    simp only [vwThetaSet, vwInnerShift, Fin.val_zero, Nat.cast_zero, Int.cast_zero, zero_div,
      add_zero, one_mul, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hz : k ^ 2 = 3 := rat_eq_of_int_cast (by push_cast; exact h)
    have hcases : k ≤ -2 ∨ k = -1 ∨ k = 0 ∨ k = 1 ∨ 2 ≤ k := by omega
    rcases hcases with h1 | h2 | h3 | h4 | h5 <;> nlinarith
  rw [vwThetaCount, hset, Set.ncard_empty]

/-- Inner `α = 1` (`(k + 1/2)² = m`) vanishes at every integer `m : ℤ` (`4(k²+k) + 1 ≠ 4m`). -/
theorem vwThetaCount_inner1_int (m : ℤ) :
    vwThetaCount (vwInnerShift 1) 1 (m : ℚ) = 0 := by
  have hset : vwThetaSet (vwInnerShift 1) 1 (m : ℚ) = ∅ := by
    ext k
    simp only [vwThetaSet, vwInnerShift, Fin.val_one, Nat.cast_one, Int.cast_one, one_mul,
      Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hz : (2 * k + 1) ^ 2 = 4 * m := rat_eq_of_int_cast (by push_cast; linarith)
    have hlin : 4 * (k ^ 2 + k) + 1 = 4 * m := by linarith
    omega
  rw [vwThetaCount, hset, Set.ncard_empty]

/-- Inner `α = 1` vanishes at `m / 3` whenever `¬ 3 ∣ m` (`3(2k+1)² = 4m` forces `3 ∣ m`). -/
theorem vwThetaCount_inner1_div_three {m : ℤ} (hm : ¬ 3 ∣ m) :
    vwThetaCount (vwInnerShift 1) 1 ((m : ℚ) / 3) = 0 := by
  have hset : vwThetaSet (vwInnerShift 1) 1 ((m : ℚ) / 3) = ∅ := by
    ext k
    simp only [vwThetaSet, vwInnerShift, Fin.val_one, Nat.cast_one, Int.cast_one, one_mul,
      Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hz : 3 * (2 * k + 1) ^ 2 = 4 * m := rat_eq_of_int_cast (by push_cast; linarith)
    exact hm ⟨(2 * k + 1) ^ 2 - m, by linarith⟩
  rw [vwThetaCount, hset, Set.ncard_empty]

/-- Outer `ν = 1, α = 0` (`(3j + 1)² / 3 = 1/3`) has multiplicity `1` (`j = 0`). -/
theorem vwThetaCount_outer10_third :
    vwThetaCount (vwOuterShift 1 0) 3 (1 / 3) = 1 := by
  have hset : vwThetaSet (vwOuterShift 1 0) 3 (1 / 3) = {0} := by
    ext j
    simp only [vwThetaSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      have hf : vwOuterForm 1 0 j = 1 / 3 := h
      rw [vwOuterForm_flux1_ch0] at hf
      have hz : (3 * j + 1) ^ 2 = 1 := rat_eq_of_int_cast (by push_cast at hf ⊢; linarith)
      have hor : 3 * j + 1 = 1 ∨ 3 * j + 1 = -1 := by
        simpa using sq_eq_sq_iff_eq_or_eq_neg.mp (show (3 * j + 1) ^ 2 = 1 ^ 2 by linarith)
      omega
    · rintro rfl
      change vwOuterForm 1 0 0 = 1 / 3
      rw [vwOuterForm_flux1_ch0]; norm_num
  rw [vwThetaCount, hset, Set.ncard_singleton]

/-- Outer `ν = 1, α = 0` (`(3j + 1)² / 3 = 16/3`) has multiplicity `1` (`j = 1`). -/
theorem vwThetaCount_outer10_sixteen_thirds :
    vwThetaCount (vwOuterShift 1 0) 3 (16 / 3) = 1 := by
  have hset : vwThetaSet (vwOuterShift 1 0) 3 (16 / 3) = {1} := by
    ext j
    simp only [vwThetaSet, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro h
      have hf : vwOuterForm 1 0 j = 16 / 3 := h
      rw [vwOuterForm_flux1_ch0] at hf
      have hz : (3 * j + 1) ^ 2 = 16 := rat_eq_of_int_cast (by push_cast at hf ⊢; linarith)
      have hor : 3 * j + 1 = 4 ∨ 3 * j + 1 = -4 := by
        simpa using sq_eq_sq_iff_eq_or_eq_neg.mp (show (3 * j + 1) ^ 2 = 4 ^ 2 by linarith)
      omega
    · rintro rfl
      change vwOuterForm 1 0 1 = 16 / 3
      rw [vwOuterForm_flux1_ch0]; norm_num
  rw [vwThetaCount, hset, Set.ncard_singleton]

/-- Outer `ν = 1, α = 0` vanishes at every integer `m : ℤ` (`(3j+1)² = 3(3j²+2j) + 1 ≠ 3m`). -/
theorem vwThetaCount_outer10_int (m : ℤ) :
    vwThetaCount (vwOuterShift 1 0) 3 (m : ℚ) = 0 := by
  have hset : vwThetaSet (vwOuterShift 1 0) 3 (m : ℚ) = ∅ := by
    ext j
    simp only [vwThetaSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hf : vwOuterForm 1 0 j = (m : ℚ) := h
    rw [vwOuterForm_flux1_ch0] at hf
    have hz : (3 * j + 1) ^ 2 = 3 * m := rat_eq_of_int_cast (by push_cast at hf ⊢; linarith)
    have hlin : 3 * (3 * j ^ 2 + 2 * j) + 1 = 3 * m := by linarith
    omega
  rw [vwThetaCount, hset, Set.ncard_empty]

/-- Outer `ν = 0, α = 0` (`3j² = 3`) has multiplicity `2` (`j = ±1`). -/
theorem vwThetaCount_outer00_three :
    vwThetaCount (vwOuterShift 0 0) 3 3 = 2 := by
  have hset : vwThetaSet (vwOuterShift 0 0) 3 3 = {1, -1} := by
    ext j
    simp only [vwThetaSet, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have hf : vwOuterForm 0 0 j = 3 := h
      rw [vwOuterForm_flux0_ch0] at hf
      have hz : j ^ 2 = 1 := rat_eq_of_int_cast (by push_cast; linarith)
      simpa using sq_eq_sq_iff_eq_or_eq_neg.mp (show j ^ 2 = 1 ^ 2 by linarith)
    · rintro (rfl | rfl) <;> (change vwOuterForm 0 0 _ = 3; rw [vwOuterForm_flux0_ch0]; norm_num)
  rw [vwThetaCount, hset, Set.ncard_pair (by decide)]

/-- Outer `ν = 0, α = 0` vanishes at `m / 3` whenever `¬ 3 ∣ m` (covers `1/3` and `16/3`). -/
theorem vwThetaCount_outer00_div_three {m : ℤ} (hm : ¬ 3 ∣ m) :
    vwThetaCount (vwOuterShift 0 0) 3 ((m : ℚ) / 3) = 0 := by
  have hset : vwThetaSet (vwOuterShift 0 0) 3 ((m : ℚ) / 3) = ∅ := by
    ext j
    simp only [vwThetaSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hf : vwOuterForm 0 0 j = (m : ℚ) / 3 := h
    rw [vwOuterForm_flux0_ch0] at hf
    have hz : 9 * j ^ 2 = m := rat_eq_of_int_cast (by push_cast; linarith)
    exact hm ⟨3 * j ^ 2, by linarith⟩
  rw [vwThetaCount, hset, Set.ncard_empty]

/-- Outer `ν = 0, α = 0` (`3j² = n²`) vanishes for every `n ≥ 1` by 3-adic infinite descent. -/
theorem vwThetaCount_outer00_sq (n : ℕ) (hn : 1 ≤ n) :
    vwThetaCount (vwOuterShift 0 0) 3 ((n : ℚ) ^ 2) = 0 := by
  have hset : vwThetaSet (vwOuterShift 0 0) 3 ((n : ℚ) ^ 2) = ∅ := by
    ext j
    simp only [vwThetaSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hf : vwOuterForm 0 0 j = (n : ℚ) ^ 2 := h
    rw [vwOuterForm_flux0_ch0] at hf
    have hz : 3 * j ^ 2 = (n : ℤ) ^ 2 := rat_eq_of_int_cast (by push_cast; exact hf)
    exact three_mul_sq_ne_sq_int hn j hz
  rw [vwThetaCount, hset, Set.ncard_empty]

/-! ### 5. Main All-`n` Witness Theorems (`n ≥ 1`) & Equal-Total Collision -/

/-- **Infinite Witness Family 1 (Flux Sector `ν = 1`):**
For every `n ≥ 1`, `vwPairing 1 (1/3) (n^2) = 2`. -/
theorem vwPairing_flux1_witness (n : ℕ) (hn : 1 ≤ n) :
    vwPairing 1 (1 / 3) ((n : ℚ) ^ 2) = 2 := by
  have hsq : ((n : ℚ) ^ 2) = (((n : ℤ) ^ 2 : ℤ) : ℚ) := by push_cast; rfl
  have h13 : (1 / 3 : ℚ) = ((1 : ℤ) : ℚ) / 3 := by norm_num
  unfold vwPairing
  rw [Fin.sum_univ_two]
  have h_in0_b := vwThetaCount_inner0_sq n hn
  have h_in0_a : vwThetaCount (vwInnerShift 0) 1 (1 / 3) = 0 := by
    rw [h13]; exact vwThetaCount_inner0_div_three (by omega)
  have h_in1_b : vwThetaCount (vwInnerShift 1) 1 ((n : ℚ) ^ 2) = 0 := by
    rw [hsq]; exact vwThetaCount_inner1_int ((n : ℤ) ^ 2)
  have h_in1_a : vwThetaCount (vwInnerShift 1) 1 (1 / 3) = 0 := by
    rw [h13]; exact vwThetaCount_inner1_div_three (by omega)
  have h_out10_a := vwThetaCount_outer10_third
  have h_out10_b : vwThetaCount (vwOuterShift 1 0) 3 ((n : ℚ) ^ 2) = 0 := by
    rw [hsq]; exact vwThetaCount_outer10_int ((n : ℤ) ^ 2)
  rw [h_in0_b, h_in0_a, h_in1_b, h_in1_a, h_out10_a, h_out10_b]
  norm_num

/-- **Cross-Sector Vanishing on Witness 1:**
For every `n ≥ 1`, `vwPairing 0 (1/3) (n^2) = 0`. -/
theorem vwPairing_flux0_vanishes_on_flux1_witness (n : ℕ) (hn : 1 ≤ n) :
    vwPairing 0 (1 / 3) ((n : ℚ) ^ 2) = 0 := by
  have hsq : ((n : ℚ) ^ 2) = (((n : ℤ) ^ 2 : ℤ) : ℚ) := by push_cast; rfl
  have h13 : (1 / 3 : ℚ) = ((1 : ℤ) : ℚ) / 3 := by norm_num
  unfold vwPairing
  rw [Fin.sum_univ_two]
  have h_in0_a : vwThetaCount (vwInnerShift 0) 1 (1 / 3) = 0 := by
    rw [h13]; exact vwThetaCount_inner0_div_three (by omega)
  have h_in1_b : vwThetaCount (vwInnerShift 1) 1 ((n : ℚ) ^ 2) = 0 := by
    rw [hsq]; exact vwThetaCount_inner1_int ((n : ℤ) ^ 2)
  have h_in1_a : vwThetaCount (vwInnerShift 1) 1 (1 / 3) = 0 := by
    rw [h13]; exact vwThetaCount_inner1_div_three (by omega)
  have h_out00_a : vwThetaCount (vwOuterShift 0 0) 3 (1 / 3) = 0 := by
    rw [h13]; exact vwThetaCount_outer00_div_three (by omega)
  have h_out00_b := vwThetaCount_outer00_sq n hn
  rw [h_in0_a, h_in1_b, h_in1_a, h_out00_a, h_out00_b]
  norm_num

/-- **Infinite Witness Family 2 (Flux Sector `ν = 0`):**
For every `n ≥ 1`, `vwPairing 0 3 (n^2) = 4`. -/
theorem vwPairing_flux0_witness (n : ℕ) (hn : 1 ≤ n) :
    vwPairing 0 3 ((n : ℚ) ^ 2) = 4 := by
  have hsq : ((n : ℚ) ^ 2) = (((n : ℤ) ^ 2 : ℤ) : ℚ) := by push_cast; rfl
  have h3 : (3 : ℚ) = ((3 : ℤ) : ℚ) := by norm_num
  unfold vwPairing
  rw [Fin.sum_univ_two]
  have h_in0_b := vwThetaCount_inner0_sq n hn
  have h_in0_a := vwThetaCount_inner0_three
  have h_in1_b : vwThetaCount (vwInnerShift 1) 1 ((n : ℚ) ^ 2) = 0 := by
    rw [hsq]; exact vwThetaCount_inner1_int ((n : ℤ) ^ 2)
  have h_in1_a : vwThetaCount (vwInnerShift 1) 1 3 = 0 := by
    rw [h3]; exact vwThetaCount_inner1_int 3
  have h_out00_a := vwThetaCount_outer00_three
  have h_out00_b := vwThetaCount_outer00_sq n hn
  rw [h_in0_b, h_in0_a, h_in1_b, h_in1_a, h_out00_a, h_out00_b]
  norm_num

/-- **Cross-Sector Vanishing on Witness 2:**
For every `n ≥ 1`, `vwPairing 1 3 (n^2) = 0`. -/
theorem vwPairing_flux1_vanishes_on_flux0_witness (n : ℕ) (hn : 1 ≤ n) :
    vwPairing 1 3 ((n : ℚ) ^ 2) = 0 := by
  let _ := hn
  have hsq : ((n : ℚ) ^ 2) = (((n : ℤ) ^ 2 : ℤ) : ℚ) := by push_cast; rfl
  have h3 : (3 : ℚ) = ((3 : ℤ) : ℚ) := by norm_num
  unfold vwPairing
  rw [Fin.sum_univ_two]
  have h_in0_a := vwThetaCount_inner0_three
  have h_in1_b : vwThetaCount (vwInnerShift 1) 1 ((n : ℚ) ^ 2) = 0 := by
    rw [hsq]; exact vwThetaCount_inner1_int ((n : ℤ) ^ 2)
  have h_in1_a : vwThetaCount (vwInnerShift 1) 1 3 = 0 := by
    rw [h3]; exact vwThetaCount_inner1_int 3
  have h_out10_a : vwThetaCount (vwOuterShift 1 0) 3 3 = 0 := by
    rw [h3]; exact vwThetaCount_outer10_int 3
  have h_out10_b : vwThetaCount (vwOuterShift 1 0) 3 ((n : ℚ) ^ 2) = 0 := by
    rw [hsq]; exact vwThetaCount_outer10_int ((n : ℤ) ^ 2)
  rw [h_in0_a, h_in1_b, h_in1_a, h_out10_a, h_out10_b]
  norm_num

/-- **Equal-Total Collision Witness `(1/3, 9)` vs `(16/3, 4)`:**
Distinct ordered addresses share the exact same total frequency `28/3`, and BOTH survive with
`vwPairing 1 = 2` (and `vwPairing 0 = 0`). -/
theorem vwCollision_equal_total : (1 / 3 : ℚ) + 9 = (16 / 3 : ℚ) + 4 := by norm_num

theorem vwCollision_distinct_addresses : ((1 / 3 : ℚ), (9 : ℚ)) ≠ (16 / 3, 4) := by
  intro h
  have h1 : (1 / 3 : ℚ) = 16 / 3 := congrArg Prod.fst h
  norm_num at h1

theorem vwCollision_both_flux1_eq_two :
    vwPairing 1 (1 / 3) 9 = 2 ∧ vwPairing 1 (16 / 3) 4 = 2 := by
  constructor
  · have h9 : (9 : ℚ) = ((3 : ℕ) : ℚ) ^ 2 := by norm_num
    rw [h9]
    exact vwPairing_flux1_witness 3 (by omega)
  · have h4 : (4 : ℚ) = ((2 : ℕ) : ℚ) ^ 2 := by norm_num
    have h4z : (4 : ℚ) = ((4 : ℤ) : ℚ) := by norm_num
    have h163 : (16 / 3 : ℚ) = ((16 : ℤ) : ℚ) / 3 := by norm_num
    unfold vwPairing
    rw [Fin.sum_univ_two]
    have h_in0_b : vwThetaCount (vwInnerShift 0) 1 4 = 2 := by
      rw [h4]; exact vwThetaCount_inner0_sq 2 (by omega)
    have h_in0_a : vwThetaCount (vwInnerShift 0) 1 (16 / 3) = 0 := by
      rw [h163]; exact vwThetaCount_inner0_div_three (by omega)
    have h_in1_b : vwThetaCount (vwInnerShift 1) 1 4 = 0 := by
      rw [h4z]; exact vwThetaCount_inner1_int 4
    have h_in1_a : vwThetaCount (vwInnerShift 1) 1 (16 / 3) = 0 := by
      rw [h163]; exact vwThetaCount_inner1_div_three (by omega)
    have h_out10_a := vwThetaCount_outer10_sixteen_thirds
    have h_out10_b : vwThetaCount (vwOuterShift 1 0) 3 4 = 0 := by
      rw [h4z]; exact vwThetaCount_outer10_int 4
    rw [h_in0_b, h_in0_a, h_in1_b, h_in1_a, h_out10_a, h_out10_b]
    norm_num

theorem vwCollision_both_flux0_eq_zero :
    vwPairing 0 (1 / 3) 9 = 0 ∧ vwPairing 0 (16 / 3) 4 = 0 := by
  constructor
  · have h9 : (9 : ℚ) = ((3 : ℕ) : ℚ) ^ 2 := by norm_num
    rw [h9]
    exact vwPairing_flux0_vanishes_on_flux1_witness 3 (by omega)
  · have h4z : (4 : ℚ) = ((4 : ℤ) : ℚ) := by norm_num
    have h163 : (16 / 3 : ℚ) = ((16 : ℤ) : ℚ) / 3 := by norm_num
    unfold vwPairing
    rw [Fin.sum_univ_two]
    have h_in0_a : vwThetaCount (vwInnerShift 0) 1 (16 / 3) = 0 := by
      rw [h163]; exact vwThetaCount_inner0_div_three (by omega)
    have h_in1_b : vwThetaCount (vwInnerShift 1) 1 4 = 0 := by
      rw [h4z]; exact vwThetaCount_inner1_int 4
    have h_in1_a : vwThetaCount (vwInnerShift 1) 1 (16 / 3) = 0 := by
      rw [h163]; exact vwThetaCount_inner1_div_three (by omega)
    have h_out00_a : vwThetaCount (vwOuterShift 0 0) 3 (16 / 3) = 0 := by
      rw [h163]; exact vwThetaCount_outer00_div_three (by omega)
    rw [h_in0_a, h_in1_b, h_in1_a, h_out00_a]
    norm_num

/-! ### 6. All-Order Vandermonde Nonvanishing & Two-Sector Elimination Hook -/

/-- Strictly increasing positive square frequencies `b_n = (n + 1)²` on `Fin (r + 1)`. -/
def vwSquareSeq (r : ℕ) : Fin (r + 1) → ℚ :=
  fun n => ((n.val + 1 : ℚ) ^ 2)

theorem vwSquareSeq_injective (r : ℕ) : Function.Injective (vwSquareSeq r) := by
  intro i j hij
  have hsq : ((i.val + 1 : ℚ) ^ 2) = ((j.val + 1 : ℚ) ^ 2) := hij
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · have hnat : ((i.val + 1 : ℕ) : ℚ) = ((j.val + 1 : ℕ) : ℚ) := by push_cast; exact h
    have heq : i.val + 1 = j.val + 1 := Nat.cast_injective hnat
    exact Fin.ext (by omega)
  · have hpos : (0 : ℚ) < (i.val + 1 : ℚ) + (j.val + 1 : ℚ) := by positivity
    linarith

/-- **All-Order Vandermonde Nonvanishing for Both Witnesses:**
For EVERY jet order `r : ℕ`, both shifted Vandermonde matrices `((1/3 + (n+1)^2)^j)` and
`((3 + (n+1)^2)^j)` have strictly nonzero determinant over `ℚ`. -/
theorem vwWitness_vandermonde_ne_zero (r : ℕ) :
    (shiftedVandermonde (1 / 3 : ℚ) (vwSquareSeq r)).det ≠ 0 ∧
      (shiftedVandermonde (3 : ℚ) (vwSquareSeq r)).det ≠ 0 :=
  ⟨shiftedVandermonde_det_ne_zero (1 / 3 : ℚ) (vwSquareSeq r) (vwSquareSeq_injective r),
   shiftedVandermonde_det_ne_zero (3 : ℚ) (vwSquareSeq r) (vwSquareSeq_injective r)⟩

/-- Exact `2(r + 1) × 2(r + 1)` coupled two-sector derivative matrix built from the exact
Vafa–Witten pairing values at `(3, (n+1)²)` (sector `0` block) and `(1/3, (n+1)²)` (sector `1`
block) over any `ℚ`-algebra `R`. -/
noncomputable def vwTwoSectorBlockMatrix {R : Type*} [CommRing R] [Algebra ℚ R] (r : ℕ) :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) R :=
  Matrix.fromBlocks
    (Matrix.of fun i j : Fin (r + 1) =>
      (vwPairing 0 3 (((i.val + 1 : ℕ) : ℚ) ^ 2) : R) *
        (algebraMap ℚ R (3 + vwSquareSeq r i)) ^ (j : ℕ))
    (Matrix.of fun i j : Fin (r + 1) =>
      (vwPairing 1 3 (((i.val + 1 : ℕ) : ℚ) ^ 2) : R) *
        (algebraMap ℚ R (3 + vwSquareSeq r i)) ^ (j : ℕ))
    (Matrix.of fun i j : Fin (r + 1) =>
      (vwPairing 0 (1 / 3) (((i.val + 1 : ℕ) : ℚ) ^ 2) : R) *
        (algebraMap ℚ R (1 / 3 + vwSquareSeq r i)) ^ (j : ℕ))
    (Matrix.of fun i j : Fin (r + 1) =>
      (vwPairing 1 (1 / 3) (((i.val + 1 : ℕ) : ℚ) ^ 2) : R) *
        (algebraMap ℚ R (1 / 3 + vwSquareSeq r i)) ^ (j : ℕ))

/-- Over any `CharZero` integral domain `R` with `[Algebra ℚ R]`, the coupled `2(r + 1) × 2(r + 1)`
Vafa–Witten witness matrix decouples identically into diagonal blocks with multipliers `4` and `2`
and has strictly nonzero determinant for every jet order `r : ℕ`. -/
theorem vwWitness_blockMatrix_det_ne_zero {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [Algebra ℚ R] (r : ℕ) :
    (vwTwoSectorBlockMatrix (R := R) r).det ≠ 0 := by
  have hblock :
      vwTwoSectorBlockMatrix (R := R) r =
        Matrix.fromBlocks
          (Matrix.diagonal (fun _ : Fin (r + 1) => (4 : R)) *
            shiftedVandermonde (algebraMap ℚ R 3) (fun i => algebraMap ℚ R (vwSquareSeq r i)))
          0
          0
          (Matrix.diagonal (fun _ : Fin (r + 1) => (2 : R)) *
            shiftedVandermonde (algebraMap ℚ R (1 / 3))
              (fun i => algebraMap ℚ R (vwSquareSeq r i))) := by
    unfold vwTwoSectorBlockMatrix
    congr 1
    · ext i j
      simp only [Matrix.of_apply, Matrix.diagonal_mul, shiftedVandermonde_apply, map_add]
      rw [vwPairing_flux0_witness (i.val + 1) (by omega)]
      norm_num
    · ext i j
      simp only [Matrix.of_apply, Matrix.zero_apply]
      rw [vwPairing_flux1_vanishes_on_flux0_witness (i.val + 1) (by omega)]
      simp
    · ext i j
      simp only [Matrix.of_apply, Matrix.zero_apply]
      rw [vwPairing_flux0_vanishes_on_flux1_witness (i.val + 1) (by omega)]
      simp
    · ext i j
      simp only [Matrix.of_apply, Matrix.diagonal_mul, shiftedVandermonde_apply, map_add]
      rw [vwPairing_flux1_witness (i.val + 1) (by omega)]
      norm_num
  rw [hblock]
  have hinjQ : Function.Injective (algebraMap ℚ R) := RingHom.injective (algebraMap ℚ R)
  exact twoSector_blockVandermonde_det_ne_zero
    (algebraMap ℚ R 3) (algebraMap ℚ R (1 / 3))
    (fun i => algebraMap ℚ R (vwSquareSeq r i))
    (fun i => algebraMap ℚ R (vwSquareSeq r i))
    (fun _ => (4 : R)) (fun _ => (2 : R))
    (hinjQ.comp (vwSquareSeq_injective r))
    (hinjQ.comp (vwSquareSeq_injective r))
    (fun _ => by norm_num) (fun _ => by norm_num)

/-- **End-to-End Vafa–Witten Two-Sector Minimal-Degree Elimination Theorem:**
Over any `CharZero` integral domain `K` injectively embedded in a `CharZero` domain `B` with
`[Algebra ℚ B]`, no nonzero minimal-total-degree polynomial relation `R` among the two order-`r`
flux jets `(V₀, V₁)` can survive extraction of the two infinite witness families `(3, (n+1)²)`
and `(1/3, (n+1)²)`. -/
theorem vwWitness_twoSector_minimal_degree_contradiction
    {K B : Type*} [CommRing K] [IsDomain K] [CharZero K]
    [CommRing B] [IsDomain B] [CharZero B] [Algebra K B] [Algebra ℚ B]
    (hinj : Function.Injective (algebraMap K B))
    {r : ℕ} (V : Fin (r + 1) ⊕ Fin (r + 1) → B)
    (R : MvPolynomial (Fin (r + 1) ⊕ Fin (r + 1)) K)
    (hR_ne : R ≠ 0) (hR_ann : MvPolynomial.aeval V R = 0)
    (hR_min : ∀ Q : MvPolynomial (Fin (r + 1) ⊕ Fin (r + 1)) K,
      Q ≠ 0 → MvPolynomial.aeval V Q = 0 → R.totalDegree ≤ Q.totalDegree)
    (hrows : ∀ i : Fin (r + 1) ⊕ Fin (r + 1),
      ∑ j : Fin (r + 1) ⊕ Fin (r + 1),
        vwTwoSectorBlockMatrix (R := B) r i j *
          MvPolynomial.aeval V (MvPolynomial.pderiv j R) = 0) :
    False :=
  minimal_degree_elimination_of_nonsingular_matrix hinj V R hR_ne hR_ann hR_min
    (vwTwoSectorBlockMatrix (R := B) r) (vwWitness_blockMatrix_det_ne_zero r) hrows

end CubicTheta.AllD
