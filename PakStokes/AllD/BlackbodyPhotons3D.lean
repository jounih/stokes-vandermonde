module

public import PakStokes.AllD.JumpPointMultivariate
public import PakStokes.AllD.Bec3DDiffTrans
public import Mathlib.NumberTheory.SumFourSquares
public import Mathlib.NumberTheory.LSeries.PrimesInAP
public import Mathlib.NumberTheory.SumTwoSquares
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import all PakStokes.AllD.JumpPointMultivariate
import all PakStokes.AllD.Bec3DDiffTrans
import all PakStokes.AllD.Bec3DAnalytic
import all PakStokes.AllD.BesicovitchCore

/-! # Wave 12 (Module 1): Physical Relativistic Blackbody Photon Gases (`2D`, `3D`, `4D`) — Unconditional Differential Transcendence & Joint Independence

Establishes **100% unconditionally from Mathlib** (zero placeholders, standard assumptions only):

1. **Exact Lattice Representation Counts (`r2Count`, `r3Count`, `r4Count`) & 3-Class Separation:**
   - `r2Count_pos_of_prime_mod_four_eq_one` (Fermat two-square theorem `p ≡ 1 (mod 4) → r₂(p) ≥ 1`),
   - `r2Count_eq_zero_of_odd_val_prime_mod_four_eq_three` &
     `r2Count_sq_mul_eq_zero_of_prime_mod_four_eq_three` &
     `r2Count_sq_mul_eq_zero_of_mod_four_eq_three` (`s ≡ 3 (mod 4) → ∀ k ≥ 1, r₂(k² s) = 0`),
   - `r3Count_sq_mul_eq_zero_of_mod_eight_eq_seven` &
     `r3Count_sq_mul_eq_zero_of_prime_mod_eight_eq_seven` (`p ≡ 7 (mod 8) → ∀ k ≥ 1, r₃(k² p) = 0`),
   - **Constructive Elementary 3-Square Separation** (`exists_new_sqf_mod_eight_eq_three_r3_pos`):
     via `N = Q² + 2 = 1² + 1² + Q² ≡ 3 (mod 8)` for the product `Q` of odd primes dividing a
     given finite set, producing infinitely many distinct square-free cores `s ≡ 3 (mod 8)` with
     `∃ k ≥ 1, r₃(k² s) ≥ 1` and `∀ k ≥ 1, r₂(k² s) = 0` without needing Legendre's 3-square theorem,
   - `r4Count_pos` (`∀ N, 1 ≤ r₄(N)` via Lagrange's four-square theorem `Nat.sum_four_squares`).
2. **Physical Relativistic Massless Blackbody Photon Gas Internal Energy & Grand Potential:**
   - Square-root action spectrum `sqrtSpectrum = {√M : M ≥ 1}`, locally finite and well-founded,
   - Exact internal energy `U_photon^{(D)}(t) = ∑_{N ≥ 1} r_D(N) √N / (e^{√N t} - 1)
     = ∑_{M ≥ 1} (∑_{k² ∣ M} r_D(M / k²) √(M / k²)) e^{-√M t}` (`photonEnergyAnalytic`,
     `photonEnergyCoeff`, `photonEnergyHahn`, `photonEnergyTrans`), with exact analytic regrouping
     identity `photonEnergyAnalytic_eq_tsum_sqrt` on `t > 0`,
   - Exact grand potential `log Z_photon^{(D)}(t)` (`photonLogZTrans`) with
     `transDerivX (photonLogZTrans r) = -(photonEnergyTrans r)`.
3. **Triangular Core-Separation Engine & Crown-Jewel Photon Gas Theorems:**
   - Besicovitch square-free core projection functionals `exists_core_functional` directly from
     `besicovitch_rfree_linearIndependent 2`,
   - Unified triangular core-separation theorem `triangular_core_transseries_diff_indep`,
   - **`photon2D_non_ade`**, **`photon3D_non_ade`**, **`photon4D_non_ade`** (algebraic independence
     of all derivatives over `AsympCoeff`, hence no polynomial ADE over `ℂ[t]`),
   - **`photon2D_photon3D_photon4D_joint_diff_indep`** (joint differential independence of
     `(U_photon^{(2)}, U_photon^{(3)}, U_photon^{(4)})` of every order `J` — and across all
     derivatives `Fin 3 × ℕ` — over `AsympCoeff` and over `ℂ[t]`),
   - **`photonLogZ_2D_3D_4D_joint_diff_indep`** (joint differential independence of the grand
     potentials `(log Z_photon^{(2)}, log Z_photon^{(3)}, log Z_photon^{(4)})`). -/

public section
namespace CubicTheta.AllD
open Set Filter MvPolynomial Matrix
open scoped BigOperators Pointwise Classical
noncomputable section

/-! ### 1. Exact Lattice Counts `r₂(N), r₃(N), r₄(N)` & Elementary 3-Class Separation -/

/-- Number of integer lattice vectors in `ℤ²` of squared Euclidean norm `N`:
`r₂(N) = #{(a, b) ∈ ℤ² : a² + b² = N}`. -/
def r2Count (N : ℕ) : ℕ :=
  ((Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
    (fun v : ℤ × ℤ ↦ v.1 ^ 2 + v.2 ^ 2 = (N : ℤ))).card

/-- Number of integer lattice vectors in `ℤ⁴` of squared Euclidean norm `N`:
`r₄(N) = #{(a, b, c, d) ∈ ℤ⁴ : a² + b² + c² + d² = N}`. -/
def r4Count (N : ℕ) : ℕ :=
  ((Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ
    (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)))).filter
    (fun v : ℤ × ℤ × ℤ × ℤ ↦
      v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = (N : ℤ))).card

theorem r2Count_le (N : ℕ) : r2Count N ≤ (2 * N + 1) ^ 2 := by
  unfold r2Count
  calc _ ≤ (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)).card :=
        Finset.card_filter_le _ _
    _ = (Finset.Icc (-(N : ℤ)) (N : ℤ)).card * (Finset.Icc (-(N : ℤ)) (N : ℤ)).card :=
        Finset.card_product _ _
    _ = (2 * N + 1) ^ 2 := by
        have hc : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
          rw [Int.card_Icc]; omega
        rw [hc, sq]

theorem r4Count_le (N : ℕ) : r4Count N ≤ (2 * N + 1) ^ 4 := by
  unfold r4Count
  calc _ ≤ (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ
            (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)))).card :=
        Finset.card_filter_le _ _
    _ = (2 * N + 1) ^ 4 := by
        have hc : (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
          rw [Int.card_Icc]; omega
        simp only [Finset.card_product, hc]
        ring

/-- Via Fermat's two-square theorem (`Nat.Prime.sq_add_sq`), every prime `p ≡ 1 (mod 4)` satisfies
`r₂(p) ≥ 1`. -/
theorem r2Count_pos_of_prime_mod_four_eq_one {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    1 ≤ r2Count p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  have ha_le : (a : ℤ) ≤ (p : ℤ) := by
    have h1 : a ≤ a ^ 2 := Nat.le_self_pow (by decide) a
    have h2 : a ^ 2 ≤ p := by omega
    exact_mod_cast h1.trans h2
  have hb_le : (b : ℤ) ≤ (p : ℤ) := by
    have h1 : b ≤ b ^ 2 := Nat.le_self_pow (by decide) b
    have h2 : b ^ 2 ≤ p := by omega
    exact_mod_cast h1.trans h2
  have hmem : ((a : ℤ), (b : ℤ)) ∈
      (Finset.Icc (-(p : ℤ)) (p : ℤ) ×ˢ Finset.Icc (-(p : ℤ)) (p : ℤ)).filter
        (fun v : ℤ × ℤ ↦ v.1 ^ 2 + v.2 ^ 2 = (p : ℤ)) := by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨by omega, ha_le⟩, ⟨by omega, hb_le⟩⟩, ?_⟩
    exact_mod_cast hab
  exact Finset.card_pos.mpr ⟨_, hmem⟩

/-- If `q` is a prime with `q ≡ 3 (mod 4)` and `q ∣ a² + b²`, then `q ∣ a` and `q ∣ b`. -/
private lemma prime_mod_four_eq_three_dvd_sq_add_sq {q a b : ℕ}
    (hq : q.Prime) (hq3 : q % 4 = 3) (hdvd : q ∣ a ^ 2 + b ^ 2) :
    q ∣ a ∧ q ∣ b := by
  have : Fact q.Prime := ⟨hq⟩
  have hmod : ((a : ZMod q) ^ 2 + (b : ZMod q) ^ 2) = 0 := by
    have h0 : ((a ^ 2 + b ^ 2 : ℕ) : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    simpa [Nat.cast_add, Nat.cast_pow] using h0
  have hb0 : (b : ZMod q) = 0 := by
    by_contra hbne
    have hsq : ((a : ZMod q) * (b : ZMod q)⁻¹) ^ 2 = -1 := by
      have ha2 : (a : ZMod q) ^ 2 = -((b : ZMod q) ^ 2) := eq_neg_of_add_eq_zero_left hmod
      rw [mul_pow, ha2, neg_mul, ← mul_pow, mul_inv_cancel₀ hbne, one_pow]
    have hisq : IsSquare (-1 : ZMod q) := ⟨(a : ZMod q) * (b : ZMod q)⁻¹, by rw [← sq, hsq]⟩
    have hne3 : q % 4 ≠ 3 := (ZMod.exists_sq_eq_neg_one_iff (p := q)).mp hisq
    exact hne3 hq3
  have hqb : q ∣ b := (ZMod.natCast_eq_zero_iff b q).mp hb0
  have ha0 : (a : ZMod q) ^ 2 = 0 := by simpa [hb0] using hmod
  have hqa : q ∣ a := (ZMod.natCast_eq_zero_iff a q).mp (eq_zero_of_pow_eq_zero ha0)
  exact ⟨hqa, hqb⟩

private lemma not_sq_add_sq_of_odd_val_prime_mod_four_eq_three {q : ℕ}
    (hq : q.Prime) (hq3 : q % 4 = 3) :
    ∀ N : ℕ, Odd (N.factorization q) → ∀ a b : ℕ, a ^ 2 + b ^ 2 ≠ N := by
  intro N
  induction N using Nat.strong_induction_on with
  | ind N ih =>
    intro hodd a b hab
    have hN0 : N ≠ 0 := by
      rintro rfl
      simp at hodd
    have hv_pos : 0 < N.factorization q := by
      rcases hodd with ⟨m, hm⟩
      omega
    have hqN : q ∣ N := (hq.dvd_iff_one_le_factorization hN0).mpr hv_pos
    have hqab : q ∣ a ^ 2 + b ^ 2 := hab ▸ hqN
    obtain ⟨⟨a', rfl⟩, ⟨b', rfl⟩⟩ := prime_mod_four_eq_three_dvd_sq_add_sq hq hq3 hqab
    have hq2N : q ^ 2 * (a' ^ 2 + b' ^ 2) = N := by
      calc q ^ 2 * (a' ^ 2 + b' ^ 2) = (q * a') ^ 2 + (q * b') ^ 2 := by ring
        _ = N := hab
    set M := a' ^ 2 + b' ^ 2
    have hM0 : M ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hq2N
      exact hN0 hq2N.symm
    have hq2_gt1 : 1 < q ^ 2 := by
      have := hq.two_le; nlinarith
    have hM_lt : M < N := by
      have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
      nlinarith
    have hvalM : N.factorization q = 2 + M.factorization q := by
      rw [← hq2N, Nat.factorization_mul (pow_ne_zero 2 hq.ne_zero) hM0,
          Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
          hq.factorization_self, mul_one]
    have hoddM : Odd (M.factorization q) := by
      rcases hodd with ⟨m, hm⟩
      refine ⟨m - 1, ?_⟩
      omega
    exact ih M hM_lt hoddM a' b' rfl

/-- Elementary `p`-adic obstruction to two squares: if `q` is prime with `q ≡ 3 (mod 4)` and
`v_q(N)` is odd, then `r₂(N) = 0`. -/
theorem r2Count_eq_zero_of_odd_val_prime_mod_four_eq_three {N q : ℕ}
    (hq : q.Prime) (hq3 : q % 4 = 3) (hodd : Odd (N.factorization q)) :
    r2Count N = 0 := by
  unfold r2Count
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _ heq
  have hnat : v.1.natAbs ^ 2 + v.2.natAbs ^ 2 = N := by
    have h1 : ((v.1.natAbs ^ 2 + v.2.natAbs ^ 2 : ℕ) : ℤ) = (N : ℤ) := by
      push_cast
      rw [sq_abs, sq_abs]
      exact heq
    exact_mod_cast h1
  exact not_sq_add_sq_of_odd_val_prime_mod_four_eq_three hq hq3 N hodd v.1.natAbs v.2.natAbs hnat

/-- For every prime `p ≡ 3 (mod 4)` and every `k ≥ 1`, `r₂(k² p) = 0`. -/
theorem r2Count_sq_mul_eq_zero_of_prime_mod_four_eq_three {p : ℕ} (hp : p.Prime)
    (hp3 : p % 4 = 3) {k : ℕ} (hk : 1 ≤ k) :
    r2Count (k ^ 2 * p) = 0 := by
  refine r2Count_eq_zero_of_odd_val_prime_mod_four_eq_three hp hp3 ?_
  rw [Nat.factorization_mul (pow_ne_zero 2 (by omega)) hp.ne_zero, Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_self]
  exact ⟨k.factorization p, rfl⟩

/-- Every `s ≡ 3 (mod 4)` has a prime factor `q ≡ 3 (mod 4)` with odd `q`-adic valuation. -/
private lemma exists_prime_mod_four_eq_three_odd_val {s : ℕ} (hs : s % 4 = 3) :
    ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ Odd (s.factorization q) := by
  have hs0 : s ≠ 0 := by omega
  by_contra hnot
  push Not at hnot
  have hprod_eq : ∏ q ∈ s.primeFactors, q ^ s.factorization q = s := by
    rw [← Nat.support_factorization]
    exact Nat.prod_factorization_pow_eq_self hs0
  have hfactor_mod : ∀ q ∈ s.primeFactors, (q ^ s.factorization q) % 4 = 1 := by
    intro q hqmem
    have hq : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hq_dvd : q ∣ s := Nat.dvd_of_mem_primeFactors hqmem
    have hq_odd : q % 2 = 1 := by
      by_contra heven
      have h2q : q = 2 := (Nat.Prime.even_iff hq).mp (Nat.even_iff.mpr (by omega))
      subst h2q
      obtain ⟨t, ht⟩ := hq_dvd
      omega
    by_cases hq1 : q % 4 = 1
    · induction (s.factorization q) with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, Nat.mul_mod, ih, hq1]
    · have hq3 : q % 4 = 3 := by omega
      have heven : Even (s.factorization q) := hnot q hq hq3
      obtain ⟨m, hm⟩ := heven
      rw [hm, ← two_mul, pow_mul]
      have hsq : (q ^ 2) % 4 = 1 := by
        rw [sq, Nat.mul_mod, hq3]
      clear hm
      induction m with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, Nat.mul_mod, ih, hsq]
  have hprod_mod : ∀ T : Finset ℕ, (∀ q ∈ T, (q ^ s.factorization q) % 4 = 1) →
      (∏ q ∈ T, q ^ s.factorization q) % 4 = 1 := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert a T ha ih =>
      intro hT
      rw [Finset.prod_insert ha, Nat.mul_mod,
          hT a (Finset.mem_insert_self a T),
          ih (fun q hq ↦ hT q (Finset.mem_insert_of_mem hq))]
  have hmod1 : (∏ q ∈ s.primeFactors, q ^ s.factorization q) % 4 = 1 :=
    hprod_mod s.primeFactors hfactor_mod
  rw [hprod_eq] at hmod1
  omega

/-- For EVERY `s ≡ 3 (mod 4)` (not necessarily prime!) and EVERY `k ≥ 1`, `r₂(k² s) = 0`. -/
theorem r2Count_sq_mul_eq_zero_of_mod_four_eq_three {s : ℕ} (hs : s % 4 = 3)
    {k : ℕ} (hk : 1 ≤ k) :
    r2Count (k ^ 2 * s) = 0 := by
  obtain ⟨q, hq, hq3, ⟨m, hm⟩⟩ := exists_prime_mod_four_eq_three_odd_val hs
  refine r2Count_eq_zero_of_odd_val_prime_mod_four_eq_three hq hq3 ?_
  rw [Nat.factorization_mul (pow_ne_zero 2 (by omega)) (by omega), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hm]
  exact ⟨k.factorization q + m, by ring⟩

/-- Elementary mod-4 descent for 3 squares: if `r₃(n) = 0`, then `r₃(4 n) = 0`. -/
private lemma r3Count_four_mul_eq_zero {n : ℕ} (hn : r3Count n = 0) : r3Count (4 * n) = 0 := by
  unfold r3Count at hn ⊢
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hn ⊢
  intro v _ heq
  have hsq_mod : ∀ x : ℤ, x ^ 2 % 4 = 0 ∨ x ^ 2 % 4 = 1 := fun x ↦ by
    have h0 : (x % 4) = 0 ∨ (x % 4) = 1 ∨ (x % 4) = 2 ∨ (x % 4) = 3 := by omega
    rcases h0 with h | h | h | h <;> rw [sq, Int.mul_emod, h] <;> norm_num
  have hsum0 : (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2) % 4 = 0 := by
    rw [heq]; push_cast; omega
  have h1 := hsq_mod v.1
  have h2 := hsq_mod v.2.1
  have h3 := hsq_mod v.2.2
  have hev1 : v.1 ^ 2 % 4 = 0 := by omega
  have hev2 : v.2.1 ^ 2 % 4 = 0 := by omega
  have hev3 : v.2.2 ^ 2 % 4 = 0 := by omega
  have hdvd2 : ∀ x : ℤ, x ^ 2 % 4 = 0 → x % 2 = 0 := fun x hx ↦ by
    have h0 : x % 4 = 0 ∨ x % 4 = 1 ∨ x % 4 = 2 ∨ x % 4 = 3 := by omega
    rcases h0 with h | h | h | h
    · omega
    · rw [sq, Int.mul_emod, h] at hx; norm_num at hx
    · omega
    · rw [sq, Int.mul_emod, h] at hx; norm_num at hx
  have hd1 := hdvd2 v.1 hev1
  have hd2 := hdvd2 v.2.1 hev2
  have hd3 := hdvd2 v.2.2 hev3
  let a : ℤ := v.1 / 2
  let b : ℤ := v.2.1 / 2
  let c : ℤ := v.2.2 / 2
  have ha : v.1 = 2 * a := by dsimp [a]; omega
  have hb : v.2.1 = 2 * b := by dsimp [b]; omega
  have hc : v.2.2 = 2 * c := by dsimp [c]; omega
  have hsum : a ^ 2 + b ^ 2 + c ^ 2 = (n : ℤ) := by
    have h4 : 4 * (a ^ 2 + b ^ 2 + c ^ 2) = 4 * (n : ℤ) := by
      calc 4 * (a ^ 2 + b ^ 2 + c ^ 2) = (2 * a) ^ 2 + (2 * b) ^ 2 + (2 * c) ^ 2 := by ring
        _ = v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 := by rw [← ha, ← hb, ← hc]
        _ = ((4 * n : ℕ) : ℤ) := heq
        _ = 4 * (n : ℤ) := by push_cast; ring
    linarith
  have hbd : ∀ x : ℤ, x ^ 2 ≤ (n : ℤ) → -(n : ℤ) ≤ x ∧ x ≤ (n : ℤ) := fun x hx ↦ by
    have h1 : |x| ≤ x ^ 2 := by
      have habs : |x| * 1 ≤ |x| * |x| ∨ |x| = 0 := by
        by_cases h0 : |x| = 0
        · exact Or.inr h0
        · have hge1 : 1 ≤ |x| := by
            have := abs_nonneg x; omega
          exact Or.inl (mul_le_mul_of_nonneg_left hge1 (abs_nonneg x))
      rcases habs with h | h
      · rw [mul_one, ← sq, sq_abs] at h; exact h
      · rw [h]; exact sq_nonneg x
    exact abs_le.mp (h1.trans hx)
  have hmem : (a, (b, c)) ∈
      Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ
        Finset.Icc (-(n : ℤ)) (n : ℤ)) := by
    simp only [Finset.mem_product, Finset.mem_Icc]
    exact ⟨hbd a (by nlinarith [sq_nonneg b, sq_nonneg c]),
      hbd b (by nlinarith [sq_nonneg a, sq_nonneg c]),
      hbd c (by nlinarith [sq_nonneg a, sq_nonneg b])⟩
  exact hn hmem hsum

/-- For EVERY `m ≡ 7 (mod 8)` and EVERY `k ≥ 1`, `r₃(k² m) = 0`. -/
theorem r3Count_sq_mul_eq_zero_of_mod_eight_eq_seven {m : ℕ} (hm : m % 8 = 7) :
    ∀ k : ℕ, 1 ≤ k → r3Count (k ^ 2 * m) = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk
    by_cases hpar : k % 2 = 0
    · set k' := k / 2
      have hk_eq : k = 2 * k' := by omega
      have hk'_pos : 1 ≤ k' := by omega
      have hk'_lt : k' < k := by omega
      have heq : k ^ 2 * m = 4 * (k' ^ 2 * m) := by rw [hk_eq]; ring
      rw [heq]
      exact r3Count_four_mul_eq_zero (ih k' hk'_lt hk'_pos)
    · have hk2 : k ^ 2 % 8 = 1 := by
        have h0 : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by omega
        rcases h0 with h | h | h | h <;> rw [sq, Nat.mul_mod, h]
      have hmod7 : (k ^ 2 * m) % 8 = 7 := by
        rw [Nat.mul_mod, hk2, hm]
      exact r3Count_eq_zero_of_mod_eight_eq_seven hmod7

/-- For every prime `p ≡ 7 (mod 8)` and every `k ≥ 1`, `r₃(k² p) = 0`. -/
theorem r3Count_sq_mul_eq_zero_of_prime_mod_eight_eq_seven {p : ℕ} (_hp : p.Prime)
    (hp7 : p % 8 = 7) {k : ℕ} (hk : 1 ≤ k) :
    r3Count (k ^ 2 * p) = 0 :=
  r3Count_sq_mul_eq_zero_of_mod_eight_eq_seven hp7 k hk

/-- Via Lagrange's four-square theorem (`Nat.sum_four_squares`), every natural number `N`
satisfies `r₄(N) ≥ 1`. -/
theorem r4Count_pos (N : ℕ) : 1 ≤ r4Count N := by
  obtain ⟨a, b, c, d, habcd⟩ := Nat.sum_four_squares N
  have hle : ∀ x : ℕ, x ^ 2 ≤ N → (x : ℤ) ≤ (N : ℤ) := fun x hx ↦ by
    have h1 : x ≤ x ^ 2 := Nat.le_self_pow (by decide) x
    exact_mod_cast h1.trans hx
  have hmem : ((a : ℤ), ((b : ℤ), ((c : ℤ), (d : ℤ)))) ∈
      (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ
        (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Finset.Icc (-(N : ℤ)) (N : ℤ)))).filter
        (fun v : ℤ × ℤ × ℤ × ℤ ↦
          v.1 ^ 2 + v.2.1 ^ 2 + v.2.2.1 ^ 2 + v.2.2.2 ^ 2 = (N : ℤ)) := by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨by omega, hle a (by omega)⟩, ⟨by omega, hle b (by omega)⟩,
      ⟨by omega, hle c (by omega)⟩, ⟨by omega, hle d (by omega)⟩⟩, ?_⟩
    exact_mod_cast habcd
  exact Finset.card_pos.mpr ⟨_, hmem⟩

/-- **Constructive Elementary 3-Square Separation (Zero Legendre 3-Square Theorem Needed!)**:
For EVERY finite set `S` of square-free cores, taking `N = Q² + 2 = 1² + 1² + Q²` where `Q`
is the product of all odd primes dividing elements of `S` produces a NEW square-free core
`s ∉ S` with `s ≡ 3 (mod 8)` and `∃ k ≥ 1, r₃(k² s) ≥ 1` (while `∀ k ≥ 1, r₂(k² s) = 0`!). -/
theorem exists_new_sqf_mod_eight_eq_three_r3_pos (S : Finset (Core 2)) :
    ∃ s : Core 2, s ∉ S ∧ s.val % 8 = 3 ∧ ∃ k : ℕ, 1 ≤ k ∧ 1 ≤ r3Count (k ^ 2 * s.val) := by
  classical
  let Pset : Finset ℕ := (S.biUnion fun x ↦ x.val.primeFactors).filter (· ≠ 2)
  let Q : ℕ := ∏ p ∈ Pset, p
  have hQ_odd : Q % 2 = 1 := by
    have hall : ∀ p ∈ Pset, p % 2 = 1 := by
      intro p hp
      obtain ⟨hbi, hne2⟩ := Finset.mem_filter.mp hp
      obtain ⟨x, _, hpx⟩ := Finset.mem_biUnion.mp hbi
      have hpr : p.Prime := Nat.prime_of_mem_primeFactors hpx
      by_contra hnot
      have hev : Even p := Nat.even_iff.mpr (by omega)
      exact hne2 ((Nat.Prime.even_iff hpr).mp hev)
    have hprod_odd : ∀ T : Finset ℕ, (∀ p ∈ T, p % 2 = 1) → (∏ p ∈ T, p) % 2 = 1 := by
      intro T
      induction T using Finset.induction_on with
      | empty => intro _; simp
      | insert a T ha ih =>
        intro hT
        rw [Finset.prod_insert ha, Nat.mul_mod,
            hT a (Finset.mem_insert_self a T),
            ih (fun p hp ↦ hT p (Finset.mem_insert_of_mem hp))]
    exact hprod_odd Pset hall
  let N : ℕ := Q ^ 2 + 2
  have hN_pos : 0 < N := by dsimp [N]; omega
  have hN_mod8 : N % 8 = 3 := by
    have hQ2 : Q ^ 2 % 8 = 1 := by
      have h0 : Q % 8 = 1 ∨ Q % 8 = 3 ∨ Q % 8 = 5 ∨ Q % 8 = 7 := by omega
      rcases h0 with h | h | h | h <;> rw [sq, Nat.mul_mod, h]
    dsimp [N]
    rw [Nat.add_mod, hQ2]
  have hr3_N : 1 ≤ r3Count N := by
    have hQ_le : (Q : ℤ) ≤ (N : ℤ) := by
      have h1 : Q ≤ Q ^ 2 := Nat.le_self_pow (by decide) Q
      have h2 : Q ≤ N := by dsimp [N]; omega
      exact_mod_cast h2
    have hmem : ((1 : ℤ), ((1 : ℤ), (Q : ℤ))) ∈
        (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ (Finset.Icc (-(N : ℤ)) (N : ℤ) ×ˢ
          Finset.Icc (-(N : ℤ)) (N : ℤ))).filter
          (fun v : ℤ × ℤ × ℤ ↦ v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2 = (N : ℤ)) := by
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
      refine ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, hQ_le⟩⟩, ?_⟩
      dsimp [N]; ring
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  let s : Core 2 := rFreeCore 2 (by decide) ⟨N, hN_pos⟩
  let k : ℕ := rFreeRoot 2 (by decide) ⟨N, hN_pos⟩
  have hk_pos : 1 ≤ k := rFreeRoot_pos 2 (by decide) ⟨N, hN_pos⟩
  have hks : k ^ 2 * s.val = N := rFreeRoot_pow_mul_core 2 (by decide) ⟨N, hN_pos⟩
  have hk_odd : k % 2 = 1 := by
    by_contra hev
    have h2k : 2 ∣ k := Nat.dvd_of_mod_eq_zero (by omega)
    obtain ⟨t, ht⟩ := h2k
    have hNe : N = 2 * (2 * t ^ 2 * s.val) := by rw [← hks, ht]; ring
    omega
  have hk2_mod8 : k ^ 2 % 8 = 1 := by
    have h0 : k % 8 = 1 ∨ k % 8 = 3 ∨ k % 8 = 5 ∨ k % 8 = 7 := by omega
    rcases h0 with h | h | h | h <;> rw [sq, Nat.mul_mod, h]
  have hs_mod8 : s.val % 8 = 3 := by
    have hmul : (k ^ 2 * s.val) % 8 = 3 := hks ▸ hN_mod8
    rw [Nat.mul_mod, hk2_mod8, one_mul, Nat.mod_mod] at hmul
    exact hmul
  have hs_notMem : s ∉ S := by
    intro hsS
    have hs_ne1 : s.val ≠ 1 := by omega
    obtain ⟨q, hq_prime, hq_dvd_s⟩ := Nat.exists_prime_and_dvd hs_ne1
    have hq_dvd_N : q ∣ N := hq_dvd_s.trans ⟨k ^ 2, by rw [mul_comm, hks]⟩
    have hq_ne2 : q ≠ 2 := by
      rintro rfl
      obtain ⟨t, ht⟩ := hq_dvd_N
      omega
    have hq_mem_Pset : q ∈ Pset := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨s, hsS, ?_⟩, hq_ne2⟩
      exact Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_s, rfree_ne_zero s.property⟩
    have hq_dvd_Q : q ∣ Q := Finset.dvd_prod_of_mem _ hq_mem_Pset
    have hq_dvd_Q2 : q ∣ Q ^ 2 := dvd_pow hq_dvd_Q (by decide)
    have hq_dvd_2 : q ∣ 2 := by
      have hsub := (Nat.dvd_add_right hq_dvd_Q2).mp hq_dvd_N
      exact hsub
    have hq_le2 : q ≤ 2 := Nat.le_of_dvd (by decide) hq_dvd_2
    have := hq_prime.two_le
    omega
  exact ⟨s, hs_notMem, hs_mod8, k, hk_pos, hks ▸ hr3_N⟩

/-- Infinite set of square-free cores `s ≡ 3 (mod 8)` witnessing `r₃(k² s) ≥ 1` while `r₂(k² s) = 0`. -/
theorem infinite_sqf_mod_eight_eq_three_r3_pos :
    {s : Core 2 | s.val % 8 = 3 ∧ ∃ k : ℕ, 1 ≤ k ∧ 1 ≤ r3Count (k ^ 2 * s.val)}.Infinite := by
  intro hfin
  obtain ⟨s, hs_not, hs_mod, hk⟩ := exists_new_sqf_mod_eight_eq_three_r3_pos hfin.toFinset
  exact hs_not (hfin.mem_toFinset.mpr ⟨hs_mod, hk⟩)

/-- Infinite set of prime square-free cores `p ≡ 1 (mod 4)` (where `r₂(p) ≥ 1`). -/
theorem infinite_prime_core_mod_four_eq_one :
    {s : Core 2 | s.val.Prime ∧ s.val % 4 = 1}.Infinite := by
  intro hfin
  let B : ℕ := hfin.toFinset.sup Subtype.val
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq B (by decide : 4 ≠ 0) (by decide : Nat.Coprime 1 4)
  let s : Core 2 := ⟨p, rfree_of_prime (by decide) hp_prime⟩
  have hs_mem : s ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hp_prime, hp_mod⟩
  have hle : p ≤ B := Finset.le_sup (f := Subtype.val) hs_mem
  omega

/-- Infinite set of prime square-free cores `p ≡ 7 (mod 8)` (where `r₂(k² p) = r₃(k² p) = 0` and `r₄(p) ≥ 1`). -/
theorem infinite_prime_core_mod_eight_eq_seven :
    {s : Core 2 | s.val.Prime ∧ s.val % 8 = 7}.Infinite := by
  intro hfin
  let B : ℕ := hfin.toFinset.sup Subtype.val
  obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq B (by decide : 8 ≠ 0) (by decide : Nat.Coprime 7 8)
  let s : Core 2 := ⟨p, rfree_of_prime (by decide) hp_prime⟩
  have hs_mem : s ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hp_prime, hp_mod⟩
  have hle : p ≤ B := Finset.le_sup (f := Subtype.val) hs_mem
  omega

/-! ### 2. Square-Root Spectrum, Besicovitch Core Projections, & Relativistic Photon Series -/

/-- The discrete positive square-root action spectrum `{√M : M ≥ 1}` of massless relativistic
photons on `ℤ^D \ {0}`. -/
def sqrtSpectrum : Set ℝ :=
  {x : ℝ | ∃ M : ℕ, 1 ≤ M ∧ x = Real.sqrt (M : ℝ)}

theorem sqrtSpectrum_pos : ∀ a ∈ sqrtSpectrum, 0 < a := by
  rintro _ ⟨M, hM, rfl⟩
  exact Real.sqrt_pos.mpr (by exact_mod_cast hM)

theorem sqrtSpectrum_locallyFinite : ∀ B : ℝ, (sqrtSpectrum ∩ Set.Iic B).Finite := by
  intro B
  let N : ℕ := Nat.ceil ((max 0 B) ^ 2)
  have hsub : sqrtSpectrum ∩ Set.Iic B ⊆
      (fun M : ℕ ↦ Real.sqrt (M : ℝ)) '' (Finset.Iic N : Set ℕ) := by
    rintro x ⟨⟨M, _, rfl⟩, hxB⟩
    refine ⟨M, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_Iic]
    have h1 : Real.sqrt (M : ℝ) ≤ max 0 B := (Set.mem_Iic.mp hxB).trans (le_max_right 0 B)
    have h2 : (M : ℝ) ≤ (max 0 B) ^ 2 := by
      have hsq := sq_le_sq' (by linarith [Real.sqrt_nonneg (M : ℝ), le_max_left 0 B]) h1
      rwa [Real.sq_sqrt (Nat.cast_nonneg M)] at hsq
    exact_mod_cast h2.trans (Nat.le_ceil _)
  exact ((Finset.finite_toSet (Finset.Iic N)).image _).subset hsub

theorem sqrtSpectrum_isWF : sqrtSpectrum.IsWF :=
  isWF_of_locallyFinite sqrtSpectrum_locallyFinite

theorem sqrtSpectrum_isPWO : sqrtSpectrum.IsPWO :=
  sqrtSpectrum_isWF.isPWO

/-- **Besicovitch Square-Free Core Projection Functional**: for every square-free core `s : Core 2`,
there exists a `ℚ`-linear functional `φ : ℝ →ₗ[ℚ] ℚ` isolating `√s` (`φ (√s) = 1`) and
annihilating EVERY other square-free root `√t` (`t ≠ s`). In particular, for EVERY `M ≥ 1`
with square-free factorization `M = k² t`, `φ (√M) = k` if `t = s` and `0` otherwise! -/
theorem exists_core_functional (s : Core 2) :
    ∃ φ : ℝ →ₗ[ℚ] ℚ,
      φ (Real.sqrt (s.val : ℝ)) = 1 ∧
      (∀ t : Core 2, t ≠ s → φ (Real.sqrt (t.val : ℝ)) = 0) ∧
      (∀ (M : ℕ+), φ (Real.sqrt (M.val : ℝ)) =
        if rFreeCore 2 (by decide) M = s then (rFreeRoot 2 (by decide) M : ℚ) else 0) := by
  have hlin : LinearIndependent ℚ (fun t : Core 2 ↦ Real.sqrt (t.val : ℝ)) := by
    have h0 := besicovitch_rfree_linearIndependent 2 (by decide)
    convert h0 using 1
    funext t
    rw [Real.sqrt_eq_rpow]
    norm_num
  let U : Submodule ℚ ℝ :=
    Submodule.span ℚ ((fun t : Core 2 ↦ Real.sqrt (t.val : ℝ)) '' {t : Core 2 | t ≠ s})
  have hnotmem : Real.sqrt (s.val : ℝ) ∉ U := by
    have h := hlin.notMem_span_image (s := {t : Core 2 | t ≠ s}) (by simp : s ∉ {t : Core 2 | t ≠ s})
    exact h
  obtain ⟨φ, hφU, hφs⟩ := LinearMap.exists_extend_of_notMem (0 : U →ₗ[ℚ] ℚ) hnotmem (1 : ℚ)
  have hφ_other : ∀ t : Core 2, t ≠ s → φ (Real.sqrt (t.val : ℝ)) = 0 := by
    intro t ht
    have hmem : Real.sqrt (t.val : ℝ) ∈ U := Submodule.subset_span ⟨t, ht, rfl⟩
    have h0 := LinearMap.congr_fun hφU ⟨Real.sqrt (t.val : ℝ), hmem⟩
    simpa using h0
  refine ⟨φ, hφs, hφ_other, fun M ↦ ?_⟩
  let t : Core 2 := rFreeCore 2 (by decide) M
  let k : ℕ := rFreeRoot 2 (by decide) M
  have hkt : k ^ 2 * t.val = M.val := rFreeRoot_pow_mul_core 2 (by decide) M
  have hsqrt : Real.sqrt (M.val : ℝ) = (k : ℚ) • Real.sqrt (t.val : ℝ) := by
    rw [← hkt, Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (Nat.cast_nonneg k), Rat.smul_def, Rat.cast_natCast]
  rw [hsqrt, map_smul, smul_eq_mul]
  by_cases hts : t = s
  · simp [t, k, hts, hφs]
  · simp [t, k, hts, hφ_other t hts]

/-- Exact coefficient of `e^{-√M t}` in the relativistic photon gas internal energy
`U_photon(t) = ∑_{N ≥ 1} ∑_{k ≥ 1} r(N) √N e^{-k √N t}`:
`c(M) = ∑_{k² ∣ M} r(M / k²) √(M / k²)`. -/
def photonEnergyCoeff (r : ℕ → ℕ) (M : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 M).filter (fun k ↦ k ^ 2 ∣ M),
    (r (M / k ^ 2) : ℝ) * Real.sqrt ((M / k ^ 2 : ℕ) : ℝ)

/-- Exact coefficient of `e^{-√M t}` in the relativistic photon gas grand potential
`log Z_photon(t) = ∑_{N ≥ 1} ∑_{k ≥ 1} (r(N) / k) e^{-k √N t}`:
`b(M) = ∑_{k² ∣ M} r(M / k²) / k`. -/
def photonLogZCoeff (r : ℕ → ℕ) (M : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Icc 1 M).filter (fun k ↦ k ^ 2 ∣ M),
    (r (M / k ^ 2) : ℝ) / (k : ℝ)

theorem photonEnergyCoeff_nonneg (r : ℕ → ℕ) (M : ℕ) : 0 ≤ photonEnergyCoeff r M :=
  Finset.sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)

theorem photonLogZCoeff_nonneg (r : ℕ → ℕ) (M : ℕ) : 0 ≤ photonLogZCoeff r M :=
  Finset.sum_nonneg fun _ _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem photonEnergyCoeff_eq_sqrt_mul_logZCoeff (r : ℕ → ℕ) (M : ℕ) :
    photonEnergyCoeff r M = Real.sqrt (M : ℝ) * photonLogZCoeff r M := by
  unfold photonEnergyCoeff photonLogZCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨hkIcc, hdvd⟩ := Finset.mem_filter.mp hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hmul : k ^ 2 * (M / k ^ 2) = M := Nat.mul_div_cancel' hdvd
  have hsqrtM : Real.sqrt (M : ℝ) = (k : ℝ) * Real.sqrt ((M / k ^ 2 : ℕ) : ℝ) := by
    conv_lhs => rw [← hmul]
    rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk_pos.le]
  rw [hsqrtM]
  field_simp [hk_pos.ne']

theorem photonEnergyCoeff_pos_of_pos (r : ℕ → ℕ) {M : ℕ} (hM : 1 ≤ M) (hr : 1 ≤ r M) :
    0 < photonEnergyCoeff r M := by
  have hmem : 1 ∈ (Finset.Icc 1 M).filter (fun k ↦ k ^ 2 ∣ M) := by
    simp only [Finset.mem_filter, Finset.mem_Icc, one_pow, one_dvd, and_true]
    exact ⟨le_rfl, hM⟩
  have hle := Finset.single_le_sum
    (f := fun k ↦ (r (M / k ^ 2) : ℝ) * Real.sqrt ((M / k ^ 2 : ℕ) : ℝ))
    (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)) hmem
  simp only [one_pow, Nat.div_one] at hle
  have h1 : 0 < (r M : ℝ) * Real.sqrt (M : ℝ) :=
    mul_pos (by exact_mod_cast hr) (Real.sqrt_pos.mpr (by exact_mod_cast hM))
  exact lt_of_lt_of_le h1 hle

theorem photonLogZCoeff_pos_of_pos (r : ℕ → ℕ) {M : ℕ} (hM : 1 ≤ M) (hr : 1 ≤ r M) :
    0 < photonLogZCoeff r M := by
  have hE := photonEnergyCoeff_pos_of_pos r hM hr
  rw [photonEnergyCoeff_eq_sqrt_mul_logZCoeff] at hE
  have hsq : 0 < Real.sqrt (M : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hM)
  nlinarith

/-- If `s` is square-free and `k² ∣ m² s`, then `k ∣ m`. -/
private lemma dvd_of_sq_dvd_sq_mul_rfree {s : Core 2} {k m : ℕ} (hm : 1 ≤ m)
    (hdvd : k ^ 2 ∣ m ^ 2 * s.val) : k ∣ m := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_dvd_iff,
      mul_eq_zero] at hdvd
    rcases hdvd with h | h
    · have : m = 0 := by simpa using h
      omega
    · exact rfree_ne_zero s.property h
  have hms0 : m ^ 2 * s.val ≠ 0 := mul_ne_zero (pow_ne_zero 2 (by omega)) (rfree_ne_zero s.property)
  rw [← Nat.factorization_le_iff_dvd hk0 (by omega)]
  intro p
  have hle := (Nat.factorization_le_iff_dvd (pow_ne_zero 2 hk0) hms0).mpr hdvd p
  rw [Nat.factorization_pow, Nat.factorization_mul (pow_ne_zero 2 (by omega)) (rfree_ne_zero s.property),
      Nat.factorization_pow] at hle
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at hle
  have hs_lt : s.val.factorization p < 2 :=
    (rfree_iff_factorization_lt (by decide) (rfree_ne_zero s.property)).mp s.property p
  omega

/-- If `r(k² s) = 0` for all `k ≥ 1`, then `photonEnergyCoeff r (m² s) = 0` for all `m ≥ 1`. -/
theorem photonEnergyCoeff_sq_mul_eq_zero_of_all_zero (r : ℕ → ℕ) {s : Core 2}
    (hzero : ∀ k : ℕ, 1 ≤ k → r (k ^ 2 * s.val) = 0) {m : ℕ} (hm : 1 ≤ m) :
    photonEnergyCoeff r (m ^ 2 * s.val) = 0 := by
  unfold photonEnergyCoeff
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨hkIcc, hdvd⟩ := Finset.mem_filter.mp hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hkIcc).1
  obtain ⟨d, hd⟩ := dvd_of_sq_dvd_sq_mul_rfree hm hdvd
  have hd_pos : 1 ≤ d := by
    by_contra h0; have : d = 0 := by omega
    rw [this, mul_zero] at hd; omega
  have hdiv : (m ^ 2 * s.val) / k ^ 2 = d ^ 2 * s.val := by
    have hmul : m ^ 2 * s.val = k ^ 2 * (d ^ 2 * s.val) := by rw [hd]; ring
    rw [hmul, Nat.mul_div_cancel_left _ (pow_pos (by omega) 2)]
  rw [hdiv, hzero d hd_pos, Nat.cast_zero, zero_mul]

theorem photonLogZCoeff_sq_mul_eq_zero_of_all_zero (r : ℕ → ℕ) {s : Core 2}
    (hzero : ∀ k : ℕ, 1 ≤ k → r (k ^ 2 * s.val) = 0) {m : ℕ} (hm : 1 ≤ m) :
    photonLogZCoeff r (m ^ 2 * s.val) = 0 := by
  have hE := photonEnergyCoeff_sq_mul_eq_zero_of_all_zero r hzero hm
  rw [photonEnergyCoeff_eq_sqrt_mul_logZCoeff] at hE
  have hpos : 0 < Real.sqrt ((m ^ 2 * s.val : ℕ) : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast Nat.mul_pos (pow_pos hm 2) (rfree_pos s.property))
  exact (mul_eq_zero.mp hE).resolve_left hpos.ne'

/-- Formal exponential Hahn series `U_photon(t) = ∑_{M ≥ 1} c(M) e^{-√M t} ∈ HahnSeries ℝ ℂ`. -/
def photonEnergyHahn (r : ℕ → ℕ) : HahnSeries ℝ ℂ where
  coeff a :=
    if h : ∃ M : ℕ, 1 ≤ M ∧ a = Real.sqrt (M : ℝ) then
      (photonEnergyCoeff r (Classical.choose h) : ℂ)
    else 0
  isPWO_support' := sqrtSpectrum_isPWO.mono fun a ha ↦ by
    by_contra hnot
    have hneg : ¬ ∃ M : ℕ, 1 ≤ M ∧ a = Real.sqrt (M : ℝ) := hnot
    exact ha (dite_eq_right_iff.mpr fun h ↦ absurd h hneg)

/-- Formal transseries lift `U_photon(t) ∈ TransSeries = HahnSeries ℝ AsympCoeff`. -/
def photonEnergyTrans (r : ℕ → ℕ) : TransSeries where
  coeff a := HahnSeries.C ((photonEnergyHahn r).coeff a)
  isPWO_support' := (photonEnergyHahn r).isPWO_support.mono fun a ha ↦ by
    intro h0; exact ha (by simp [h0])

/-- Formal transseries lift of the grand potential `log Z_photon(t) ∈ TransSeries`. -/
def photonLogZTrans (r : ℕ → ℕ) : TransSeries where
  coeff a :=
    if h : ∃ M : ℕ, 1 ≤ M ∧ a = Real.sqrt (M : ℝ) then
      HahnSeries.C (photonLogZCoeff r (Classical.choose h) : ℂ)
    else 0
  isPWO_support' := sqrtSpectrum_isPWO.mono fun a ha ↦ by
    by_contra hnot
    have hneg : ¬ ∃ M : ℕ, 1 ≤ M ∧ a = Real.sqrt (M : ℝ) := hnot
    exact ha (dite_eq_right_iff.mpr fun h ↦ absurd h hneg)

theorem photonEnergyHahn_coeff_sqrt (r : ℕ → ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (photonEnergyHahn r).coeff (Real.sqrt (M : ℝ)) = (photonEnergyCoeff r M : ℂ) := by
  have hex : ∃ M' : ℕ, 1 ≤ M' ∧ Real.sqrt (M : ℝ) = Real.sqrt (M' : ℝ) := ⟨M, hM, rfl⟩
  change (if h : ∃ M' : ℕ, 1 ≤ M' ∧ Real.sqrt (M : ℝ) = Real.sqrt (M' : ℝ) then
    (photonEnergyCoeff r (Classical.choose h) : ℂ) else 0) = _
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have hspec := Classical.choose_spec hex
  have heq : Classical.choose hex = M := by
    have hsq := congrArg (· ^ 2) hspec.2
    rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
    exact_mod_cast hsq.symm
  rw [heq]

theorem photonEnergyTrans_coeff_sqrt (r : ℕ → ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (photonEnergyTrans r).coeff (Real.sqrt (M : ℝ)) =
      HahnSeries.C (photonEnergyCoeff r M : ℂ) := by
  change HahnSeries.C ((photonEnergyHahn r).coeff (Real.sqrt (M : ℝ))) = _
  rw [photonEnergyHahn_coeff_sqrt r hM]

theorem photonLogZTrans_coeff_sqrt (r : ℕ → ℕ) {M : ℕ} (hM : 1 ≤ M) :
    (photonLogZTrans r).coeff (Real.sqrt (M : ℝ)) =
      HahnSeries.C (photonLogZCoeff r M : ℂ) := by
  have hex : ∃ M' : ℕ, 1 ≤ M' ∧ Real.sqrt (M : ℝ) = Real.sqrt (M' : ℝ) := ⟨M, hM, rfl⟩
  change (if h : ∃ M' : ℕ, 1 ≤ M' ∧ Real.sqrt (M : ℝ) = Real.sqrt (M' : ℝ) then
    HahnSeries.C (photonLogZCoeff r (Classical.choose h) : ℂ) else 0) = _
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  have hspec := Classical.choose_spec hex
  have heq : Classical.choose hex = M := by
    have hsq := congrArg (· ^ 2) hspec.2
    rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)] at hsq
    exact_mod_cast hsq.symm
  rw [heq]

theorem photonEnergyTrans_support_subset (r : ℕ → ℕ) :
    (photonEnergyTrans r).support ⊆ sqrtSpectrum := by
  intro a ha
  by_contra hnot
  apply ha
  change HahnSeries.C ((photonEnergyHahn r).coeff a) = 0
  have h0 : (photonEnergyHahn r).coeff a = 0 := by
    change (if h : ∃ M : ℕ, 1 ≤ M ∧ a = Real.sqrt (M : ℝ) then _ else 0) = 0
    exact dite_eq_right_of_eq_false (eq_false hnot)
  rw [h0, map_zero]

theorem photonLogZTrans_support_subset (r : ℕ → ℕ) :
    (photonLogZTrans r).support ⊆ sqrtSpectrum := by
  intro a ha
  by_contra hnot
  apply ha
  change (if h : ∃ M : ℕ, 1 ≤ M ∧ a = Real.sqrt (M : ℝ) then _ else 0) = 0
  exact dite_eq_right_of_eq_false (eq_false hnot)

/-- **Exact Thermodynamic Identity (`d/dt log Z_photon(t) = -U_photon(t)`)** in `TransSeries`:
`transDerivX (photonLogZTrans r) = -(photonEnergyTrans r)`. -/
theorem transDerivX_photonLogZTrans (r : ℕ → ℕ) :
    transDerivX (photonLogZTrans r) = -(photonEnergyTrans r) := by
  apply HahnSeries.ext; funext a
  rw [transDerivX_coeff, HahnSeries.coeff_neg]
  by_cases ha : a ∈ sqrtSpectrum
  · obtain ⟨M, hM, rfl⟩ := ha
    rw [photonLogZTrans_coeff_sqrt r hM, photonEnergyTrans_coeff_sqrt r hM]
    have hdz : asympDerivX (HahnSeries.C (photonLogZCoeff r M : ℂ)) = 0 := by
      apply HahnSeries.ext; funext γ
      rw [asympDerivX_coeff, HahnSeries.coeff_zero, HahnSeries.C_apply, HahnSeries.coeff_single]
      split_ifs with hγ
      · simp [hγ]
      · simp
    rw [hdz, zero_add]
    apply HahnSeries.ext; funext γ
    rw [HahnSeries.coeff_smul, HahnSeries.coeff_neg, HahnSeries.C_apply, HahnSeries.C_apply,
        HahnSeries.coeff_single, HahnSeries.coeff_single]
    split_ifs with h0
    · rw [smul_eq_mul, photonEnergyCoeff_eq_sqrt_mul_logZCoeff]
      push_cast; ring
    · simp
  · have hlog0 : (photonLogZTrans r).coeff a = 0 := by
      by_contra hne; exact ha (photonLogZTrans_support_subset r hne)
    have hE0 : (photonEnergyTrans r).coeff a = 0 := by
      by_contra hne; exact ha (photonEnergyTrans_support_subset r hne)
    have hdz : asympDerivX (0 : AsympCoeff) = 0 := by apply HahnSeries.ext; funext γ; simp
    simp [hlog0, hE0, hdz]

/-- Physical 2D, 3D, and 4D relativistic blackbody photon gas internal energies in `TransSeries`. -/
def photonEnergyTrans2D : TransSeries := photonEnergyTrans r2Count
def photonEnergyTrans3D : TransSeries := photonEnergyTrans r3Count
def photonEnergyTrans4D : TransSeries := photonEnergyTrans r4Count

/-- Physical 2D, 3D, and 4D relativistic blackbody photon gas grand potentials `log Z` in `TransSeries`. -/
def photonLogZTrans2D : TransSeries := photonLogZTrans r2Count
def photonLogZTrans3D : TransSeries := photonLogZTrans r3Count
def photonLogZTrans4D : TransSeries := photonLogZTrans r4Count

/-- Analytic internal energy of the relativistic blackbody photon gas for `t > 0`:
`U_photon(t) = ∑_{N ≥ 1} r(N) √N / (e^{√N t} - 1)`. -/
def photonEnergyAnalytic (r : ℕ → ℕ) (t : ℝ) : ℝ :=
  ∑' N : ℕ+, (r N.val : ℝ) * Real.sqrt (N.val : ℝ) / (Real.exp (Real.sqrt (N.val : ℝ) * t) - 1)

/-- Elementary exponential-decay summability for polynomial weights on `ℕ+ × ℕ+`. -/
private lemma summable_poly_mul_exp_neg_sqrt {C : ℝ} {d : ℕ} {t : ℝ} (ht : 0 < t) :
    Summable (fun p : ℕ+ × ℕ+ ↦
      C * (((p.2.val + 1 : ℕ) : ℝ) ^ d) * Real.sqrt (p.2.val : ℝ) *
        Real.exp (-(p.1.val : ℝ) * Real.sqrt (p.2.val : ℝ) * t)) := by
  -- Use `e^x ≥ x^(2d+6) / (2d+6)!` on `x ≥ 0` to bound by `K * (k^2 * N)^(-2)`!
  let m : ℕ := 2 * d + 6
  have hbound : ∀ p : ℕ+ × ℕ+,
      ‖C * (((p.2.val + 1 : ℕ) : ℝ) ^ d) * Real.sqrt (p.2.val : ℝ) *
        Real.exp (-(p.1.val : ℝ) * Real.sqrt (p.2.val : ℝ) * t)‖ ≤
      (|C| * (2 : ℝ) ^ d * (Nat.factorial m : ℝ) / t ^ m) *
        ((1 / (p.1.val : ℝ) ^ 2) * (1 / (p.2.val : ℝ) ^ 2)) := by
    intro ⟨k, N⟩
    have hk1 : (1 : ℝ) ≤ (k.val : ℝ) := by exact_mod_cast k.pos
    have hN1 : (1 : ℝ) ≤ (N.val : ℝ) := by exact_mod_cast N.pos
    have hsqN1 : (1 : ℝ) ≤ Real.sqrt (N.val : ℝ) := by
      rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN1
    have hx_pos : 0 < (k.val : ℝ) * Real.sqrt (N.val : ℝ) * t := by positivity
    have hexp_ge : ((k.val : ℝ) * Real.sqrt (N.val : ℝ) * t) ^ m / (Nat.factorial m : ℝ) ≤
        Real.exp ((k.val : ℝ) * Real.sqrt (N.val : ℝ) * t) :=
      Real.pow_div_factorial_le_exp _ hx_pos.le m
    have hexp_le : Real.exp (-(k.val : ℝ) * Real.sqrt (N.val : ℝ) * t) ≤
        (Nat.factorial m : ℝ) / ((k.val : ℝ) * Real.sqrt (N.val : ℝ) * t) ^ m := by
      have hneg : -(k.val : ℝ) * Real.sqrt (N.val : ℝ) * t =
          -((k.val : ℝ) * Real.sqrt (N.val : ℝ) * t) := by ring
      rw [hneg, Real.exp_neg]
      have hpos_lhs : 0 < ((k.val : ℝ) * Real.sqrt (N.val : ℝ) * t) ^ m / (Nat.factorial m : ℝ) := by
        positivity
      have hinv := inv_anti₀ hpos_lhs hexp_ge
      rwa [inv_div] at hinv
    have hNadd : ((N.val + 1 : ℕ) : ℝ) ^ d ≤ (2 : ℝ) ^ d * (N.val : ℝ) ^ d := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      push_cast; linarith
    have hpow_ge : (k.val : ℝ) ^ 2 * (N.val : ℝ) ^ (d + 3) ≤
        ((k.val : ℝ) * Real.sqrt (N.val : ℝ)) ^ m := by
      rw [mul_pow]
      have hk_le : (k.val : ℝ) ^ 2 ≤ (k.val : ℝ) ^ m :=
        pow_le_pow_right₀ hk1 (by dsimp [m]; omega)
      have hsq_eq : (Real.sqrt (N.val : ℝ)) ^ m = (N.val : ℝ) ^ (d + 3) := by
        have hm2 : m = 2 * (d + 3) := by dsimp [m]; omega
        rw [hm2, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
      rw [hsq_eq]
      exact mul_le_mul_of_nonneg_right hk_le (by positivity)
    have hsq_le_N : Real.sqrt (N.val : ℝ) ≤ (N.val : ℝ) := by
      calc Real.sqrt (N.val : ℝ) ≤ Real.sqrt ((N.val : ℝ) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = (N.val : ℝ) := Real.sqrt_sq (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((N.val + 1 : ℕ) : ℝ) ^ d),
        abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_pos (Real.exp_pos _)]
    have hden_pos : 0 < ((k.val : ℝ) * Real.sqrt (N.val : ℝ) * t) ^ m := by positivity
    dsimp only
    calc |C| * ((N.val + 1 : ℕ) : ℝ) ^ d * Real.sqrt (N.val : ℝ) *
            Real.exp (-(k.val : ℝ) * Real.sqrt (N.val : ℝ) * t)
        ≤ |C| * ((2 : ℝ) ^ d * (N.val : ℝ) ^ d) * (N.val : ℝ) *
            ((Nat.factorial m : ℝ) / ((k.val : ℝ) * Real.sqrt (N.val : ℝ) * t) ^ m) := by
          gcongr
      _ = |C| * (2 : ℝ) ^ d * (Nat.factorial m : ℝ) / t ^ m *
            ((N.val : ℝ) ^ (d + 1) / ((k.val : ℝ) * Real.sqrt (N.val : ℝ)) ^ m) := by
          rw [mul_pow]; ring
      _ ≤ |C| * (2 : ℝ) ^ d * (Nat.factorial m : ℝ) / t ^ m *
            ((N.val : ℝ) ^ (d + 1) / ((k.val : ℝ) ^ 2 * (N.val : ℝ) ^ (d + 3))) := by
          gcongr
      _ = |C| * (2 : ℝ) ^ d * (Nat.factorial m : ℝ) / t ^ m *
            ((1 / (k.val : ℝ) ^ 2) * (1 / (N.val : ℝ) ^ 2)) := by
          have hk0 : (k.val : ℝ) ≠ 0 := by positivity
          have hN0 : (N.val : ℝ) ≠ 0 := by positivity
          have hexp3 : (N.val : ℝ) ^ (d + 3) = (N.val : ℝ) ^ (d + 1) * (N.val : ℝ) ^ 2 := by
            rw [← pow_add]
          rw [hexp3]; field_simp [hk0, hN0]
  have hsum_inv : Summable (fun n : ℕ+ ↦ 1 / (n.val : ℝ) ^ 2) := by
    have hnat : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) := by
      simp [one_div]
    exact hnat.comp_injective PNat.coe_injective
  have hprod : Summable (fun p : ℕ+ × ℕ+ ↦
      (|C| * (2 : ℝ) ^ d * (Nat.factorial m : ℝ) / t ^ m) *
        ((1 / (p.1.val : ℝ) ^ 2) * (1 / (p.2.val : ℝ) ^ 2))) :=
    (hsum_inv.mul_of_nonneg hsum_inv (fun _ ↦ by positivity) (fun _ ↦ by positivity)).mul_left _
  exact Summable.of_norm_bounded hprod hbound

/-- **Exact Analytic Regrouping Identity for Relativistic Blackbody Photon Gases (`t > 0`)**:
For any polynomially bounded lattice count `r` (in particular `r2Count`, `r3Count`, `r4Count`)
and every `t > 0`:
`∑'_{N : ℕ+} r(N) √N / (e^{√N t} - 1) = ∑'_{M : ℕ+} photonEnergyCoeff r M · e^{-√M t}`. -/
theorem photonEnergyAnalytic_eq_tsum_sqrt {r : ℕ → ℕ} {C : ℝ} {d : ℕ}
    (hbound : ∀ N : ℕ, (r N : ℝ) ≤ C * ((N + 1 : ℕ) : ℝ) ^ d) {t : ℝ} (ht : 0 < t) :
    photonEnergyAnalytic r t =
      ∑' M : ℕ+, photonEnergyCoeff r M.val * Real.exp (-Real.sqrt (M.val : ℝ) * t) := by
  let f : ℕ+ × ℕ+ → ℝ := fun p ↦
    (r p.2.val : ℝ) * Real.sqrt (p.2.val : ℝ) *
      Real.exp (-(p.1.val : ℝ) * Real.sqrt (p.2.val : ℝ) * t)
  have hf_nn : ∀ p, 0 ≤ f p := fun p ↦ by dsimp [f]; positivity
  have hf_sum : Summable f := by
    refine Summable.of_nonneg_of_le hf_nn (fun p ↦ ?_) (summable_poly_mul_exp_neg_sqrt (C := C) (d := d) ht)
    dsimp [f]
    have hN : (r p.2.val : ℝ) ≤ C * ((p.2.val + 1 : ℕ) : ℝ) ^ d := hbound p.2.val
    gcongr
  -- Step 1: Sum over `k` first gives `photonEnergyAnalytic r t`.
  have hstep1 : (∑' p : ℕ+ × ℕ+, f p) = photonEnergyAnalytic r t := by
    have hcomm : (∑' p : ℕ+ × ℕ+, f p) = ∑' N : ℕ+, ∑' k : ℕ+, f (k, N) := by
      have hs : Summable (fun q : ℕ+ × ℕ+ ↦ f q.swap) :=
        hf_sum.comp_injective (Equiv.prodComm ℕ+ ℕ+).injective
      calc (∑' p : ℕ+ × ℕ+, f p) = ∑' q : ℕ+ × ℕ+, f q.swap :=
            ((Equiv.prodComm ℕ+ ℕ+).tsum_eq f).symm
        _ = ∑' N : ℕ+, ∑' k : ℕ+, f (k, N) :=
            hs.tsum_prod' (fun N ↦ hs.comp_injective (fun k₁ k₂ h ↦ by
              simpa using congrArg Prod.snd h))
    have hinner (N : ℕ+) : (∑' k : ℕ+, f (k, N)) =
        (r N.val : ℝ) * Real.sqrt (N.val : ℝ) / (Real.exp (Real.sqrt (N.val : ℝ) * t) - 1) := by
      let x : ℝ := Real.sqrt (N.val : ℝ) * t
      have hx_pos : 0 < x := mul_pos (Real.sqrt_pos.mpr (by exact_mod_cast N.pos)) ht
      have hr_lt1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      have hgeom : (∑' k : ℕ+, Real.exp (-(k.val : ℝ) * x)) = 1 / (Real.exp x - 1) := by
        have heq : (fun k : ℕ+ ↦ Real.exp (-(k.val : ℝ) * x)) = fun k : ℕ+ ↦ Real.exp (-x) ^ k.val := by
          funext k; rw [← Real.exp_nat_mul]; congr 1; ring
        rw [heq]
        have hshift : (∑' k : ℕ+, Real.exp (-x) ^ k.val) =
            ∑' n : ℕ, Real.exp (-x) * Real.exp (-x) ^ n := by
          rw [← Equiv.pnatEquivNat.symm.tsum_eq (fun k : ℕ+ ↦ Real.exp (-x) ^ k.val)]
          apply tsum_congr; intro n
          simp [Equiv.pnatEquivNat, pow_succ']
        rw [hshift, tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hr_lt1]
        have hexp_ne : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr (Real.one_lt_exp_iff.mpr hx_pos).ne'
        rw [Real.exp_neg]
        field_simp [hexp_ne, (Real.exp_pos x).ne']
      calc (∑' k : ℕ+, f (k, N))
          = (r N.val : ℝ) * Real.sqrt (N.val : ℝ) * ∑' k : ℕ+, Real.exp (-(k.val : ℝ) * x) := by
            rw [← tsum_mul_left]; apply tsum_congr; intro k; dsimp [f, x]; congr 1; congr 1; ring
        _ = (r N.val : ℝ) * Real.sqrt (N.val : ℝ) / (Real.exp x - 1) := by
            rw [hgeom, mul_one_div]
    rw [hcomm]
    exact tsum_congr hinner
  -- Step 2: Group by fiber `g (k, N) = k² * N : ℕ+` via `Equiv.sigmaFiberEquiv g`!
  let g : ℕ+ × ℕ+ → ℕ+ := fun p ↦ ⟨p.1.val ^ 2 * p.2.val, Nat.mul_pos (pow_pos p.1.pos 2) p.2.pos⟩
  have hfiber (M : ℕ+) : (∑' p : {p : ℕ+ × ℕ+ // g p = M}, f p.val) =
      photonEnergyCoeff r M.val * Real.exp (-Real.sqrt (M.val : ℝ) * t) := by
    let S : Finset ℕ := (Finset.Icc 1 M.val).filter (fun k ↦ k ^ 2 ∣ M.val)
    let e : S ≃ {p : ℕ+ × ℕ+ // g p = M} :=
      { toFun := fun ⟨k, hk⟩ ↦
          have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
          have hdvd : k ^ 2 ∣ M.val := (Finset.mem_filter.mp hk).2
          have hdiv_pos : 0 < M.val / k ^ 2 :=
            Nat.div_pos (Nat.le_of_dvd M.pos hdvd) (pow_pos (by omega) 2)
          ⟨(⟨k, by omega⟩, ⟨M.val / k ^ 2, hdiv_pos⟩), Subtype.ext (Nat.mul_div_cancel' hdvd)⟩
        invFun := fun ⟨⟨k, N⟩, hEq⟩ ↦
          have hval : k.val ^ 2 * N.val = M.val := congrArg Subtype.val hEq
          have hk_le : k.val ≤ M.val := by
            have h1 : k.val ≤ k.val ^ 2 := Nat.le_self_pow (by decide) k.val
            have h2 : k.val ^ 2 ≤ k.val ^ 2 * N.val := Nat.le_mul_of_pos_right _ N.pos
            omega
          ⟨k.val, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨k.pos, hk_le⟩, ⟨N.val, hval.symm⟩⟩⟩
        left_inv := fun ⟨k, _⟩ ↦ rfl
        right_inv := fun ⟨⟨k, N⟩, hEq⟩ ↦ by
          have hval : k.val ^ 2 * N.val = M.val := congrArg Subtype.val hEq
          apply Subtype.ext; apply Prod.ext
          · rfl
          · apply PNat.eq
            change M.val / k.val ^ 2 = N.val
            rw [← hval, Nat.mul_div_cancel_left _ (pow_pos k.pos 2)] }
    rw [← e.tsum_eq (fun p : {p : ℕ+ × ℕ+ // g p = M} ↦ f p.val), tsum_fintype,
        photonEnergyCoeff, Finset.sum_mul]
    rw [← Finset.sum_attach S (fun k ↦ (r (M.val / k ^ 2) : ℝ) *
      Real.sqrt ((M.val / k ^ 2 : ℕ) : ℝ) * Real.exp (-Real.sqrt (M.val : ℝ) * t))]
    rw [Finset.univ_eq_attach]
    apply Finset.sum_congr rfl
    rintro ⟨k, hk⟩ _
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    have hdvd : k ^ 2 ∣ M.val := (Finset.mem_filter.mp hk).2
    have hmul : k ^ 2 * (M.val / k ^ 2) = M.val := Nat.mul_div_cancel' hdvd
    have hsq : (k : ℝ) * Real.sqrt ((M.val / k ^ 2 : ℕ) : ℝ) = Real.sqrt (M.val : ℝ) := by
      conv_rhs => rw [← hmul]
      rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg k)]
    dsimp [e, f]
    congr 1; congr 1
    linarith [congrArg (· * t) hsq]
  have hsigma : (∑' p : ℕ+ × ℕ+, f p) = ∑' M : ℕ+, ∑' p : {p : ℕ+ × ℕ+ // g p = M}, f p.val := by
    have hs : Summable (fun q : (M : ℕ+) × {p : ℕ+ × ℕ+ // g p = M} ↦ f (Equiv.sigmaFiberEquiv g q)) :=
      hf_sum.comp_injective (Equiv.sigmaFiberEquiv g).injective
    calc (∑' p : ℕ+ × ℕ+, f p)
        = ∑' q : (M : ℕ+) × {p : ℕ+ × ℕ+ // g p = M}, f (Equiv.sigmaFiberEquiv g q) :=
          ((Equiv.sigmaFiberEquiv g).tsum_eq f).symm
      _ = ∑' M : ℕ+, ∑' p : {p : ℕ+ × ℕ+ // g p = M}, f p.val := hs.tsum_sigma
  rw [← hstep1, hsigma]
  exact tsum_congr hfiber

/-! ### 3. Unified Triangular Core-Separation Engine & Crown-Jewel Photon Gas Theorems -/

/-- Helper: Vandermonde jet determinant non-vanishing for ANY injective nonzero real actions
`a : Fin J → ℝ` (generalizing `transseries_vandermonde_det_ne_zero` from `StrictMono` to `Injective`). -/
private theorem transseries_vandermonde_det_ne_zero_of_inj {J : ℕ} (a : Fin J → ℝ)
    (ha_inj : Function.Injective a) (ha_nz : ∀ i : Fin J, a i ≠ 0)
    (Y : TransSeries) (hY : ∀ i : Fin J, Y.coeff (a i) ≠ 0) :
    (Matrix.of fun i j : Fin J ↦ (transDerivX^[j.val] Y).coeff (a i)).det ≠ 0 := by
  classical
  let S : Finset ℝ := Finset.univ.image a
  have hScard : S.card = J := by
    rw [Finset.card_image_of_injective _ ha_inj, Finset.card_fin]
  let emb : Fin J ↪o ℝ := S.orderEmbOfFin hScard
  have hmem (i : Fin J) : emb i ∈ S := Finset.orderEmbOfFin_mem S hScard i
  let toIdx : Fin J → Fin J := fun i ↦ (Finset.mem_image.mp (hmem i)).choose
  have htoIdx_eq (i : Fin J) : a (toIdx i) = emb i := (Finset.mem_image.mp (hmem i)).choose_spec.2
  have htoIdx_inj : Function.Injective toIdx := fun i₁ i₂ h ↦ by
    have : emb i₁ = emb i₂ := by rw [← htoIdx_eq i₁, ← htoIdx_eq i₂, h]
    exact emb.injective this
  let σ : Equiv.Perm (Fin J) := Equiv.ofBijective toIdx (Finite.injective_iff_bijective.mp htoIdx_inj)
  have hmono : StrictMono (a ∘ σ) := by
    intro i j hij
    change a (toIdx i) < a (toIdx j)
    rw [htoIdx_eq i, htoIdx_eq j]
    exact emb.strictMono hij
  have hdet_perm : (Matrix.of fun i j : Fin J ↦ (transDerivX^[j.val] Y).coeff ((a ∘ σ) i)).det ≠ 0 :=
    transseries_vandermonde_det_ne_zero (a ∘ σ) hmono (fun i ↦ ha_nz (σ i)) Y (fun i ↦ hY (σ i))
  have hsub : (Matrix.of fun i j : Fin J ↦ (transDerivX^[j.val] Y).coeff ((a ∘ σ) i)) =
      (Matrix.of fun i j : Fin J ↦ (transDerivX^[j.val] Y).coeff (a i)).submatrix σ id := by
    ext i j; rfl
  rw [hsub, Matrix.det_permute] at hdet_perm
  intro h0
  rw [h0, mul_zero] at hdet_perm
  exact hdet_perm rfl

/-- **Unified Triangular Core-Separation Engine (`triangular_core_transseries_diff_indep`)**:
Let `U : Fin m → TransSeries` be `m` formal transseries supported on `sqrtSpectrum = {√M : M ≥ 1}`.
Suppose that for every index `i : Fin m`, there are infinitely many square-free cores `s : Core 2`
such that:
1. every earlier series `U i'` (`i' < i`) vanishes on the entire ray `{k √s : k ≥ 1}`, and
2. `U i` is nonzero at some point `k √s` (`k ≥ 1`).
Then for EVERY derivative order `J : ℕ`, the combined `(m × J)`-jet
`(i, j) ↦ transDerivX^[j] (U i)` is **algebraically independent over `AsympCoeff`**! -/
theorem triangular_core_transseries_diff_indep {m : ℕ} (U : Fin m → TransSeries)
    (hsupp : ∀ i : Fin m, (U i).support ⊆ sqrtSpectrum)
    (hsep : ∀ i : Fin m,
      {s : Core 2 |
        (∀ i' : Fin m, i' < i → ∀ k : ℕ, 1 ≤ k → (U i').coeff ((k : ℝ) * Real.sqrt (s.val : ℝ)) = 0) ∧
        (∃ k : ℕ, 1 ≤ k ∧ (U i).coeff ((k : ℝ) * Real.sqrt (s.val : ℝ)) ≠ 0)}.Infinite)
    (J : ℕ) :
    AlgebraicIndependent AsympCoeff (fun p : Fin m × Fin J ↦ transDerivX^[p.2.val] (U p.1)) := by
  classical
  have : CharZero AsympCoeff := charZero_of_injective_algebraMap
    (R := ℂ) (HahnSeries.C_injective (Γ := ℝ) (R := ℂ))
  let Y : Fin m × Fin J → TransSeries := fun p ↦ transDerivX^[p.2.val] (U p.1)
  let ev := MvPolynomial.aeval (R := AsympCoeff) Y
  let ratHom : ℚ →+* AsympCoeff := HahnSeries.C.comp (Rat.castHom ℂ)
  -- Core step: any vanishing polynomial relation `ev P = 0` forces every partial `ev (pderiv p P) = 0`!
  have hstable : ∀ {P : MvPolynomial (Fin m × Fin J) AsympCoeff}, ev P = 0 →
      ∀ p : Fin m × Fin J, ev (pderiv p P) = 0 := by
    intro P hP
    let G : Fin m × Fin J → TransSeries := fun p ↦ ev (pderiv p P)
    -- Prove `G (i, j) = 0` by downward induction on `i` (i.e. induction on `m - 1 - i.val`)!
    have hdown : ∀ (d : ℕ) (i : Fin m), m - 1 - i.val = d → ∀ j : Fin J, G (i, j) = 0 := by
      intro d
      induction d using Nat.strong_induction_on with
      | ind d ih =>
        intro i hi
        have hgt_zero : ∀ i'' : Fin m, i < i'' → ∀ j : Fin J, G (i'', j) = 0 := by
          intro i'' hi'' j
          have hlt : m - 1 - i''.val < d := by omega
          exact ih (m - 1 - i''.val) hlt i'' rfl j
        by_contra hnot
        push Not at hnot
        obtain ⟨j₀, hj₀⟩ := hnot
        -- Global minimal exponent `μ₀` of the `i`-th block `{G (i, j) : j < J}`.
        let S : Set ℝ := ⋃ j : Fin J, (G (i, j)).support
        have hSne : S.Nonempty := by
          obtain ⟨μ, hμ⟩ := HahnSeries.support_nonempty_iff.mpr hj₀
          exact ⟨μ, Set.mem_iUnion.mpr ⟨j₀, hμ⟩⟩
        have hSwf : S.IsWF := isWF_iUnion_fin (fun j ↦ (G (i, j)).support) (fun j ↦ (G (i, j)).isWF_support)
        let μ₀ : ℝ := hSwf.min hSne
        have hμ₀_mem : μ₀ ∈ S := hSwf.min_mem hSne
        have hμ₀_le : ∀ (j : Fin J) (x : ℝ), x ∈ (G (i, j)).support → μ₀ ≤ x := by
          intro j x hx
          by_contra hlt
          exact hSwf.not_lt_min hSne (Set.mem_iUnion.mpr ⟨j, hx⟩) (not_le.mp hlt)
        let rvec : Fin J → AsympCoeff := fun j ↦ (G (i, j)).coeff μ₀
        have hr_ne : rvec ≠ 0 := by
          obtain ⟨j₁, hj₁⟩ := Set.mem_iUnion.mp hμ₀_mem
          intro hr0
          exact hj₁ (congrFun hr0 j₁)
        -- Pick `J` pairwise distinct separating square-free cores `s : Fin J → Core 2`.
        obtain ⟨T, hTsub, hTcard⟩ := (hsep i).exists_subset_card_eq J
        let eT : Fin J ≃ T := (Fintype.equivOfCardEq (by simp [hTcard])).symm
        let s : Fin J → Core 2 := fun ν ↦ (eT ν).val
        have hs_inj : Function.Injective s := fun ν₁ ν₂ h ↦ eT.injective (Subtype.ext h)
        have hs_lt : ∀ ν : Fin J, ∀ i' : Fin m, i' < i → ∀ k : ℕ, 1 ≤ k →
            (U i').coeff ((k : ℝ) * Real.sqrt ((s ν).val : ℝ)) = 0 :=
          fun ν ↦ (hTsub (eT ν).property).1
        have hs_ex : ∀ ν : Fin J, ∃ k : ℕ, 1 ≤ k ∧
            (U i).coeff ((k : ℝ) * Real.sqrt ((s ν).val : ℝ)) ≠ 0 :=
          fun ν ↦ (hTsub (eT ν).property).2
        -- For each `ν`, choose the MINIMAL `k* ν ≥ 1` with `(U i).coeff (k* ν * √(s ν)) ≠ 0`.
        let kStar : Fin J → ℕ := fun ν ↦ Nat.find (hs_ex ν)
        have hkStar_pos (ν : Fin J) : 1 ≤ kStar ν := (Nat.find_spec (hs_ex ν)).1
        have hkStar_ne (ν : Fin J) : (U i).coeff ((kStar ν : ℝ) * Real.sqrt ((s ν).val : ℝ)) ≠ 0 :=
          (Nat.find_spec (hs_ex ν)).2
        have hkStar_min (ν : Fin J) {k : ℕ} (hk1 : 1 ≤ k) (hklt : k < kStar ν) :
            (U i).coeff ((k : ℝ) * Real.sqrt ((s ν).val : ℝ)) = 0 := by
          by_contra hne
          exact Nat.find_min (hs_ex ν) hklt ⟨hk1, hne⟩
        let a : Fin J → ℝ := fun ν ↦ (kStar ν : ℝ) * Real.sqrt ((s ν).val : ℝ)
        have ha_pos (ν : Fin J) : 0 < a ν :=
          mul_pos (by exact_mod_cast hkStar_pos ν)
            (Real.sqrt_pos.mpr (by exact_mod_cast rfree_pos (s ν).property))
        have ha_inj : Function.Injective a := fun ν₁ ν₂ h ↦ by
          have hsq : ((kStar ν₁ ^ 2 * (s ν₁).val : ℕ) : ℝ) = ((kStar ν₂ ^ 2 * (s ν₂).val : ℕ) : ℝ) := by
            have h1 := congrArg (· ^ 2) h
            dsimp only [a] at h1
            rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)] at h1
            push_cast; exact h1
          have hnat : kStar ν₁ ^ 2 * (s ν₁).val = kStar ν₂ ^ 2 * (s ν₂).val := by exact_mod_cast hsq
          have huniq := rfree_factor_unique (r := 2) (by decide) (hkStar_pos ν₁) (hkStar_pos ν₂) hnat
          exact hs_inj huniq.1
        -- Define the `J × J` matrix `M_{ν, j} = (kStar ν : AsympCoeff) * (transDerivX^[j] (U i)).coeff (a ν)`.
        let M : Matrix (Fin J) (Fin J) AsympCoeff :=
          Matrix.of fun ν j ↦ ((kStar ν : ℕ) : AsympCoeff) * (Y (i, j)).coeff (a ν)
        have hM_det : M.det ≠ 0 := by
          have hfac : M = Matrix.diagonal (fun ν : Fin J ↦ ((kStar ν : ℕ) : AsympCoeff)) *
              Matrix.of (fun ν j : Fin J ↦ (transDerivX^[j.val] (U i)).coeff (a ν)) := by
            ext ν j; simp [M, Y, Matrix.diagonal_mul]
          rw [hfac, Matrix.det_mul, Matrix.det_diagonal]
          refine mul_ne_zero ?_ ?_
          · exact Finset.prod_ne_zero_iff.mpr fun ν _ ↦ Nat.cast_ne_zero.mpr (by have := hkStar_pos ν; omega)
          · exact transseries_vandermonde_det_ne_zero_of_inj a ha_inj (fun ν ↦ (ha_pos ν).ne') (U i) hkStar_ne
        -- Show `M *ᵥ rvec = 0` by applying `hahnDeriv ψ_ν` to `ev P = 0` and extracting `[μ₀ + a ν]`!
        have hMr : M *ᵥ rvec = 0 := by
          funext ν
          obtain ⟨φ, _, _, hφM⟩ := exists_core_functional (s ν)
          let ψ : ℝ →+ AsympCoeff := ratHom.toAddMonoidHom.comp φ.toAddMonoidHom
          have hψ_sqrt (M' : ℕ+) : ψ (Real.sqrt (M'.val : ℝ)) =
              if rFreeCore 2 (by decide) M' = s ν then ((rFreeRoot 2 (by decide) M' : ℕ) : AsympCoeff) else 0 := by
            change ratHom (φ (Real.sqrt (M'.val : ℝ))) = _
            rw [hφM M']
            split_ifs <;> simp [ratHom]
          -- For every `i' < i` and every `j`, `hahnDeriv ψ (Y (i', j)) = 0`!
          have hlt_deriv_zero (i' : Fin m) (hi' : i' < i) (j : Fin J) :
              hahnDeriv ψ (Y (i', j)) = 0 := by
            ext x
            rw [hahnDeriv_coeff, HahnSeries.coeff_zero]
            by_cases hx : x ∈ (Y (i', j)).support
            · have hx_spec : x ∈ sqrtSpectrum := hsupp i' (transDerivX_iterate_support_subset (U i') j.val hx)
              obtain ⟨M', hM', rfl⟩ := hx_spec
              let Mp : ℕ+ := ⟨M', hM'⟩
              rw [show (M' : ℝ) = (Mp.val : ℝ) from rfl, hψ_sqrt Mp]
              split_ifs with hcore
              · -- Then `M' = k^2 * s ν`, where `U i'` vanishes!
                have hfac : (rFreeRoot 2 (by decide) Mp) ^ 2 * (s ν).val = M' := by
                  rw [← hcore]; exact rFreeRoot_pow_mul_core 2 (by decide) Mp
                have hsq : Real.sqrt (Mp.val : ℝ) =
                    ((rFreeRoot 2 (by decide) Mp : ℕ) : ℝ) * Real.sqrt ((s ν).val : ℝ) := by
                  change Real.sqrt (M' : ℝ) = _
                  rw [← hfac, Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _),
                      Real.sqrt_sq (Nat.cast_nonneg _)]
                exfalso
                have hU0 : (U i').coeff (Real.sqrt (Mp.val : ℝ)) = 0 := by
                  rw [hsq]; exact hs_lt ν i' hi' _ (rFreeRoot_pos 2 (by decide) Mp)
                exact transDerivX_iterate_support_subset (U i') j.val hx hU0
              · simp
            · have hx0 : (Y (i', j)).coeff x = 0 := by by_contra hne; exact hx hne
              rw [hx0, mul_zero]
          -- Apply `hahnDeriv ψ` to `ev P = 0`!
          have hchain : (∑ p : Fin m × Fin J, G p * hahnDeriv ψ (Y p)) = 0 := by
            have h0 := hahnDeriv_aeval ψ Y P
            rw [hP, hahnDeriv_zero] at h0
            exact h0.symm
          -- Collapse the outer sum over `Fin m` to JUST block `i`!
          have hblock_sum : (∑ j : Fin J, G (i, j) * hahnDeriv ψ (Y (i, j))) = 0 := by
            rw [Fintype.sum_prod_type] at hchain
            rw [← hchain]
            symm
            refine Finset.sum_eq_single i (fun i' _ hne ↦ ?_) (fun hnot ↦ absurd (Finset.mem_univ i) hnot)
            apply Finset.sum_eq_zero; intro j _
            rcases lt_or_gt_of_ne hne with hlt | hgt
            · rw [hlt_deriv_zero i' hlt j]; exact mul_zero (M₀ := TransSeries) _
            · rw [hgt_zero i' hgt j]; exact zero_mul (M₀ := TransSeries) _
          have hcoeff_sum : ∑ j : Fin J, (G (i, j) * hahnDeriv ψ (Y (i, j))).coeff (μ₀ + a ν) = 0 := by
            have hc := congrArg (fun f : TransSeries ↦ f.coeff (μ₀ + a ν)) hblock_sum
            simpa [HahnSeries.coeff_sum] using hc
          -- Lower bound on support of `hahnDeriv ψ (Y (i, j))`: every element is `≥ a ν`!
          have hsupp_ge (j : Fin J) (y : ℝ) (hy : y ∈ (hahnDeriv ψ (Y (i, j))).support) : a ν ≤ y := by
            have hyY : y ∈ (Y (i, j)).support := hahnDeriv_support_subset ψ (Y (i, j)) hy
            have hyU : y ∈ (U i).support := transDerivX_iterate_support_subset (U i) j.val hyY
            obtain ⟨M', hM', rfl⟩ := hsupp i hyU
            let Mp : ℕ+ := ⟨M', hM'⟩
            have hψ_ne : ψ (Real.sqrt (Mp.val : ℝ)) ≠ 0 := left_ne_zero_of_mul hy
            rw [hψ_sqrt Mp] at hψ_ne
            have hcore : rFreeCore 2 (by decide) Mp = s ν := by
              by_contra hne; simp [hne] at hψ_ne
            let k := rFreeRoot 2 (by decide) Mp
            have hk_pos : 1 ≤ k := rFreeRoot_pos 2 (by decide) Mp
            have hfac : k ^ 2 * (s ν).val = M' := by
              rw [← hcore]; exact rFreeRoot_pow_mul_core 2 (by decide) Mp
            have hsq : Real.sqrt (M' : ℝ) = (k : ℝ) * Real.sqrt ((s ν).val : ℝ) := by
              rw [← hfac, Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _),
                  Real.sqrt_sq (Nat.cast_nonneg k)]
            have hk_ge : kStar ν ≤ k := by
              by_contra hlt
              have h0 := hkStar_min ν hk_pos (not_le.mp hlt)
              rw [← hsq] at h0
              exact hyU h0
            rw [hsq]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk_ge) (Real.sqrt_nonneg _)
          -- Value of `ψ (a ν) = (kStar ν : AsympCoeff)`!
          have hψ_a : ψ (a ν) = ((kStar ν : ℕ) : AsympCoeff) := by
            let Mp : ℕ+ := ⟨kStar ν ^ 2 * (s ν).val, Nat.mul_pos (pow_pos (hkStar_pos ν) 2) (rfree_pos (s ν).property)⟩
            have ha_eq : a ν = Real.sqrt (Mp.val : ℝ) := by
              change (kStar ν : ℝ) * Real.sqrt ((s ν).val : ℝ) = Real.sqrt ((kStar ν ^ 2 * (s ν).val : ℕ) : ℝ)
              rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _),
                  Real.sqrt_sq (Nat.cast_nonneg _)]
            rw [ha_eq, hψ_sqrt Mp]
            have huniq := rfree_factor_unique (r := 2) (by decide)
              (rFreeRoot_pos 2 (by decide) Mp) (hkStar_pos ν)
              (rFreeRoot_pow_mul_core 2 (by decide) Mp)
            simp [huniq.1, huniq.2]
          -- Extract each summand at `μ₀ + a ν` — unique antidiagonal pair `(μ₀, a ν)`!
          have hterm (j : Fin J) :
              (G (i, j) * hahnDeriv ψ (Y (i, j))).coeff (μ₀ + a ν) = M ν j * rvec j := by
            rw [HahnSeries.coeff_mul]
            have honly : ∀ pq ∈ Finset.antidiagonal (G (i, j)).isPWO_support
                (hahnDeriv ψ (Y (i, j))).isPWO_support (μ₀ + a ν), pq = (μ₀, a ν) := by
              rintro ⟨x, y⟩ hpq
              have ⟨hx, hy, hxy⟩ := Finset.mem_antidiagonal.mp hpq
              have hx_ge := hμ₀_le j x hx
              have hy_ge := hsupp_ge j y hy
              exact Prod.ext (by linarith) (by linarith)
            by_cases hmem : (μ₀, a ν) ∈ Finset.antidiagonal (G (i, j)).isPWO_support
                (hahnDeriv ψ (Y (i, j))).isPWO_support (μ₀ + a ν)
            · rw [Finset.sum_eq_single (μ₀, a ν)
                (fun pq hpq hne ↦ absurd (honly pq hpq) hne)
                (fun hnot ↦ absurd hmem hnot)]
              rw [hahnDeriv_coeff, hψ_a, mul_comm]
              rfl
            · have hemp : Finset.antidiagonal (G (i, j)).isPWO_support
                  (hahnDeriv ψ (Y (i, j))).isPWO_support (μ₀ + a ν) = ∅ := by
                rw [Finset.eq_empty_iff_forall_notMem]
                intro pq hpq
                exact hmem (honly pq hpq ▸ hpq)
              rw [hemp, Finset.sum_empty]
              rw [Finset.mem_antidiagonal] at hmem
              push Not at hmem
              by_cases hG0 : (G (i, j)).coeff μ₀ = 0
              · simp [rvec, hG0]
              · have hY0 : (hahnDeriv ψ (Y (i, j))).coeff (a ν) = 0 := by
                  by_contra hne
                  exact hmem hG0 hne rfl
                rw [hahnDeriv_coeff, hψ_a] at hY0
                simp [M, hY0]
          simp_rw [hterm] at hcoeff_sum
          simpa [Matrix.mulVec, dotProduct] using hcoeff_sum
        exact hr_ne (M.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero
          (mem_nonZeroDivisors_of_ne_zero hM_det) hMr)
    intro p
    exact hdown (m - 1 - p.1.val) p.1 rfl p.2
  -- Finish by strong induction on `P.totalDegree`.
  apply algebraicIndependent_iff.mpr
  intro P
  induction P using (measure fun P : MvPolynomial (Fin m × Fin J) AsympCoeff ↦ P.totalDegree).wf.induction with
  | h P ih =>
    intro hP
    have fromConst (hc : P = MvPolynomial.C (P.coeff 0)) : P = 0 := by
      have hh : HahnSeries.C (P.coeff 0) = (0 : TransSeries) := by
        have h1 : ev (MvPolynomial.C (P.coeff 0)) = 0 := hc ▸ hP
        simpa [ev, MvPolynomial.aeval_C, HahnSeries.algebraMap_apply] using h1
      have hc0 : P.coeff 0 = 0 := by
        have := congrArg (fun f : TransSeries ↦ f.coeff 0) hh
        simpa using this
      rw [hc, hc0, MvPolynomial.C_0]
    rcases Nat.eq_zero_or_pos P.totalDegree with he | he
    · exact fromConst (MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp he)
    · exact fromConst (eq_C_of_all_pderiv_zero P fun p ↦
        ih _ (lower_totalDegree_domain p P he) (hstable hP p))

/-- Helper: single-series specialization of `triangular_core_transseries_diff_indep`. -/
private theorem single_core_transseries_diff_indep (U : TransSeries)
    (hsupp : U.support ⊆ sqrtSpectrum)
    (hsep : {s : Core 2 | ∃ k : ℕ, 1 ≤ k ∧ U.coeff ((k : ℝ) * Real.sqrt (s.val : ℝ)) ≠ 0}.Infinite)
    (J : ℕ) :
    AlgebraicIndependent AsympCoeff (fun j : Fin J ↦ transDerivX^[j.val] U) := by
  have h1 := triangular_core_transseries_diff_indep (m := 1) (fun _ ↦ U) (fun _ ↦ hsupp)
    (fun i ↦ hsep.mono fun s hs ↦ ⟨fun i' hi' ↦ by omega, hs⟩) J
  let e : Fin J → Fin 1 × Fin J := fun j ↦ (0, j)
  exact h1.comp e (fun _ _ h ↦ congrArg Prod.snd h)

/-- Helper: lift `Fin m × Fin J` independence (for all `J`) to unbounded-order `Fin m × ℕ`. -/
private theorem lift_all_derivs_diff_indep {m : ℕ} (U : Fin m → TransSeries)
    (hJ : ∀ J : ℕ, AlgebraicIndependent AsympCoeff
      (fun p : Fin m × Fin J ↦ transDerivX^[p.2.val] (U p.1))) :
    AlgebraicIndependent AsympCoeff (fun p : Fin m × ℕ ↦ transDerivX^[p.2] (U p.1)) := by
  classical
  rw [algebraicIndependent_iff]
  intro P hP
  let J : ℕ := (P.vars.sup Prod.snd) + 1
  let emb : Fin m × Fin J → Fin m × ℕ := fun p ↦ (p.1, p.2.val)
  let proj : Fin m × ℕ → Fin m × Fin J := fun p ↦
    if h : p.2 < J then (p.1, ⟨p.2, h⟩) else (p.1, ⟨0, Nat.succ_pos _⟩)
  let Q : MvPolynomial (Fin m × Fin J) AsympCoeff := MvPolynomial.rename proj P
  have hQP : MvPolynomial.rename emb Q = P := by
    rw [MvPolynomial.rename_rename, MvPolynomial.rename_eq_aeval]
    have hcongr : ∀ u ∈ P.vars, emb (proj u) = u := by
      rintro ⟨i, n⟩ hu
      have hn : n < J := by
        have hle : n ≤ P.vars.sup Prod.snd := Finset.le_sup (f := Prod.snd) hu
        omega
      simp [emb, proj, hn]
    have h1 : MvPolynomial.aeval (MvPolynomial.X (R := AsympCoeff) ∘ (emb ∘ proj)) P =
        MvPolynomial.aeval (MvPolynomial.X (R := AsympCoeff)) P := by
      simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
      apply Finset.sum_congr rfl; intro mon hmon; congr 1
      apply Finsupp.prod_congr; intro u hu
      simp only [Function.comp_apply, hcongr u ((MvPolynomial.mem_vars_iff_mem_support u).mpr ⟨mon, hmon, hu⟩)]
    rw [h1]
    exact congrFun (congrArg DFunLike.coe (MvPolynomial.aeval_X_left (R := AsympCoeff) (σ := Fin m × ℕ))) P
  have hQ0 : MvPolynomial.aeval (fun p : Fin m × Fin J ↦ transDerivX^[p.2.val] (U p.1)) Q = 0 := by
    have heq : MvPolynomial.aeval (fun p : Fin m × ℕ ↦ transDerivX^[p.2] (U p.1)) (MvPolynomial.rename emb Q) =
        MvPolynomial.aeval (fun p : Fin m × Fin J ↦ transDerivX^[p.2.val] (U p.1)) Q := by
      rw [MvPolynomial.aeval_rename]; rfl
    rw [← heq, hQP, hP]
  have hQzero : Q = 0 := algebraicIndependent_iff.mp (hJ J) Q hQ0
  rw [← hQP, hQzero, map_zero]

/-- **Crown Jewel 1 — Physical 2D Blackbody Photon Gas Is Differentially Transcendental**:
`U_photon^{(2)}(t) = ∑_{n ∈ ℤ² \ {0}} |n| / (e^{|n| t} - 1)` has algebraically independent
derivatives of every order `J` over `AsympCoeff` (and hence satisfies NO polynomial ADE over `ℂ[t]`)! -/
theorem photon2D_non_ade (J : ℕ) :
    AlgebraicIndependent AsympCoeff (fun j : Fin J ↦ transDerivX^[j.val] photonEnergyTrans2D) := by
  refine single_core_transseries_diff_indep photonEnergyTrans2D (photonEnergyTrans_support_subset _) ?_ J
  refine Set.Infinite.mono (fun s hs ↦ ?_) infinite_prime_core_mod_four_eq_one
  rcases hs with ⟨hp, hmod⟩
  refine ⟨1, le_rfl, ?_⟩
  rw [Nat.cast_one, one_mul, photonEnergyTrans2D,
      photonEnergyTrans_coeff_sqrt r2Count (rfree_pos s.property)]
  have hpos := photonEnergyCoeff_pos_of_pos r2Count (rfree_pos s.property)
    (r2Count_pos_of_prime_mod_four_eq_one hp hmod)
  exact HahnSeries.C_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- **Crown Jewel 2 — Physical 3D Blackbody Photon Gas Is Differentially Transcendental**:
`U_photon^{(3)}(t) = ∑_{n ∈ ℤ³ \ {0}} |n| / (e^{|n| t} - 1)` has algebraically independent
derivatives of every order `J` over `AsympCoeff` (and hence satisfies NO polynomial ADE over `ℂ[t]`)! -/
theorem photon3D_non_ade (J : ℕ) :
    AlgebraicIndependent AsympCoeff (fun j : Fin J ↦ transDerivX^[j.val] photonEnergyTrans3D) := by
  refine single_core_transseries_diff_indep photonEnergyTrans3D (photonEnergyTrans_support_subset _) ?_ J
  refine Set.Infinite.mono (fun s hs ↦ ?_) infinite_prime_core_mod_four_eq_one
  rcases hs with ⟨hp, hmod⟩
  refine ⟨1, le_rfl, ?_⟩
  rw [Nat.cast_one, one_mul, photonEnergyTrans3D,
      photonEnergyTrans_coeff_sqrt r3Count (rfree_pos s.property)]
  have hpos := photonEnergyCoeff_pos_of_pos r3Count (rfree_pos s.property)
    (r3Count_pos_of_prime_mod_four_eq_one hp hmod)
  exact HahnSeries.C_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- **Crown Jewel 3 — Physical 4D Blackbody Photon Gas Is Differentially Transcendental**:
`U_photon^{(4)}(t) = ∑_{n ∈ ℤ⁴ \ {0}} |n| / (e^{|n| t} - 1)` has algebraically independent
derivatives of every order `J` over `AsympCoeff` (and hence satisfies NO polynomial ADE over `ℂ[t]`)! -/
theorem photon4D_non_ade (J : ℕ) :
    AlgebraicIndependent AsympCoeff (fun j : Fin J ↦ transDerivX^[j.val] photonEnergyTrans4D) := by
  refine single_core_transseries_diff_indep photonEnergyTrans4D (photonEnergyTrans_support_subset _) ?_ J
  refine Set.Infinite.mono (fun s _ ↦ ?_) infinite_prime_core_mod_eight_eq_seven
  refine ⟨1, le_rfl, ?_⟩
  rw [Nat.cast_one, one_mul, photonEnergyTrans4D,
      photonEnergyTrans_coeff_sqrt r4Count (rfree_pos s.property)]
  have hpos := photonEnergyCoeff_pos_of_pos r4Count (rfree_pos s.property) (r4Count_pos s.val)
  exact HahnSeries.C_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- Helper: `photonEnergyTrans r` vanishes on `(k : ℝ) * √s` whenever `r(m² s) = 0` for all `m ≥ 1`. -/
private lemma photonEnergyTrans_coeff_mul_sqrt_eq_zero (r : ℕ → ℕ) {s : Core 2}
    (hzero : ∀ m : ℕ, 1 ≤ m → r (m ^ 2 * s.val) = 0) {k : ℕ} (hk : 1 ≤ k) :
    (photonEnergyTrans r).coeff ((k : ℝ) * Real.sqrt (s.val : ℝ)) = 0 := by
  have hsq : (k : ℝ) * Real.sqrt (s.val : ℝ) = Real.sqrt ((k ^ 2 * s.val : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg k)]
  rw [hsq, photonEnergyTrans_coeff_sqrt r (Nat.mul_pos (pow_pos hk 2) (rfree_pos s.property)),
      photonEnergyCoeff_sq_mul_eq_zero_of_all_zero r hzero hk, Complex.ofReal_zero, map_zero]

/-- Helper: `photonLogZTrans r` vanishes on `(k : ℝ) * √s` whenever `r(m² s) = 0` for all `m ≥ 1`. -/
private lemma photonLogZTrans_coeff_mul_sqrt_eq_zero (r : ℕ → ℕ) {s : Core 2}
    (hzero : ∀ m : ℕ, 1 ≤ m → r (m ^ 2 * s.val) = 0) {k : ℕ} (hk : 1 ≤ k) :
    (photonLogZTrans r).coeff ((k : ℝ) * Real.sqrt (s.val : ℝ)) = 0 := by
  have hsq : (k : ℝ) * Real.sqrt (s.val : ℝ) = Real.sqrt ((k ^ 2 * s.val : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg k)]
  rw [hsq, photonLogZTrans_coeff_sqrt r (Nat.mul_pos (pow_pos hk 2) (rfree_pos s.property)),
      photonLogZCoeff_sq_mul_eq_zero_of_all_zero r hzero hk, Complex.ofReal_zero, map_zero]

/-- The 3-tuple `(U_photon^{(2)}, U_photon^{(3)}, U_photon^{(4)})` of physical 2D, 3D, and 4D
relativistic blackbody photon gas internal energies. -/
def photonGasFamily : Fin 3 → TransSeries :=
  ![photonEnergyTrans2D, photonEnergyTrans3D, photonEnergyTrans4D]

/-- **Crown Jewel 4 — Joint Differential Independence of `{2D, 3D, 4D}` Relativistic Blackbody Photon Gases**:
For EVERY order `J : ℕ`, the combined `3 J`-tuple of derivatives of `(U_photon^{(2)}, U_photon^{(3)},
U_photon^{(4)})` is **jointly algebraically independent over `AsympCoeff`**!
Proved 100% unconditionally via 3-class arithmetic separation:
- `2D` (`p ≡ 1 mod 4`, Fermat two-square theorem),
- `3D` vs `2D` (`s ≡ 3 mod 8` from `Q² + 2 = 1² + 1² + Q²`, zero Legendre 3-square theorem needed!),
- `4D` vs `{2D, 3D}` (`p ≡ 7 mod 8`, Lagrange four-square theorem)! -/
theorem photon2D_photon3D_photon4D_joint_diff_indep (J : ℕ) :
    AlgebraicIndependent AsympCoeff
      (fun p : Fin 3 × Fin J ↦ transDerivX^[p.2.val] (photonGasFamily p.1)) := by
  refine triangular_core_transseries_diff_indep photonGasFamily ?_ ?_ J
  · intro i
    fin_cases i
    · exact photonEnergyTrans_support_subset r2Count
    · exact photonEnergyTrans_support_subset r3Count
    · exact photonEnergyTrans_support_subset r4Count
  · intro i
    fin_cases i
    · -- `i = 0` (2D): primes `p ≡ 1 (mod 4)`
      refine Set.Infinite.mono (fun s hs ↦ ?_) infinite_prime_core_mod_four_eq_one
      rcases hs with ⟨hp, hmod⟩
      refine ⟨fun i' hi' ↦ by
        have hlt0 : i'.val < 0 := hi'
        omega, ⟨1, le_rfl, ?_⟩⟩
      change (photonEnergyTrans2D).coeff ((1 : ℕ) * Real.sqrt (s.val : ℝ)) ≠ 0
      rw [Nat.cast_one, one_mul, photonEnergyTrans2D,
          photonEnergyTrans_coeff_sqrt r2Count (rfree_pos s.property)]
      have hpos := photonEnergyCoeff_pos_of_pos r2Count (rfree_pos s.property)
        (r2Count_pos_of_prime_mod_four_eq_one hp hmod)
      exact HahnSeries.C_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')
    · -- `i = 1` (3D vs 2D): constructive square-free cores `s ≡ 3 (mod 8)` from `Q² + 2`
      refine Set.Infinite.mono (fun s hs ↦ ?_) infinite_sqf_mod_eight_eq_three_r3_pos
      rcases hs with ⟨hs8, k, hk1, hr3⟩
      have hs4 : s.val % 4 = 3 := by omega
      refine ⟨fun i' hi' m hm ↦ ?_, ⟨k, hk1, ?_⟩⟩
      · have hi0 : i' = 0 := Fin.ext (by change i'.val < 1 at hi'; omega)
        subst hi0
        exact photonEnergyTrans_coeff_mul_sqrt_eq_zero r2Count
          (fun d hd ↦ r2Count_sq_mul_eq_zero_of_mod_four_eq_three hs4 hd) hm
      · change (photonEnergyTrans3D).coeff ((k : ℝ) * Real.sqrt (s.val : ℝ)) ≠ 0
        have hsq : (k : ℝ) * Real.sqrt (s.val : ℝ) = Real.sqrt ((k ^ 2 * s.val : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg k)]
        rw [hsq, photonEnergyTrans3D,
            photonEnergyTrans_coeff_sqrt r3Count (Nat.mul_pos (pow_pos hk1 2) (rfree_pos s.property))]
        have hpos := photonEnergyCoeff_pos_of_pos r3Count
          (Nat.mul_pos (pow_pos hk1 2) (rfree_pos s.property)) hr3
        exact HahnSeries.C_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')
    · -- `i = 2` (4D vs {2D, 3D}): primes `p ≡ 7 (mod 8)`
      refine Set.Infinite.mono (fun s hs ↦ ?_) infinite_prime_core_mod_eight_eq_seven
      rcases hs with ⟨hp, hp7⟩
      have hp3 : s.val % 4 = 3 := by omega
      refine ⟨fun i' hi' m hm ↦ ?_, ⟨1, le_rfl, ?_⟩⟩
      · have hcases : i' = 0 ∨ i' = 1 := by
          have hlt2 : i'.val < 2 := hi'
          have hor : i'.val = 0 ∨ i'.val = 1 := by omega
          rcases hor with h0 | h1
          · exact Or.inl (Fin.ext h0)
          · exact Or.inr (Fin.ext h1)
        rcases hcases with rfl | rfl
        · exact photonEnergyTrans_coeff_mul_sqrt_eq_zero r2Count
            (fun d hd ↦ r2Count_sq_mul_eq_zero_of_prime_mod_four_eq_three hp hp3 hd) hm
        · exact photonEnergyTrans_coeff_mul_sqrt_eq_zero r3Count
            (fun d hd ↦ r3Count_sq_mul_eq_zero_of_prime_mod_eight_eq_seven hp hp7 hd) hm
      · change (photonEnergyTrans4D).coeff ((1 : ℕ) * Real.sqrt (s.val : ℝ)) ≠ 0
        rw [Nat.cast_one, one_mul, photonEnergyTrans4D,
            photonEnergyTrans_coeff_sqrt r4Count (rfree_pos s.property)]
        have hpos := photonEnergyCoeff_pos_of_pos r4Count (rfree_pos s.property) (r4Count_pos s.val)
        exact HahnSeries.C_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')

/-- Unbounded-order corollary: ALL derivatives `(i, j) ∈ Fin 3 × ℕ` of
`(U_photon^{(2)}, U_photon^{(3)}, U_photon^{(4)})` are jointly algebraically independent over
`AsympCoeff`. -/
theorem photon2D_photon3D_photon4D_all_derivs_diff_indep :
    AlgebraicIndependent AsympCoeff
      (fun p : Fin 3 × ℕ ↦ transDerivX^[p.2] (photonGasFamily p.1)) :=
  lift_all_derivs_diff_indep photonGasFamily photon2D_photon3D_photon4D_joint_diff_indep

/-- Non-autonomous polynomial-ADE corollary over `ℂ[t]`: NO nonzero polynomial
`P(t; (U_D^{(j)})) ∈ ℂ[t][Z_{D, j}]` vanishes on `(U_photon^{(2)}, U_photon^{(3)}, U_photon^{(4)})`! -/
theorem photon2D_photon3D_photon4D_no_joint_poly_ade (J : ℕ)
    (P : MvPolynomial (Fin 3 × Fin J) (Polynomial ℂ))
    (hP : MvPolynomial.aeval (fun p : Fin 3 × Fin J ↦ transDerivX^[p.2.val] (photonGasFamily p.1))
      (MvPolynomial.map polyToAsymp P) = 0) :
    P = 0 := by
  have hind := photon2D_photon3D_photon4D_joint_diff_indep J
  have hmap0 : MvPolynomial.map polyToAsymp P = 0 :=
    algebraicIndependent_iff.mp hind (MvPolynomial.map polyToAsymp P) hP
  exact MvPolynomial.map_injective polyToAsymp polyToAsymp_injective
    (hmap0.trans (map_zero _).symm)

/-- The 3-tuple `(log Z_photon^{(2)}, log Z_photon^{(3)}, log Z_photon^{(4)})` of physical 2D, 3D,
and 4D relativistic blackbody photon gas grand potentials. -/
def photonLogZFamily : Fin 3 → TransSeries :=
  ![photonLogZTrans2D, photonLogZTrans3D, photonLogZTrans4D]

/-- **Grand Potential Joint Differential Independence**:
`(log Z_photon^{(2)}, log Z_photon^{(3)}, log Z_photon^{(4)})` are jointly differentially
independent over `AsympCoeff` for every order `J` (and hence over `ℂ[t]`). -/
theorem photonLogZ_2D_3D_4D_joint_diff_indep (J : ℕ) :
    AlgebraicIndependent AsympCoeff
      (fun p : Fin 3 × Fin J ↦ transDerivX^[p.2.val] (photonLogZFamily p.1)) := by
  refine triangular_core_transseries_diff_indep photonLogZFamily ?_ ?_ J
  · intro i
    fin_cases i
    · exact photonLogZTrans_support_subset r2Count
    · exact photonLogZTrans_support_subset r3Count
    · exact photonLogZTrans_support_subset r4Count
  · intro i
    fin_cases i
    · refine Set.Infinite.mono (fun s hs ↦ ?_) infinite_prime_core_mod_four_eq_one
      rcases hs with ⟨hp, hmod⟩
      refine ⟨fun i' hi' ↦ by
        have hlt0 : i'.val < 0 := hi'
        omega, ⟨1, le_rfl, ?_⟩⟩
      change (photonLogZTrans2D).coeff ((1 : ℕ) * Real.sqrt (s.val : ℝ)) ≠ 0
      rw [Nat.cast_one, one_mul, photonLogZTrans2D,
          photonLogZTrans_coeff_sqrt r2Count (rfree_pos s.property)]
      have hpos := photonLogZCoeff_pos_of_pos r2Count (rfree_pos s.property)
        (r2Count_pos_of_prime_mod_four_eq_one hp hmod)
      exact HahnSeries.C_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')
    · refine Set.Infinite.mono (fun s hs ↦ ?_) infinite_sqf_mod_eight_eq_three_r3_pos
      rcases hs with ⟨hs8, k, hk1, hr3⟩
      have hs4 : s.val % 4 = 3 := by omega
      refine ⟨fun i' hi' m hm ↦ ?_, ⟨k, hk1, ?_⟩⟩
      · have hi0 : i' = 0 := Fin.ext (by change i'.val < 1 at hi'; omega)
        subst hi0
        exact photonLogZTrans_coeff_mul_sqrt_eq_zero r2Count
          (fun d hd ↦ r2Count_sq_mul_eq_zero_of_mod_four_eq_three hs4 hd) hm
      · change (photonLogZTrans3D).coeff ((k : ℝ) * Real.sqrt (s.val : ℝ)) ≠ 0
        have hsq : (k : ℝ) * Real.sqrt (s.val : ℝ) = Real.sqrt ((k ^ 2 * s.val : ℕ) : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg k)]
        rw [hsq, photonLogZTrans3D,
            photonLogZTrans_coeff_sqrt r3Count (Nat.mul_pos (pow_pos hk1 2) (rfree_pos s.property))]
        have hpos := photonLogZCoeff_pos_of_pos r3Count
          (Nat.mul_pos (pow_pos hk1 2) (rfree_pos s.property)) hr3
        exact HahnSeries.C_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')
    · refine Set.Infinite.mono (fun s hs ↦ ?_) infinite_prime_core_mod_eight_eq_seven
      rcases hs with ⟨hp, hp7⟩
      have hp3 : s.val % 4 = 3 := by omega
      refine ⟨fun i' hi' m hm ↦ ?_, ⟨1, le_rfl, ?_⟩⟩
      · have hcases : i' = 0 ∨ i' = 1 := by
          have hlt2 : i'.val < 2 := hi'
          have hor : i'.val = 0 ∨ i'.val = 1 := by omega
          rcases hor with h0 | h1
          · exact Or.inl (Fin.ext h0)
          · exact Or.inr (Fin.ext h1)
        rcases hcases with rfl | rfl
        · exact photonLogZTrans_coeff_mul_sqrt_eq_zero r2Count
            (fun d hd ↦ r2Count_sq_mul_eq_zero_of_prime_mod_four_eq_three hp hp3 hd) hm
        · exact photonLogZTrans_coeff_mul_sqrt_eq_zero r3Count
            (fun d hd ↦ r3Count_sq_mul_eq_zero_of_prime_mod_eight_eq_seven hp hp7 hd) hm
      · change (photonLogZTrans4D).coeff ((1 : ℕ) * Real.sqrt (s.val : ℝ)) ≠ 0
        rw [Nat.cast_one, one_mul, photonLogZTrans4D,
            photonLogZTrans_coeff_sqrt r4Count (rfree_pos s.property)]
        have hpos := photonLogZCoeff_pos_of_pos r4Count (rfree_pos s.property) (r4Count_pos s.val)
        exact HahnSeries.C_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne')

end
end CubicTheta.AllD
