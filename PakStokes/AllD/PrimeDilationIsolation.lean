module

public import PakStokes.AllD.MockModularAlgebraCore
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Tactic

/-! # Prime-Frequency Dilation Isolation & Dual-Ray Block Elimination

Unconditional Lean 4 formalization from Mathlib (zero placeholders, standard assumptions only)
of the Appendix A Prime-Frequency Dilation Isolation Theorem for mock-modular and false-theta
families across arbitrary finite sets of positive integer dilations:

1. **Exact Prime-Square Dilation Isolation** (`no_sq_mul_eq_prime_sq_mul_of_gt`,
   `no_nat_eq_prime_mul_sqrt_ratio`, `prime_dilation_freq_ne`):
   For any prime `p` and integers `0 < d' < d < p`, there is NO integer `k` with
   `k^2 * d = p^2 * d'`, equivalently `p * √(d' / d)` is never an integer and `A_k / d' ≠ A_p / d`
   for any quadratic frequency ladder `A_m = c * m^2` (`c ≠ 0`).
2. **Non-Vanishing Mock/False-Theta Residue Factor** (`prime_mod_six_of_gt_three`,
   `mockFalse_sine_factor_eq`, `mockFalse_sine_factor_ne_zero`):
   Every prime `p > 3` satisfies `p % 6 = 1 ∨ p % 6 = 5` and
   `Real.sin (Real.pi * p / 3) = ± √3 / 2 ≠ 0`.
3. **Arbitrarily Many Strictly Increasing Isolated Primes**
   (`exists_isolated_primes_for_max_dilation`):
   For any finite nonempty set `D : Finset ℕ` of positive integers with maximum `d = D.max' hne`
   and any order `r : ℕ`, there exist `r + 1` strictly increasing primes `p_0 < ... < p_r`
   with `p_i > max 3 d`, `Real.sin (Real.pi * p_i / 3) ≠ 0`, and complete isolation of block `d`
   from every strictly smaller dilation `d' ∈ D`.
4. **Prime-Frequency Mock-Modular Jet Vandermonde Nonsingularity**
   (`prime_dilation_jet_det_ne_zero`, `prime_dilation_jet_eval_det_ne_zero`,
   `prime_dilation_weighted_jet_det_ne_zero`):
   Combining isolated primes with `mockModular_jet_det_eq` from `MockModularAlgebraCore`, the
   `(r + 1) × (r + 1)` mock-modular jet matrix at frequencies `ω_s = c * p_s^2 / d` has nonzero
   polynomial determinant `X^(r*(r+1)) * ∏_{a < b} (c / d) * (p_b^2 - p_a^2) ≠ 0` in `ℂ[X]` and
   nonzero scalar determinant at every `x ∈ ℂ \ {0}` (even after multiplying rows by arbitrary
   nonzero residue amplitudes such as `sin(π p_s / 3)`).
5. **Descending Block-Elimination & Dual-Ray Mock/False-Theta Joint Elimination**
   (`prime_dilation_block_elimination`, `dual_ray_prime_dilation_elimination`,
   `dual_ray_prime_dilation_constant`):
   Strong descending induction from `D.max'` eliminates all partial derivatives `∂_{d, j} R = 0`
   across every dilation `d ∈ D` and every derivative order `j ≤ r`; applying the same
   elimination on both positive (`+c`) and negative (`-c`) Stokes rays eliminates all joint jet
   variables even when `D_+ = D_-`, forcing `R` to depend only on the base variable `x`.
-/

namespace CubicTheta.AllD

public section

open Real Finset Matrix

/-! ### 1. Exact Prime-Square Dilation Isolation -/

/-- **Prime-Square Dilation Isolation (`ℕ` form):**
For any prime `p` and integers `0 < d' < d < p`, no natural number `k` satisfies
`k^2 * d = p^2 * d'`. -/
theorem no_sq_mul_eq_prime_sq_mul_of_gt {p d d' : ℕ}
    (hp : Nat.Prime p) (hd' : 0 < d') (hd'd : d' < d) (hdp : d < p) (k : ℕ) :
    k ^ 2 * d ≠ p ^ 2 * d' := by
  intro heq
  have hp_dvd_prod : p ∣ k ^ 2 * d := by
    refine ⟨p * d', ?_⟩
    linarith [heq]
  have hp_not_dvd_d : ¬ p ∣ d := Nat.not_dvd_of_pos_of_lt (lt_trans hd' hd'd) hdp
  have hp_dvd_ksq : p ∣ k ^ 2 := (hp.dvd_mul.mp hp_dvd_prod).resolve_right hp_not_dvd_d
  have hp_dvd_k : p ∣ k := hp.dvd_of_dvd_pow hp_dvd_ksq
  rcases hp_dvd_k with ⟨m, rfl⟩
  have hcancel : p ^ 2 * (m ^ 2 * d) = p ^ 2 * d' := by
    calc
      p ^ 2 * (m ^ 2 * d) = (p * m) ^ 2 * d := by ring
      _ = p ^ 2 * d' := heq
  have hp2_pos : 0 < p ^ 2 := pow_pos hp.pos 2
  have hmd : m ^ 2 * d = d' := Nat.eq_of_mul_eq_mul_left hp2_pos hcancel
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · simp at hmd
    omega
  · have hm2 : 1 ≤ m ^ 2 := Nat.one_le_pow 2 m hm_pos
    have hge : d ≤ m ^ 2 * d := by nlinarith
    omega

/-- Signed integer version of prime-square dilation isolation: no `k : ℤ` satisfies
`k^2 * d = p^2 * d'`. -/
theorem no_int_sq_mul_eq_prime_sq_mul_of_gt {p d d' : ℕ}
    (hp : Nat.Prime p) (hd' : 0 < d') (hd'd : d' < d) (hdp : d < p) (k : ℤ) :
    k ^ 2 * (d : ℤ) ≠ (p : ℤ) ^ 2 * (d' : ℤ) := by
  intro heq
  have hnat : k.natAbs ^ 2 * d = p ^ 2 * d' := by
    have hcast : ((k.natAbs ^ 2 * d : ℕ) : ℤ) = ((p ^ 2 * d' : ℕ) : ℤ) := by
      push_cast
      rw [sq_abs]
      exact heq
    exact Int.ofNat.inj hcast
  exact no_sq_mul_eq_prime_sq_mul_of_gt hp hd' hd'd hdp k.natAbs hnat

/-- Real square-root formulation: `p * √(d' / d)` is never a natural number when
`0 < d' < d < p` and `p` is prime. -/
theorem no_nat_eq_prime_mul_sqrt_ratio {p d d' : ℕ}
    (hp : Nat.Prime p) (hd' : 0 < d') (hd'd : d' < d) (hdp : d < p) (k : ℕ) :
    (k : ℝ) ≠ (p : ℝ) * Real.sqrt ((d' : ℝ) / (d : ℝ)) := by
  intro heq
  have hd_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (lt_trans hd' hd'd)
  have hratio_nn : 0 ≤ (d' : ℝ) / (d : ℝ) := by positivity
  have hsq : (k : ℝ) ^ 2 = (p : ℝ) ^ 2 * ((d' : ℝ) / (d : ℝ)) := by
    calc
      (k : ℝ) ^ 2 = ((p : ℝ) * Real.sqrt ((d' : ℝ) / (d : ℝ))) ^ 2 := by rw [heq]
      _ = (p : ℝ) ^ 2 * (Real.sqrt ((d' : ℝ) / (d : ℝ))) ^ 2 := by ring
      _ = (p : ℝ) ^ 2 * ((d' : ℝ) / (d : ℝ)) := by rw [Real.sq_sqrt hratio_nn]
  have hmul : (k : ℝ) ^ 2 * (d : ℝ) = (p : ℝ) ^ 2 * (d' : ℝ) := by
    have hd_ne : (d : ℝ) ≠ 0 := ne_of_gt hd_pos
    field_simp [hd_ne] at hsq
    linarith
  have hnat : k ^ 2 * d = p ^ 2 * d' := by exact_mod_cast hmul
  exact no_sq_mul_eq_prime_sq_mul_of_gt hp hd' hd'd hdp k hnat

/-- Quadratic frequency isolation over any field `K` of characteristic zero (such as `ℝ` or `ℂ`):
for any nonzero scale `c`, `c * k^2 / d' ≠ c * p^2 / d` whenever `0 < d' < d < p` and `p` is prime. -/
theorem prime_dilation_freq_ne {K : Type*} [Field K] [CharZero K] {p d d' : ℕ}
    (hp : Nat.Prime p) (hd' : 0 < d') (hd'd : d' < d) (hdp : d < p)
    {c : K} (hc : c ≠ 0) (k : ℕ) :
    c * (k : K) ^ 2 / (d' : K) ≠ c * (p : K) ^ 2 / (d : K) := by
  intro heq
  have hd'_ne : (d' : K) ≠ 0 := Nat.cast_ne_zero.mpr hd'.ne'
  have hd_ne : (d : K) ≠ 0 := Nat.cast_ne_zero.mpr (lt_trans hd' hd'd).ne'
  have hcancel : (k : K) ^ 2 / (d' : K) = (p : K) ^ 2 / (d : K) := by
    apply mul_left_cancel₀ hc
    simpa [mul_div_assoc] using heq
  have hcross : (k : K) ^ 2 * (d : K) = (p : K) ^ 2 * (d' : K) := by
    field_simp [hd'_ne, hd_ne] at hcancel
    rw [mul_comm (d' : K)] at hcancel
    exact hcancel
  have hnat : k ^ 2 * d = p ^ 2 * d' := by exact_mod_cast hcross
  exact no_sq_mul_eq_prime_sq_mul_of_gt hp hd' hd'd hdp k hnat

/-! ### 2. Residue Congruence Modulo `6` & Non-Vanishing Sine Factor for Primes `p > 3` -/

/-- Every prime `p > 3` satisfies `p % 6 = 1` or `p % 6 = 5`. -/
theorem prime_mod_six_of_gt_three {p : ℕ} (hp : Nat.Prime p) (hgt : 3 < p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ 2 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h
    omega
  have h3 : ¬ 3 ∣ p := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h
    omega
  omega

/-- Exact value of the mock/false-theta sine factor `\sin(\pi p / 3)` for every prime `p > 3`:
it equals `√3 / 2` when `p ≡ 1 (mod 6)` and `-√3 / 2` when `p ≡ 5 (mod 6)`. -/
theorem mockFalse_sine_factor_eq {p : ℕ} (hp : Nat.Prime p) (hgt : 3 < p) :
    Real.sin (Real.pi * (p : ℝ) / 3) =
      if p % 6 = 1 then Real.sqrt 3 / 2 else -(Real.sqrt 3 / 2) := by
  rcases prime_mod_six_of_gt_three hp hgt with h1 | h5
  · simp only [h1, ↓reduceIte]
    set q := p / 6
    have hp_eq : p = 6 * q + 1 := by omega
    have harg : Real.pi * (p : ℝ) / 3 =
        Real.pi / 3 + (q : ℝ) * (2 * Real.pi) := by
      rw [hp_eq]; push_cast; ring
    rw [harg, Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_three]
  · have hne1 : p % 6 ≠ 1 := by omega
    simp only [hne1, ↓reduceIte]
    set q := p / 6
    have hp_eq : p = 6 * q + 5 := by omega
    have harg : Real.pi * (p : ℝ) / 3 =
        (-(Real.pi / 3)) + (((q + 1 : ℕ) : ℝ)) * (2 * Real.pi) := by
      rw [hp_eq]; push_cast; ring
    rw [harg, Real.sin_add_nat_mul_two_pi, Real.sin_neg, Real.sin_pi_div_three]

/-- For every prime `p > 3`, `Real.sin (Real.pi * p / 3) ≠ 0`. -/
theorem mockFalse_sine_factor_ne_zero {p : ℕ} (hp : Nat.Prime p) (hgt : 3 < p) :
    Real.sin (Real.pi * (p : ℝ) / 3) ≠ 0 := by
  rw [mockFalse_sine_factor_eq hp hgt]
  have hpos : 0 < Real.sqrt 3 / 2 := by positivity
  split_ifs
  · exact ne_of_gt hpos
  · exact neg_ne_zero.mpr (ne_of_gt hpos)

/-! ### 3. Existence of Arbitrarily Many Strictly Increasing Isolated Primes -/

/-- For any bound `B` and length `r`, there exist `r + 1` strictly increasing primes all
strictly greater than `B`. -/
theorem exists_strictMono_primes_gt (B r : ℕ) :
    ∃ p : Fin (r + 1) → ℕ, StrictMono p ∧ (∀ i, Nat.Prime (p i)) ∧ (∀ i, B < p i) := by
  induction r with
  | zero =>
    obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (B + 1)
    refine ⟨fun _ ↦ q, ?_, fun _ ↦ hq_prime, fun _ ↦ by dsimp only; omega⟩
    intro a b hab
    have : a = b := Fin.ext (by omega)
    exact absurd (this ▸ hab) (lt_irrefl _)
  | succ r ih =>
    obtain ⟨p, hmono, hprime, hgt⟩ := ih
    let last : ℕ := p (Fin.last r)
    obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (max B last + 1)
    let p' : Fin (r + 2) → ℕ := Fin.snoc p q
    have hq_gt_last : last < q := by omega
    have hq_gt_B : B < q := by omega
    have hmono' : StrictMono p' := by
      intro a b
      refine Fin.lastCases ?_ (fun b' ↦ ?_) b
      · refine Fin.lastCases ?_ (fun a' ↦ ?_) a
        · intro hab; exact absurd hab (lt_irrefl _)
        · intro _
          simp only [p', Fin.snoc_castSucc, Fin.snoc_last]
          have hle : p a' ≤ last := by
            rcases eq_or_lt_of_le (Fin.le_last a') with h | h
            · simp [last, h]
            · exact le_of_lt (hmono h)
          omega
      · refine Fin.lastCases ?_ (fun a' ↦ ?_) a
        · intro hab; exact absurd hab (not_lt_of_ge (Fin.le_last _))
        · intro hab
          simp only [p', Fin.snoc_castSucc]
          exact hmono (Fin.castSucc_lt_castSucc_iff.mp hab)
    have hprime' : ∀ i, Nat.Prime (p' i) := by
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa [p'] using hq_prime
      · simpa [p'] using hprime j
    have hgt' : ∀ i, B < p' i := by
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa [p'] using hq_gt_B
      · simpa [p'] using hgt j
    exact ⟨p', hmono', hprime', hgt'⟩

/-- **Paper #10 Appendix A Prime Isolation Lemma (`exists_isolated_primes_for_max_dilation`):**
For any finite nonempty set `D : Finset ℕ` of positive integers with maximum `d = D.max' hne`
and any order `r : ℕ`, there exist `r + 1` strictly increasing primes `p_0 < ... < p_r` such that:
1. `3 < p i` and `d < p i` for every `i : Fin (r + 1)`,
2. `p i % 6 = 1 ∨ p i % 6 = 5` and `Real.sin (Real.pi * p i / 3) ≠ 0`,
3. for every `d' ∈ D` with `d' < d` and every `k : ℕ`, `k^2 * d ≠ (p i)^2 * d'`. -/
theorem exists_isolated_primes_for_max_dilation (D : Finset ℕ) (hD_pos : ∀ d' ∈ D, 0 < d')
    (hne : D.Nonempty) (r : ℕ) :
    let d := D.max' hne
    ∃ p : Fin (r + 1) → ℕ,
      StrictMono p ∧
      (∀ i, Nat.Prime (p i)) ∧
      (∀ i, 3 < p i ∧ d < p i) ∧
      (∀ i, p i % 6 = 1 ∨ p i % 6 = 5) ∧
      (∀ i, Real.sin (Real.pi * (p i : ℝ) / 3) ≠ 0) ∧
      (∀ i, ∀ d' ∈ D, d' < d → ∀ k : ℕ, k ^ 2 * d ≠ (p i) ^ 2 * d') := by
  dsimp only
  set d := D.max' hne
  obtain ⟨p, hmono, hprime, hgt⟩ := exists_strictMono_primes_gt (max 3 d) r
  refine ⟨p, hmono, hprime, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi := hgt i
    exact ⟨lt_of_le_of_lt (le_max_left 3 d) hi, lt_of_le_of_lt (le_max_right 3 d) hi⟩
  · intro i
    exact prime_mod_six_of_gt_three (hprime i) (lt_of_le_of_lt (le_max_left 3 d) (hgt i))
  · intro i
    exact mockFalse_sine_factor_ne_zero (hprime i) (lt_of_le_of_lt (le_max_left 3 d) (hgt i))
  · intro i d' hd' hlt k
    exact no_sq_mul_eq_prime_sq_mul_of_gt (hprime i) (hD_pos d' hd') hlt
      (lt_of_le_of_lt (le_max_right 3 d) (hgt i)) k

/-! ### 4. Mock-Modular Jet Vandermonde Nonsingularity at Isolated Prime Frequencies -/

/-- Prime frequency tuple `ω_s = c * p_s^2 / d` is injective whenever `p` is strictly increasing,
`c ≠ 0`, and `d > 0`. -/
theorem prime_freq_injective {r d : ℕ} (hd : 0 < d) {c : ℂ} (hc : c ≠ 0)
    {p : Fin (r + 1) → ℕ} (hmono : StrictMono p) :
    Function.Injective (fun s : Fin (r + 1) ↦ c * ((p s : ℂ) ^ 2) / (d : ℂ)) := by
  intro a b hab
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hsqC : ((p a : ℂ) ^ 2) = ((p b : ℂ) ^ 2) := by
    have := congrArg (· * (d : ℂ)) hab
    field_simp [hd_ne, hc] at this
    exact this
  have hsq : (p a) ^ 2 = (p b) ^ 2 := by exact_mod_cast hsqC
  have hp_eq : p a = p b := by nlinarith
  exact hmono.injective hp_eq

/-- **Symbolic Mock-Modular Jet Determinant Non-Vanishing at Prime Frequencies:**
For any weight `k : ℂ`, order `r : ℕ`, dilation `d > 0`, nonzero scale `c : ℂ`, and strictly
increasing sequence `p : Fin (r + 1) → ℕ`, the `(r + 1) × (r + 1)` jet matrix
`mockJetP k r j (c * p_s^2 / d)` has nonzero determinant in `Polynomial ℂ`. -/
theorem prime_dilation_jet_det_ne_zero (k : ℂ) (r : ℕ) {d : ℕ} (hd : 0 < d)
    {c : ℂ} (hc : c ≠ 0) {p : Fin (r + 1) → ℕ} (hmono : StrictMono p) :
    Matrix.det (Matrix.of fun s j : Fin (r + 1) ↦
      mockJetP k r j.1 (c * ((p s : ℂ) ^ 2) / (d : ℂ))) ≠ 0 := by
  let ω : Fin (r + 1) → ℂ := fun s ↦ c * ((p s : ℂ) ^ 2) / (d : ℂ)
  change Matrix.det (Matrix.of fun s j : Fin (r + 1) ↦ mockJetP k r j.1 (ω s)) ≠ 0
  rw [mockModular_jet_det_eq]
  have hX : (Polynomial.X : Polynomial ℂ) ^ (r * (r + 1)) ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hinj : Function.Injective ω := prime_freq_injective hd hc hmono
  have hprod : Polynomial.C (∏ a : Fin (r + 1), ∏ b ∈ Finset.Ioi a, (ω b - ω a)) ≠ 0 := by
    refine Polynomial.C_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ ↦
      Finset.prod_ne_zero_iff.mpr fun b hb ↦ ?_)
    have hab : a < b := Finset.mem_Ioi.mp hb
    exact sub_ne_zero.mpr (fun h ↦ hab.ne' (hinj h))
  exact mul_ne_zero hX hprod

/-- **Pointwise Complex Mock-Modular Jet Determinant Non-Vanishing** at every `x ∈ ℂ \ {0}`. -/
theorem prime_dilation_jet_eval_det_ne_zero (k : ℂ) (r : ℕ) {d : ℕ} (hd : 0 < d)
    {c x : ℂ} (hc : c ≠ 0) (hx : x ≠ 0) {p : Fin (r + 1) → ℕ} (hmono : StrictMono p) :
    Matrix.det (Matrix.of fun s j : Fin (r + 1) ↦
      (mockJetP k r j.1 (c * ((p s : ℂ) ^ 2) / (d : ℂ))).eval x) ≠ 0 := by
  let ω : Fin (r + 1) → ℂ := fun s ↦ c * ((p s : ℂ) ^ 2) / (d : ℂ)
  have hmap : (Matrix.of fun s j : Fin (r + 1) ↦ (mockJetP k r j.1 (ω s)).eval x) =
      (Polynomial.evalRingHom x).mapMatrix (Matrix.of fun s j : Fin (r + 1) ↦ mockJetP k r j.1 (ω s)) := by
    ext s j; rfl
  rw [hmap, ← RingHom.map_det, mockModular_jet_det_eq]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C]
  have hX : x ^ (r * (r + 1)) ≠ 0 := pow_ne_zero _ hx
  have hinj : Function.Injective ω := prime_freq_injective hd hc hmono
  have hprod : (∏ a : Fin (r + 1), ∏ b ∈ Finset.Ioi a, (ω b - ω a)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun a _ ↦
      Finset.prod_ne_zero_iff.mpr fun b hb ↦ ?_
    have hab : a < b := Finset.mem_Ioi.mp hb
    exact sub_ne_zero.mpr (fun h ↦ hab.ne' (hinj h))
  exact mul_ne_zero hX hprod

/-- Multiplying each row `s` of the prime-frequency jet matrix by any nonzero residue amplitude
`w s ≠ 0` (such as `Real.sin (Real.pi * p s / 3) ≠ 0`) preserves nonsingularity. -/
theorem prime_dilation_weighted_jet_det_ne_zero (k : ℂ) (r : ℕ) {d : ℕ} (hd : 0 < d)
    {c : ℂ} (hc : c ≠ 0) {p : Fin (r + 1) → ℕ} (hmono : StrictMono p)
    {w : Fin (r + 1) → ℂ} (hw : ∀ s, w s ≠ 0) :
    Matrix.det (Matrix.of fun s j : Fin (r + 1) ↦
      Polynomial.C (w s) * mockJetP k r j.1 (c * ((p s : ℂ) ^ 2) / (d : ℂ))) ≠ 0 := by
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Polynomial ℂ) :=
    Matrix.of fun s j ↦ mockJetP k r j.1 (c * ((p s : ℂ) ^ 2) / (d : ℂ))
  have hfac : (Matrix.of fun s j : Fin (r + 1) ↦
      Polynomial.C (w s) * mockJetP k r j.1 (c * ((p s : ℂ) ^ 2) / (d : ℂ))) =
      Matrix.diagonal (fun s ↦ Polynomial.C (w s)) * M := by
    ext s j
    simp [M, Matrix.diagonal_mul]
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal]
  have hdiag : (∏ s : Fin (r + 1), Polynomial.C (w s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s _ ↦ Polynomial.C_ne_zero.mpr (hw s)
  exact mul_ne_zero hdiag (prime_dilation_jet_det_ne_zero k r hd hc hmono)

/-! ### 5. Descending Block-Elimination & Dual-Ray Mock/False-Theta Joint Elimination -/

/-- Cramer's-rule elimination over any integral domain `A` lifted to `MvPolynomial ι A`:
if `M : Matrix (Fin n) (Fin n) A` has `M.det ≠ 0` and `(M.map C) *ᵥ v = 0`, then `v = 0`. -/
theorem mvPoly_vec_eq_zero_of_det_ne_zero {A ι : Type*} [CommRing A] [IsDomain A] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (hdet : M.det ≠ 0)
    (v : Fin n → MvPolynomial ι A)
    (hv : ∀ s : Fin n, ∑ j : Fin n, MvPolynomial.C (M s j) * v j = 0) :
    ∀ j : Fin n, v j = 0 := by
  let MC : Matrix (Fin n) (Fin n) (MvPolynomial ι A) := (MvPolynomial.C : A →+* MvPolynomial ι A).mapMatrix M
  have hMC_mulVec : MC *ᵥ v = 0 := by
    funext s
    simpa [MC, Matrix.mulVec, dotProduct] using hv s
  have hMC_det : MC.det ≠ 0 := by
    rw [show MC.det = MvPolynomial.C M.det from (RingHom.map_det (MvPolynomial.C : A →+* MvPolynomial ι A) M).symm]
    exact fun h ↦ hdet (MvPolynomial.C_eq_zero.mp h)
  have hscale : MC.det • v = 0 := by
    have h1 := congrArg (MC.adjugate *ᵥ ·) hMC_mulVec
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
      Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    exact h1
  intro j
  have hj := congrFun hscale j
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hj
  exact (mul_eq_zero.mp hj).resolve_left hMC_det

/-- **Descending Prime-Dilation Block Elimination (`prime_dilation_block_elimination`):**
Given a finite set `D : Finset ℕ` of positive integer dilations, weight `k₀ : ℂ`, nonzero scale
`c : ℂ`, order `r : ℕ`, a polynomial `R : MvPolynomial (ℕ × Fin (r + 1)) (Polynomial ℂ)`, and
an amplitude function `amp : ℕ → ℕ → ℕ → ℂ` (representing the jump amplitude of block `d'` at
prime frequency `c * p^2 / d`) satisfying:
1. `hamp_self`: block `d` has nonzero amplitude at its own prime frequencies `p > 3`,
2. `hamp_supp`: block `d'` can contribute at frequency `c * p^2 / d` only if `∃ k > 0, k^2 * d = p^2 * d'`,
3. `hvanish`: for every `d ∈ D` and every prime `p > 3`, the combined directional derivative of `R`
   across all blocks `d' ∈ D` at frequency `c * p^2 / d` vanishes identically,

then EVERY partial derivative `MvPolynomial.pderiv (d, j) R` vanishes identically for all `d ∈ D`
and all `j : Fin (r + 1)`. -/
theorem prime_dilation_block_elimination (k₀ : ℂ) {c : ℂ} (hc : c ≠ 0) (r : ℕ)
    (D : Finset ℕ) (hD_pos : ∀ d ∈ D, 0 < d)
    (R : MvPolynomial (ℕ × Fin (r + 1)) (Polynomial ℂ))
    (amp : ℕ → ℕ → ℕ → ℂ)
    (hamp_self : ∀ d ∈ D, ∀ p : ℕ, Nat.Prime p → 3 < p → amp d d p ≠ 0)
    (hamp_supp : ∀ d' ∈ D, ∀ d ∈ D, ∀ p : ℕ, amp d' d p ≠ 0 → ∃ k : ℕ, 0 < k ∧ k ^ 2 * d = p ^ 2 * d')
    (hvanish : ∀ d ∈ D, ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∑ d' ∈ D, MvPolynomial.C (Polynomial.C (amp d' d p)) *
        (∑ j : Fin (r + 1),
          MvPolynomial.C (mockJetP k₀ r j.1 (c * ((p : ℂ) ^ 2) / (d : ℂ))) *
            MvPolynomial.pderiv (d', j) R) = 0) :
    ∀ d ∈ D, ∀ j : Fin (r + 1), MvPolynomial.pderiv (d, j) R = 0 := by
  induction hn : D.card using Nat.strong_induction_on generalizing D with
  | ind n ih =>
    rcases D.eq_empty_or_nonempty with rfl | hne
    · intro d hd; exact absurd hd (Finset.notMem_empty d)
    · set dmax := D.max' hne with hdmax_def
      have hdmax_mem : dmax ∈ D := Finset.max'_mem D hne
      have hdmax_pos : 0 < dmax := hD_pos dmax hdmax_mem
      obtain ⟨p, hmono, hprime, hgt, _, _, hisol⟩ :=
        exists_isolated_primes_for_max_dilation D hD_pos hne r
      -- Step 1: Isolate the maximal block `dmax` at the `r + 1` primes `p 0 < ... < p r`.
      have hmax_sys : ∀ s : Fin (r + 1),
          ∑ j : Fin (r + 1),
            MvPolynomial.C (mockJetP k₀ r j.1 (c * ((p s : ℂ) ^ 2) / (dmax : ℂ))) *
              MvPolynomial.pderiv (dmax, j) R = 0 := by
        intro s
        have hv := hvanish dmax hdmax_mem (p s) (hprime s) (hgt s).1
        have hcollapse :
            ∑ d' ∈ D, MvPolynomial.C (Polynomial.C (amp d' dmax (p s))) *
              (∑ j : Fin (r + 1),
                MvPolynomial.C (mockJetP k₀ r j.1 (c * ((p s : ℂ) ^ 2) / (dmax : ℂ))) *
                  MvPolynomial.pderiv (d', j) R) =
            MvPolynomial.C (Polynomial.C (amp dmax dmax (p s))) *
              (∑ j : Fin (r + 1),
                MvPolynomial.C (mockJetP k₀ r j.1 (c * ((p s : ℂ) ^ 2) / (dmax : ℂ))) *
                  MvPolynomial.pderiv (dmax, j) R) := by
          rw [Finset.sum_eq_single dmax]
          · intro d' hd' hne_d
            have hle : d' ≤ dmax := Finset.le_max' D d' hd'
            have hlt : d' < dmax := lt_of_le_of_ne hle hne_d
            have hamp0 : amp d' dmax (p s) = 0 := by
              by_contra hne0
              obtain ⟨k, _, hk⟩ := hamp_supp d' hd' dmax hdmax_mem (p s) hne0
              exact hisol s d' hd' hlt k hk
            simp [hamp0]
          · intro hnot; exact absurd hdmax_mem hnot
        rw [hcollapse] at hv
        have hscalar_ne :
            (MvPolynomial.C (Polynomial.C (amp dmax dmax (p s))) :
              MvPolynomial (ℕ × Fin (r + 1)) (Polynomial ℂ)) ≠ 0 := by
          intro h0
          have h1 : Polynomial.C (amp dmax dmax (p s)) = 0 := MvPolynomial.C_eq_zero.mp h0
          exact hamp_self dmax hdmax_mem (p s) (hprime s) (hgt s).1 (Polynomial.C_eq_zero.mp h1)
        exact (mul_eq_zero.mp hv).resolve_left hscalar_ne
      -- Step 2: Invert the `(r + 1) × (r + 1)` prime-frequency jet Vandermonde matrix!
      have hdmax_zero : ∀ j : Fin (r + 1), MvPolynomial.pderiv (dmax, j) R = 0 := by
        let M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Polynomial ℂ) :=
          Matrix.of fun s j ↦ mockJetP k₀ r j.1 (c * ((p s : ℂ) ^ 2) / (dmax : ℂ))
        exact mvPoly_vec_eq_zero_of_det_ne_zero M
          (prime_dilation_jet_det_ne_zero k₀ r hdmax_pos hc hmono)
          (fun j ↦ MvPolynomial.pderiv (dmax, j) R)
          hmax_sys
      -- Step 3: Descend to `D' = D.erase dmax`!
      let D' := D.erase dmax
      have hcard_lt : D'.card < n := by
        rw [← hn]
        exact Finset.card_erase_lt_of_mem hdmax_mem
      have hD'_sub : D' ⊆ D := Finset.erase_subset dmax D
      have hD'_zero : ∀ d ∈ D', ∀ j : Fin (r + 1), MvPolynomial.pderiv (d, j) R = 0 := by
        refine ih D'.card hcard_lt D' (fun d hd ↦ hD_pos d (hD'_sub hd))
          (fun d hd p hp h3 ↦ hamp_self d (hD'_sub hd) p hp h3)
          (fun d' hd' d hd p hne0 ↦ hamp_supp d' (hD'_sub hd') d (hD'_sub hd) p hne0)
          ?_ rfl
        intro d hd p hp h3
        have hv := hvanish d (hD'_sub hd) p hp h3
        have hsplit := Finset.add_sum_erase D
          (fun d' ↦ MvPolynomial.C (Polynomial.C (amp d' d p)) *
            (∑ j : Fin (r + 1),
              MvPolynomial.C (mockJetP k₀ r j.1 (c * ((p : ℂ) ^ 2) / (d : ℂ))) *
                MvPolynomial.pderiv (d', j) R))
          hdmax_mem
        have hdmax_term :
            MvPolynomial.C (Polynomial.C (amp dmax d p)) *
              (∑ j : Fin (r + 1),
                MvPolynomial.C (mockJetP k₀ r j.1 (c * ((p : ℂ) ^ 2) / (d : ℂ))) *
                  MvPolynomial.pderiv (dmax, j) R) = 0 := by
          simp [hdmax_zero]
        rw [hdmax_term, zero_add] at hsplit
        simpa [D', hsplit] using hv
      -- Combine `dmax` and `D.erase dmax`!
      intro d hd j
      by_cases hEq : d = dmax
      · subst hEq; exact hdmax_zero j
      · exact hD'_zero d (Finset.mem_erase.mpr ⟨hEq, hd⟩) j

/-- **Dual-Ray (Mock + False Theta) Joint Prime-Dilation Elimination (`dual_ray_prime_dilation_elimination`):**
For ANY two finite sets of positive integer dilations `Dpos, Dneg : Finset ℕ` (even when
`Dpos = Dneg`!), a polynomial `R : MvPolynomial ((Bool × ℕ) × Fin (r + 1)) (Polynomial ℂ)`
whose positive-ray (`true`) jump directional derivatives vanish on `Dpos` at frequencies `+c * p^2 / d`
and whose negative-ray (`false`) jump directional derivatives vanish on `Dneg` at frequencies
`-c * p^2 / d` has EVERY partial derivative in `Dpos` and `Dneg` identically zero. -/
theorem dual_ray_prime_dilation_elimination (kpos kneg : ℂ) {c : ℂ} (hc : c ≠ 0) (r : ℕ)
    (Dpos Dneg : Finset ℕ)
    (hDpos : ∀ d ∈ Dpos, 0 < d) (hDneg : ∀ d ∈ Dneg, 0 < d)
    (R : MvPolynomial ((Bool × ℕ) × Fin (r + 1)) (Polynomial ℂ))
    (ampPos ampNeg : ℕ → ℕ → ℕ → ℂ)
    (hampPos_self : ∀ d ∈ Dpos, ∀ p : ℕ, Nat.Prime p → 3 < p → ampPos d d p ≠ 0)
    (hampPos_supp : ∀ d' ∈ Dpos, ∀ d ∈ Dpos, ∀ p : ℕ,
      ampPos d' d p ≠ 0 → ∃ k : ℕ, 0 < k ∧ k ^ 2 * d = p ^ 2 * d')
    (hvanishPos : ∀ d ∈ Dpos, ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∑ d' ∈ Dpos, MvPolynomial.C (Polynomial.C (ampPos d' d p)) *
        (∑ j : Fin (r + 1),
          MvPolynomial.C (mockJetP kpos r j.1 (c * ((p : ℂ) ^ 2) / (d : ℂ))) *
            MvPolynomial.pderiv ((true, d'), j) R) = 0)
    (hampNeg_self : ∀ d ∈ Dneg, ∀ p : ℕ, Nat.Prime p → 3 < p → ampNeg d d p ≠ 0)
    (hampNeg_supp : ∀ d' ∈ Dneg, ∀ d ∈ Dneg, ∀ p : ℕ,
      ampNeg d' d p ≠ 0 → ∃ k : ℕ, 0 < k ∧ k ^ 2 * d = p ^ 2 * d')
    (hvanishNeg : ∀ d ∈ Dneg, ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∑ d' ∈ Dneg, MvPolynomial.C (Polynomial.C (ampNeg d' d p)) *
        (∑ j : Fin (r + 1),
          MvPolynomial.C (mockJetP kneg r j.1 ((-c) * ((p : ℂ) ^ 2) / (d : ℂ))) *
            MvPolynomial.pderiv ((false, d'), j) R) = 0) :
    (∀ d ∈ Dpos, ∀ j : Fin (r + 1), MvPolynomial.pderiv ((true, d), j) R = 0) ∧
    (∀ d ∈ Dneg, ∀ j : Fin (r + 1), MvPolynomial.pderiv ((false, d), j) R = 0) := by
  have helim_branch : ∀ (b : Bool) (k₀ c₀ : ℂ), c₀ ≠ 0 →
      ∀ (D : Finset ℕ), (∀ d ∈ D, 0 < d) →
      ∀ (amp : ℕ → ℕ → ℕ → ℂ),
        (∀ d ∈ D, ∀ p : ℕ, Nat.Prime p → 3 < p → amp d d p ≠ 0) →
        (∀ d' ∈ D, ∀ d ∈ D, ∀ p : ℕ, amp d' d p ≠ 0 → ∃ k : ℕ, 0 < k ∧ k ^ 2 * d = p ^ 2 * d') →
        (∀ d ∈ D, ∀ p : ℕ, Nat.Prime p → 3 < p →
          ∑ d' ∈ D, MvPolynomial.C (Polynomial.C (amp d' d p)) *
            (∑ j : Fin (r + 1),
              MvPolynomial.C (mockJetP k₀ r j.1 (c₀ * ((p : ℂ) ^ 2) / (d : ℂ))) *
                MvPolynomial.pderiv ((b, d'), j) R) = 0) →
      ∀ d ∈ D, ∀ j : Fin (r + 1), MvPolynomial.pderiv ((b, d), j) R = 0 := by
    intro b k₀ c₀ hc₀ D hD amp hself hsupp hv
    induction hn : D.card using Nat.strong_induction_on generalizing D with
    | ind n ih =>
      rcases D.eq_empty_or_nonempty with rfl | hne
      · intro d hd; exact absurd hd (Finset.notMem_empty d)
      · set dmax := D.max' hne
        have hdmax_mem : dmax ∈ D := Finset.max'_mem D hne
        have hdmax_pos : 0 < dmax := hD dmax hdmax_mem
        obtain ⟨p, hmono, hprime, hgt, _, _, hisol⟩ :=
          exists_isolated_primes_for_max_dilation D hD hne r
        have hmax_sys : ∀ s : Fin (r + 1),
            ∑ j : Fin (r + 1),
              MvPolynomial.C (mockJetP k₀ r j.1 (c₀ * ((p s : ℂ) ^ 2) / (dmax : ℂ))) *
                MvPolynomial.pderiv ((b, dmax), j) R = 0 := by
          intro s
          have hvs := hv dmax hdmax_mem (p s) (hprime s) (hgt s).1
          have hcol :
              ∑ d' ∈ D, MvPolynomial.C (Polynomial.C (amp d' dmax (p s))) *
                (∑ j : Fin (r + 1),
                  MvPolynomial.C (mockJetP k₀ r j.1 (c₀ * ((p s : ℂ) ^ 2) / (dmax : ℂ))) *
                    MvPolynomial.pderiv ((b, d'), j) R) =
              MvPolynomial.C (Polynomial.C (amp dmax dmax (p s))) *
                (∑ j : Fin (r + 1),
                  MvPolynomial.C (mockJetP k₀ r j.1 (c₀ * ((p s : ℂ) ^ 2) / (dmax : ℂ))) *
                    MvPolynomial.pderiv ((b, dmax), j) R) := by
            rw [Finset.sum_eq_single dmax]
            · intro d' hd' hne_d
              have hlt : d' < dmax := lt_of_le_of_ne (Finset.le_max' D d' hd') hne_d
              have h0 : amp d' dmax (p s) = 0 := by
                by_contra hne0
                obtain ⟨k, _, hk⟩ := hsupp d' hd' dmax hdmax_mem (p s) hne0
                exact hisol s d' hd' hlt k hk
              simp [h0]
            · intro hnot; exact absurd hdmax_mem hnot
          rw [hcol] at hvs
          have hsc : (MvPolynomial.C (Polynomial.C (amp dmax dmax (p s))) :
              MvPolynomial ((Bool × ℕ) × Fin (r + 1)) (Polynomial ℂ)) ≠ 0 := by
            intro h0
            have h1 : Polynomial.C (amp dmax dmax (p s)) = 0 := MvPolynomial.C_eq_zero.mp h0
            exact hself dmax hdmax_mem (p s) (hprime s) (hgt s).1 (Polynomial.C_eq_zero.mp h1)
          exact (mul_eq_zero.mp hvs).resolve_left hsc
        have hdmax_zero : ∀ j : Fin (r + 1), MvPolynomial.pderiv ((b, dmax), j) R = 0 := by
          let M : Matrix (Fin (r + 1)) (Fin (r + 1)) (Polynomial ℂ) :=
            Matrix.of fun s j ↦ mockJetP k₀ r j.1 (c₀ * ((p s : ℂ) ^ 2) / (dmax : ℂ))
          exact mvPoly_vec_eq_zero_of_det_ne_zero M
            (prime_dilation_jet_det_ne_zero k₀ r hdmax_pos hc₀ hmono)
            (fun j ↦ MvPolynomial.pderiv ((b, dmax), j) R)
            hmax_sys
        let D' := D.erase dmax
        have hD'_sub : D' ⊆ D := Finset.erase_subset dmax D
        have hD'_zero : ∀ d ∈ D', ∀ j : Fin (r + 1), MvPolynomial.pderiv ((b, d), j) R = 0 := by
          refine ih D'.card (hn ▸ Finset.card_erase_lt_of_mem hdmax_mem) D'
            (fun d hd ↦ hD d (hD'_sub hd))
            (fun d hd p hp h3 ↦ hself d (hD'_sub hd) p hp h3)
            (fun d' hd' d hd p hne0 ↦ hsupp d' (hD'_sub hd') d (hD'_sub hd) p hne0)
            ?_ rfl
          intro d hd p hp h3
          have hvd := hv d (hD'_sub hd) p hp h3
          have hsplit := Finset.add_sum_erase D
            (fun d' ↦ MvPolynomial.C (Polynomial.C (amp d' d p)) *
              (∑ j : Fin (r + 1),
                MvPolynomial.C (mockJetP k₀ r j.1 (c₀ * ((p : ℂ) ^ 2) / (d : ℂ))) *
                  MvPolynomial.pderiv ((b, d'), j) R))
            hdmax_mem
          have hterm0 :
              MvPolynomial.C (Polynomial.C (amp dmax d p)) *
                (∑ j : Fin (r + 1),
                  MvPolynomial.C (mockJetP k₀ r j.1 (c₀ * ((p : ℂ) ^ 2) / (d : ℂ))) *
                    MvPolynomial.pderiv ((b, dmax), j) R) = 0 := by
            simp [hdmax_zero]
          rw [hterm0, zero_add] at hsplit
          simpa [D', hsplit] using hvd
        intro d hd j
        by_cases hEq : d = dmax
        · subst hEq; exact hdmax_zero j
        · exact hD'_zero d (Finset.mem_erase.mpr ⟨hEq, hd⟩) j
  exact ⟨helim_branch true kpos c hc Dpos hDpos ampPos hampPos_self hampPos_supp hvanishPos,
    helim_branch false kneg (-c) (neg_ne_zero.mpr hc) Dneg hDneg ampNeg hampNeg_self
      hampNeg_supp hvanishNeg⟩

/-- **Corollary (`dual_ray_prime_dilation_constant`):**
If every variable occurring in `R` belongs to `Dpos` (positive ray) or `Dneg` (negative ray)
and both rays satisfy the prime-frequency jump-vanishing hypotheses, then `R` is independent of
every jet variable (`R = MvPolynomial.C (MvPolynomial.constantCoeff R)`). -/
theorem dual_ray_prime_dilation_constant (kpos kneg : ℂ) {c : ℂ} (hc : c ≠ 0) (r : ℕ)
    (Dpos Dneg : Finset ℕ)
    (hDpos : ∀ d ∈ Dpos, 0 < d) (hDneg : ∀ d ∈ Dneg, 0 < d)
    (R : MvPolynomial ((Bool × ℕ) × Fin (r + 1)) (Polynomial ℂ))
    (hvars : ∀ v ∈ R.vars, (v.1.1 = true ∧ v.1.2 ∈ Dpos) ∨ (v.1.1 = false ∧ v.1.2 ∈ Dneg))
    (ampPos ampNeg : ℕ → ℕ → ℕ → ℂ)
    (hampPos_self : ∀ d ∈ Dpos, ∀ p : ℕ, Nat.Prime p → 3 < p → ampPos d d p ≠ 0)
    (hampPos_supp : ∀ d' ∈ Dpos, ∀ d ∈ Dpos, ∀ p : ℕ,
      ampPos d' d p ≠ 0 → ∃ k : ℕ, 0 < k ∧ k ^ 2 * d = p ^ 2 * d')
    (hvanishPos : ∀ d ∈ Dpos, ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∑ d' ∈ Dpos, MvPolynomial.C (Polynomial.C (ampPos d' d p)) *
        (∑ j : Fin (r + 1),
          MvPolynomial.C (mockJetP kpos r j.1 (c * ((p : ℂ) ^ 2) / (d : ℂ))) *
            MvPolynomial.pderiv ((true, d'), j) R) = 0)
    (hampNeg_self : ∀ d ∈ Dneg, ∀ p : ℕ, Nat.Prime p → 3 < p → ampNeg d d p ≠ 0)
    (hampNeg_supp : ∀ d' ∈ Dneg, ∀ d ∈ Dneg, ∀ p : ℕ,
      ampNeg d' d p ≠ 0 → ∃ k : ℕ, 0 < k ∧ k ^ 2 * d = p ^ 2 * d')
    (hvanishNeg : ∀ d ∈ Dneg, ∀ p : ℕ, Nat.Prime p → 3 < p →
      ∑ d' ∈ Dneg, MvPolynomial.C (Polynomial.C (ampNeg d' d p)) *
        (∑ j : Fin (r + 1),
          MvPolynomial.C (mockJetP kneg r j.1 ((-c) * ((p : ℂ) ^ 2) / (d : ℂ))) *
            MvPolynomial.pderiv ((false, d'), j) R) = 0) :
    R = MvPolynomial.C (MvPolynomial.constantCoeff R) := by
  have ⟨hpos0, hneg0⟩ := dual_ray_prime_dilation_elimination kpos kneg hc r Dpos Dneg hDpos hDneg R
    ampPos ampNeg hampPos_self hampPos_supp hvanishPos hampNeg_self hampNeg_supp hvanishNeg
  have hall_pderiv : ∀ v : (Bool × ℕ) × Fin (r + 1), MvPolynomial.pderiv v R = 0 := by
    intro v
    by_cases hv : v ∈ R.vars
    · rcases hvars v hv with ⟨ht, hd⟩ | ⟨hf, hd⟩
      · rcases v with ⟨⟨b, d⟩, j⟩
        dsimp only at ht hd
        subst ht
        exact hpos0 d hd j
      · rcases v with ⟨⟨b, d⟩, j⟩
        dsimp only at hf hd
        subst hf
        exact hneg0 d hd j
    · exact MvPolynomial.pderiv_eq_zero_of_notMem_vars hv
  -- In characteristic zero, vanishing of all partial derivatives implies `R` is constant!
  apply MvPolynomial.ext
  intro m
  by_cases hm : m = 0
  · subst hm
    simp [MvPolynomial.constantCoeff_eq]
  · rw [MvPolynomial.coeff_C]
    have hne0 : (0 : ((Bool × ℕ) × Fin (r + 1)) →₀ ℕ) ≠ m := Ne.symm hm
    simp only [hne0, ↓reduceIte]
    obtain ⟨v, hv⟩ : ∃ v, m v ≠ 0 := by
      by_contra h
      push Not at h
      exact hm (Finsupp.ext h)
    set d : ((Bool × ℕ) × Fin (r + 1)) →₀ ℕ := m - Finsupp.single v 1
    have hpv := congrArg (fun p : MvPolynomial ((Bool × ℕ) × Fin (r + 1)) (Polynomial ℂ) ↦
      p.coeff d) (hall_pderiv v)
    simp only [MvPolynomial.coeff_pderiv] at hpv
    have hzero : (0 : MvPolynomial ((Bool × ℕ) × Fin (r + 1)) (Polynomial ℂ)).coeff d = 0 := by
      simp
    rw [hzero] at hpv
    have hadd : d + Finsupp.single v 1 = m := by
      ext w
      by_cases hvw : w = v
      · subst hvw; simp [d]; omega
      · simp [d, Ne.symm hvw]
    rw [hadd] at hpv
    have hcoeff_ne : ((d v : Polynomial ℂ) + 1) ≠ 0 := by
      have hcast : ((d v : Polynomial ℂ) + 1) = (((d v + 1 : ℕ) : Polynomial ℂ)) := by push_cast; rfl
      rw [hcast]
      exact Nat.cast_ne_zero.mpr (Nat.succ_ne_zero (d v))
    exact (mul_eq_zero.mp hpv).resolve_right hcoeff_ne

end

end CubicTheta.AllD
