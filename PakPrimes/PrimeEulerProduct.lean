module

public import PakPrimes.PartitionsIntoPrimes
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.LinearCombination

/-! # Literal Euler Products for Partitions into Primes (A000607) & Distinct-Prime Partitions (A000586)

Following the coefficientwise Pi-topology pattern of `MacMahonEulerFactors` / `MacMahonEulerProduct`,
this module identifies the recurrence-defined series `partitionPrimesSeries` and
`distinctPrimesSeries` with their literal Euler products over `p : Nat.Primes`:

* `hasProd_partitionPrimesEulerProduct`:
  `HasProd (fun p : Nat.Primes => (1 - (X : PowerSeries ℂ) ^ (p : ℕ))⁻¹) partitionPrimesSeries`
* `partitionPrimesEulerProduct_algebraicIndependent_of_pnt`:
  differential transcendence over `ℂ(q)` of the literal `tprod` `∏' p : Nat.Primes, (1 - X ^ (p : ℕ))⁻¹`
* `hasProd_distinctPrimesEulerProduct`:
  `HasProd (fun p : Nat.Primes => 1 + (X : PowerSeries ℂ) ^ (p : ℕ)) distinctPrimesSeries`
* `distinctPrimesEulerProduct_algebraicIndependent_of_pnt`:
  differential transcendence over `ℂ(q)` of the literal `tprod` `∏' p : Nat.Primes, (1 + X ^ (p : ℕ))`
-/

public section
noncomputable section

namespace PakPrimes.PartitionsIntoPrimes

open PowerSeries Filter PakPrimes.PrimeNome PakPrimes.Main
open scoped PowerSeries.WithPiTopology Topology BigOperators

/-- Geometric series `∑_{k ≥ 0} X^{k * m}` for `m ≥ 1`. -/
private def geomSeries (m : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if m ∣ n then 1 else 0

private lemma constantCoeff_X_pow_zero {m : ℕ} (hm : m ≠ 0) :
    constantCoeff ((X : PowerSeries ℂ) ^ m) = 0 := by
  rw [map_pow, constantCoeff_X, zero_pow hm]

private lemma geomSeries_mul_one_sub {m : ℕ} (hm : 0 < m) :
    geomSeries m * (1 - X ^ m) = 1 := by
  rw [mul_sub, mul_one]
  ext d
  rw [map_sub, coeff_mul_X_pow', coeff_one]
  by_cases h : m ≤ d
  · have hd : d ≠ 0 := by omega
    simp [h, hd, geomSeries, Nat.dvd_sub_iff_left h (dvd_refl m)]
  · by_cases hd : d = 0
    · simp [hd, geomSeries, Nat.ne_of_gt hm]
    · have hn : ¬(m ∣ d) := fun hav => h (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hav)
      simp [h, hd, hn, geomSeries]

private lemma geomSeries_eq_inv {m : ℕ} (hm : 0 < m) :
    geomSeries m = (1 - X ^ m)⁻¹ := by
  refine (PowerSeries.eq_inv_iff_mul_eq_one ?_).mpr (geomSeries_mul_one_sub hm)
  simp [constantCoeff_X_pow_zero (Nat.ne_of_gt hm)]

/-- Alternating geometric series `∑_{k ≥ 0} (-1)^k X^{k * m}` for `m ≥ 1`. -/
private def altGeomSeries (m : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if m ∣ n then (-1 : ℂ) ^ (n / m) else 0

private lemma altGeomSeries_mul_one_add {m : ℕ} (hm : 0 < m) :
    altGeomSeries m * (1 + X ^ m) = 1 := by
  rw [mul_add, mul_one]
  ext d
  rw [map_add, coeff_mul_X_pow', coeff_one]
  by_cases h : m ≤ d
  · have hd : d ≠ 0 := by omega
    simp only [h, ↓reduceIte, hd, altGeomSeries, coeff_mk]
    by_cases hdv : m ∣ d
    · have hdv' : m ∣ d - m := (Nat.dvd_sub_iff_left h (dvd_refl m)).mpr hdv
      simp only [hdv, hdv', ↓reduceIte]
      obtain ⟨k, rfl⟩ := hdv
      have hk : 1 ≤ k := by
        rcases k with _ | k
        · simp at hd
        · omega
      have hsub : m * k - m = m * (k - 1) := by
        cases k with
        | zero => omega
        | succ k' => simp [Nat.mul_succ]
      rw [hsub, Nat.mul_div_cancel_left k hm, Nat.mul_div_cancel_left (k - 1) hm]
      cases k with
      | zero => omega
      | succ k' =>
        simp [pow_succ]
    · have hdv' : ¬(m ∣ d - m) := fun h' => hdv ((Nat.dvd_sub_iff_left h (dvd_refl m)).mp h')
      simp [hdv, hdv']
  · by_cases hd : d = 0
    · simp [hd, altGeomSeries, Nat.ne_of_gt hm]
    · have hn : ¬(m ∣ d) := fun hav => h (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hav)
      simp [h, hd, hn, altGeomSeries]

/-- The Euler-product factor `(1 - X^p)⁻¹` for a prime `p`. -/
@[expose] def primePartFactor (p : Nat.Primes) : PowerSeries ℂ :=
  (1 - (X : PowerSeries ℂ) ^ (p : ℕ))⁻¹

/-- The Euler-product factor `1 + X^p` for a prime `p`. -/
@[expose] def primeDistinctFactor (p : Nat.Primes) : PowerSeries ℂ :=
  1 + (X : PowerSeries ℂ) ^ (p : ℕ)

private lemma primePartFactor_constantCoeff (p : Nat.Primes) :
    constantCoeff (primePartFactor p) = 1 := by
  simp [primePartFactor, PowerSeries.constantCoeff_inv, constantCoeff_X_pow_zero p.prop.ne_zero]

private lemma primeDistinctFactor_constantCoeff (p : Nat.Primes) :
    constantCoeff (primeDistinctFactor p) = 1 := by
  simp [primeDistinctFactor, constantCoeff_X_pow_zero p.prop.ne_zero]

private lemma primePartFactor_ode (p : Nat.Primes) :
    X * derivative (primePartFactor p) =
      (C ((p : ℕ) : ℂ) * (geomSeries (p : ℕ) - 1)) * primePartFactor p := by
  have hp : 0 < (p : ℕ) := p.prop.pos
  have h1 : geomSeries (p : ℕ) - 1 = X ^ (p : ℕ) * geomSeries (p : ℕ) := by
    linear_combination geomSeries_mul_one_sub hp
  have hderiv : derivative ((X : PowerSeries ℂ) ^ (p : ℕ)) =
      C ((p : ℕ) : ℂ) * X ^ ((p : ℕ) - 1) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero p.prop.ne_zero
    rw [hm, derivative_X_pow_succ]
    simp [map_natCast]
  rw [h1, geomSeries_eq_inv hp, primePartFactor, derivative_inv', map_sub, derivative_one, hderiv]
  have hxp : X * X ^ ((p : ℕ) - 1) = (X : PowerSeries ℂ) ^ (p : ℕ) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero p.prop.ne_zero
    rw [hm, Nat.succ_sub_one, pow_succ']
  calc X * (-(1 - X ^ (p : ℕ))⁻¹ ^ 2 * (0 - C ((p : ℕ) : ℂ) * X ^ ((p : ℕ) - 1)))
      = C ((p : ℕ) : ℂ) * (X * X ^ ((p : ℕ) - 1)) * (1 - X ^ (p : ℕ))⁻¹ * (1 - X ^ (p : ℕ))⁻¹ := by
        ring
    _ = C ((p : ℕ) : ℂ) * (X ^ (p : ℕ) * (1 - X ^ (p : ℕ))⁻¹) * (1 - X ^ (p : ℕ))⁻¹ := by
        rw [hxp]; ring

private lemma primeDistinctFactor_ode (p : Nat.Primes) :
    X * derivative (primeDistinctFactor p) =
      (C ((p : ℕ) : ℂ) * (1 - altGeomSeries (p : ℕ))) * primeDistinctFactor p := by
  have hp : 0 < (p : ℕ) := p.prop.pos
  have h1 : 1 - altGeomSeries (p : ℕ) = X ^ (p : ℕ) * altGeomSeries (p : ℕ) := by
    linear_combination -(altGeomSeries_mul_one_add hp)
  have hderiv : derivative ((X : PowerSeries ℂ) ^ (p : ℕ)) =
      C ((p : ℕ) : ℂ) * X ^ ((p : ℕ) - 1) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero p.prop.ne_zero
    rw [hm, derivative_X_pow_succ]
    simp [map_natCast]
  have hxp : X * X ^ ((p : ℕ) - 1) = (X : PowerSeries ℂ) ^ (p : ℕ) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero p.prop.ne_zero
    rw [hm, Nat.succ_sub_one, pow_succ']
  rw [h1, primeDistinctFactor, map_add, derivative_one, zero_add, hderiv]
  calc X * (C ((p : ℕ) : ℂ) * X ^ ((p : ℕ) - 1))
      = C ((p : ℕ) : ℂ) * (X * X ^ ((p : ℕ) - 1)) * 1 := by ring
    _ = C ((p : ℕ) : ℂ) * X ^ (p : ℕ) * (altGeomSeries (p : ℕ) * (1 + X ^ (p : ℕ))) := by
        rw [hxp, altGeomSeries_mul_one_add hp]
    _ = C ((p : ℕ) : ℂ) * (X ^ (p : ℕ) * altGeomSeries (p : ℕ)) * (1 + X ^ (p : ℕ)) := by ring

private lemma euler_prod_primes (factor weight : Nat.Primes → PowerSeries ℂ)
    (h : ∀ p, X * derivative (factor p) = weight p * factor p) (s : Finset Nat.Primes) :
    X * derivative (∏ p ∈ s, factor p) = (∑ p ∈ s, weight p) * ∏ p ∈ s, factor p := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
    rw [Finset.prod_insert hp, Finset.sum_insert hp, derivative.leibniz]
    simp only [smul_eq_mul]
    linear_combination (∏ q ∈ s, factor q) * h p + factor p * ih

private lemma coeff_euler_prime (f : PowerSeries ℂ) (d : ℕ) :
    coeff d (X * derivative f) = (d : ℂ) * coeff d f := by
  cases d with
  | zero => simp [coeff_zero_X_mul]
  | succ n => simp [coeff_succ_X_mul, coeff_derivative, mul_comm]

private lemma coeff_ext_ode_prime (f g l m : PowerSeries ℂ)
    (h0 : constantCoeff f = constantCoeff g)
    (hf : X * derivative f = l * f) (hg : X * derivative g = m * g)
    (hm : coeff 0 m = 0) (d : ℕ) (hlm : ∀ j ≤ d, coeff j l = coeff j m) :
    coeff d f = coeff d g := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases hd : d = 0
    · simpa [hd, coeff_zero_eq_constantCoeff] using h0
    have hF := congrArg (coeff d) hf
    have hG := congrArg (coeff d) hg
    rw [coeff_euler_prime, coeff_mul] at hF hG
    apply mul_left_cancel₀ (show (d : ℂ) ≠ 0 by exact_mod_cast hd)
    rw [hF, hG]
    refine Finset.sum_congr rfl fun ab hab => ?_
    have hab' : ab.1 + ab.2 = d := by simpa using hab
    rw [hlm ab.1 (by omega)]
    by_cases ha : ab.1 = 0
    · simp [ha, hm]
    · have hlt : ab.2 < d := by omega
      rw [ih ab.2 hlt (fun j hj => hlm j (hj.trans hlt.le))]

/-- Finite set of all primes `p ≤ d` inside `Nat.Primes`. -/
private def primesUpTo (d : ℕ) : Finset Nat.Primes :=
  ((Finset.Icc 1 d).filter Nat.Prime).attach.map
    ⟨fun x => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩, fun a b h => by
      apply Subtype.ext
      exact congrArg (fun q : Nat.Primes => (q : ℕ)) h⟩

private lemma mem_primesUpTo {d : ℕ} {p : Nat.Primes} :
    p ∈ primesUpTo d ↔ (p : ℕ) ≤ d := by
  simp only [primesUpTo, Finset.mem_map, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨⟨n, hn⟩, hEq⟩
    have hle : n ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2
    have hval : n = (p : ℕ) := congrArg (fun q : Nat.Primes => (q : ℕ)) hEq
    omega
  · intro hle
    have hmem : (p : ℕ) ∈ (Finset.Icc 1 d).filter Nat.Prime :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨p.prop.one_lt.le, hle⟩, p.prop⟩
    exact ⟨⟨(p : ℕ), hmem⟩, Subtype.ext rfl⟩

private lemma coeff_primePartWeight (p : Nat.Primes) (j : ℕ) :
    coeff j (C ((p : ℕ) : ℂ) * (geomSeries (p : ℕ) - 1)) =
      if j ≠ 0 ∧ (p : ℕ) ∣ j then ((p : ℕ) : ℂ) else 0 := by
  rw [coeff_C_mul, map_sub, coeff_one]
  simp only [geomSeries, coeff_mk]
  by_cases hj : j = 0
  · subst hj; simp
  · simp [hj]

private lemma coeff_primeDistinctWeight (p : Nat.Primes) (j : ℕ) :
    coeff j (C ((p : ℕ) : ℂ) * (1 - altGeomSeries (p : ℕ))) =
      if j ≠ 0 ∧ (p : ℕ) ∣ j then -((-1 : ℂ) ^ (j / (p : ℕ))) * ((p : ℕ) : ℂ) else 0 := by
  rw [coeff_C_mul, map_sub, coeff_one]
  simp only [altGeomSeries, coeff_mk]
  by_cases hj : j = 0
  · subst hj; simp
  · by_cases hdv : (p : ℕ) ∣ j
    · simp [hj, hdv]; ring
    · simp [hj, hdv]

private lemma coeff_sum_primePartWeight {j d : ℕ} (hjd : j ≤ d) {s : Finset Nat.Primes}
    (hs : primesUpTo d ⊆ s) :
    coeff j (∑ p ∈ s, C ((p : ℕ) : ℂ) * (geomSeries (p : ℕ) - 1)) =
      coeff j partLogDerivSeries := by
  rw [map_sum, coeff_partLogDeriv_eq]
  by_cases hj : j = 0
  · subst hj
    simp only [coeff_primePartWeight, ne_eq, not_true_eq_false, false_and, ↓reduceIte,
      Finset.sum_const_zero]
    simp [sigmaP]
  · simp only [coeff_primePartWeight, hj, ne_eq, not_false_eq_true, true_and]
    rw [← Finset.sum_subset (show primesUpTo j ⊆ s from
      fun p hp => hs (mem_primesUpTo.mpr ((mem_primesUpTo.mp hp).trans hjd)))]
    · simp only [primesUpTo, Finset.sum_map]
      change (∑ x ∈ ((Finset.Icc 1 j).filter Nat.Prime).attach,
        if x.1 ∣ j then (x.1 : ℂ) else 0) = (sigmaP j : ℂ)
      rw [Finset.sum_attach ((Finset.Icc 1 j).filter Nat.Prime)
        (fun p => if p ∣ j then (p : ℂ) else 0)]
      simp only [sigmaP, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs <;> simp
    · intro p _ hpnot
      have hgt : j < (p : ℕ) := not_le.mp (fun hle => hpnot (mem_primesUpTo.mpr hle))
      have hndvd : ¬((p : ℕ) ∣ j) := fun hdvd =>
        not_le_of_gt hgt (Nat.le_of_dvd (Nat.pos_of_ne_zero hj) hdvd)
      simp [hndvd]

private lemma coeff_sum_primeDistinctWeight {j d : ℕ} (hjd : j ≤ d) {s : Finset Nat.Primes}
    (hs : primesUpTo d ⊆ s) :
    coeff j (∑ p ∈ s, C ((p : ℕ) : ℂ) * (1 - altGeomSeries (p : ℕ))) =
      coeff j distinctLogDerivSeries := by
  rw [map_sum]
  simp only [distinctLogDerivSeries, coeff_mk]
  by_cases hj : j = 0
  · subst hj
    simp only [coeff_primeDistinctWeight, ne_eq, not_true_eq_false, false_and, ↓reduceIte,
      Finset.sum_const_zero]
    simp [sigmaPDistinct, sigmaP]
  · simp only [coeff_primeDistinctWeight, hj, ne_eq, not_false_eq_true, true_and]
    rw [← Finset.sum_subset (show primesUpTo j ⊆ s from
      fun p hp => hs (mem_primesUpTo.mpr ((mem_primesUpTo.mp hp).trans hjd)))]
    · simp only [primesUpTo, Finset.sum_map]
      change (∑ x ∈ ((Finset.Icc 1 j).filter Nat.Prime).attach,
        if x.1 ∣ j then -((-1 : ℂ) ^ (j / x.1)) * (x.1 : ℂ) else 0) = (sigmaPDistinct j : ℂ)
      rw [Finset.sum_attach ((Finset.Icc 1 j).filter Nat.Prime)
        (fun p => if p ∣ j then -((-1 : ℂ) ^ (j / p)) * (p : ℂ) else 0)]
      have hterm : ∀ p ∈ (Finset.Icc 1 j).filter Nat.Prime,
          (if p ∣ j then -((-1 : ℂ) ^ (j / p)) * (p : ℂ) else 0) =
          (if p ∣ j then (p : ℂ) else 0) -
            (if 2 ∣ j ∧ p ∣ (j / 2) then 2 * (p : ℂ) else 0) := by
        intro p hp
        have hp0 : 0 < p := (Finset.mem_filter.mp hp).2.pos
        by_cases hdv : p ∣ j
        · by_cases hev : 2 ∣ j / p
          · have h2j : 2 ∣ j := dvd_trans hev (Nat.div_dvd_of_dvd hdv)
            have hpj2 : p ∣ j / 2 := by
              obtain ⟨k, hk⟩ := hev
              obtain ⟨m, rfl⟩ := hdv
              rw [Nat.mul_div_cancel_left m hp0] at hk
              subst hk
              refine ⟨k, ?_⟩
              have : p * (2 * k) = 2 * (p * k) := by ring
              rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
            obtain ⟨k, hk⟩ := hev
            simp only [hdv, h2j, hpj2, and_self, ↓reduceIte, hk, pow_mul]
            norm_num; ring
          · have hnot : ¬(2 ∣ j ∧ p ∣ (j / 2)) := by
              rintro ⟨h2j, hpj2⟩
              apply hev
              obtain ⟨a, ha⟩ := hpj2
              have hj2 : j = 2 * (p * a) := by
                have := Nat.mul_div_cancel' h2j
                omega
              have : j / p = 2 * a := by
                rw [show j = p * (2 * a) by rw [hj2]; ring, Nat.mul_div_cancel_left _ hp0]
              exact ⟨a, this⟩
            have hodd : Odd (j / p) := Nat.not_even_iff_odd.mp (fun h => hev (even_iff_two_dvd.mp h))
            simp only [hdv, hnot, ↓reduceIte, Odd.neg_one_pow hodd]
            ring
        · have hnot : ¬(2 ∣ j ∧ p ∣ (j / 2)) := by
            rintro ⟨h2j, hpj2⟩
            exact hdv (dvd_trans hpj2 (Nat.div_dvd_of_dvd h2j))
          simp [hdv, hnot]
      rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
      have h1 : (∑ p ∈ (Finset.Icc 1 j).filter Nat.Prime, if p ∣ j then (p : ℂ) else 0) =
          (sigmaP j : ℂ) := by
        simp only [sigmaP, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        split_ifs <;> simp
      have h2 : (∑ p ∈ (Finset.Icc 1 j).filter Nat.Prime,
            if 2 ∣ j ∧ p ∣ (j / 2) then 2 * (p : ℂ) else 0) =
          ((if 2 ∣ j then 2 * sigmaP (j / 2) else 0 : ℝ) : ℂ) := by
        by_cases h2j : 2 ∣ j
        · simp only [h2j, true_and, ↓reduceIte, Complex.ofReal_mul, Complex.ofReal_ofNat,
            sigmaP, Complex.ofReal_sum, Finset.mul_sum]
          rw [← Finset.sum_subset (show (Finset.Icc 1 (j / 2)).filter Nat.Prime ⊆
              (Finset.Icc 1 j).filter Nat.Prime from
            Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right (Nat.div_le_self j 2)))]
          · refine Finset.sum_congr rfl fun p _ => ?_
            split_ifs <;> simp
          · intro p hp hpnot
            have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp).2
            have hgt : j / 2 < p := by
              by_contra hle
              push Not at hle
              exact hpnot (Finset.mem_filter.mpr
                ⟨Finset.mem_Icc.mpr ⟨hp_prime.one_lt.le, hle⟩, hp_prime⟩)
            have hj2_pos : 0 < j / 2 := by
              obtain ⟨k, rfl⟩ := h2j
              have : 0 < k := by omega
              omega
            have hndvd : ¬(p ∣ j / 2) := fun hdvd =>
              not_le_of_gt hgt (Nat.le_of_dvd hj2_pos hdvd)
            simp [hndvd]
        · simp [h2j]
      rw [h1, h2, sigmaPDistinct, Complex.ofReal_sub]
    · intro p _ hpnot
      have hgt : j < (p : ℕ) := not_le.mp (fun hle => hpnot (mem_primesUpTo.mpr hle))
      have hndvd : ¬((p : ℕ) ∣ j) := fun hdvd =>
        not_le_of_gt hgt (Nat.le_of_dvd (Nat.pos_of_ne_zero hj) hdvd)
      simp [hndvd]

/-- **Literal Euler Product for Partitions into Primes (OEIS A000607)**:
`∏_{p prime} (1 - q^p)⁻¹` converges in the coefficientwise Pi-topology to `partitionPrimesSeries`. -/
theorem hasProd_partitionPrimesEulerProduct :
    HasProd (fun p : Nat.Primes => (1 - (X : PowerSeries ℂ) ^ (p : ℕ))⁻¹)
      partitionPrimesSeries := by
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℂ _ _ _).2
  intro d
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (primesUpTo d)] with s hs
  symm
  refine coeff_ext_ode_prime _ _ _ _ ?_
    (euler_prod_primes _ _ primePartFactor_ode s) partitionPrimesSeries_ode ?_ d
    (fun j hj => coeff_sum_primePartWeight hj hs)
  · rw [map_prod, Finset.prod_eq_one (fun p _ => primePartFactor_constantCoeff p),
      partitionPrimesSeries_constantCoeff]
  · rw [coeff_partLogDeriv_eq 0]; simp [sigmaP]

/-- **Literal Euler Product for Distinct-Prime Partitions (OEIS A000586)**:
`∏_{p prime} (1 + q^p)` converges in the coefficientwise Pi-topology to `distinctPrimesSeries`. -/
theorem hasProd_distinctPrimesEulerProduct :
    HasProd (fun p : Nat.Primes => 1 + (X : PowerSeries ℂ) ^ (p : ℕ))
      distinctPrimesSeries := by
  apply (PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto ℂ _ _ _).2
  intro d
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (primesUpTo d)] with s hs
  symm
  refine coeff_ext_ode_prime _ _ _ _ ?_
    (euler_prod_primes _ _ primeDistinctFactor_ode s) distinctPrimesSeries_ode ?_ d
    (fun j hj => coeff_sum_primeDistinctWeight hj hs)
  · rw [map_prod, Finset.prod_eq_one (fun p _ => primeDistinctFactor_constantCoeff p),
      distinctPrimesSeries_constantCoeff]
  · simp [distinctLogDerivSeries, sigmaPDistinct, sigmaP]

/-- **Literal Euler-Product Differential Transcendence of Partitions into Primes (A000607)**
assuming only `PNTAllOrders`. -/
theorem partitionPrimesEulerProduct_algebraicIndependent_of_pnt (hpnt : PNTAllOrders) :
    AlgebraicIndependent ℂ (seriesCoordinates
      (∏' p : Nat.Primes, (1 - (X : PowerSeries ℂ) ^ (p : ℕ))⁻¹)) := by
  rw [hasProd_partitionPrimesEulerProduct.tprod_eq]
  exact partitionPrimes_algebraicIndependent_of_pnt hpnt

/-- **Literal Euler-Product Differential Transcendence of Distinct-Prime Partitions (A000586)**
assuming only `PNTAllOrders`. -/
theorem distinctPrimesEulerProduct_algebraicIndependent_of_pnt (hpnt : PNTAllOrders) :
    AlgebraicIndependent ℂ (seriesCoordinates
      (∏' p : Nat.Primes, (1 + (X : PowerSeries ℂ) ^ (p : ℕ)))) := by
  rw [hasProd_distinctPrimesEulerProduct.tprod_eq]
  exact distinctPrimes_algebraicIndependent_of_pnt hpnt

end PakPrimes.PartitionsIntoPrimes
