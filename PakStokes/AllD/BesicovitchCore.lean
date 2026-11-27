module

public import Mathlib.FieldTheory.NormalizedTrace
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! Unconditional all-`r` Besicovitch theorem (`r ≥ 2`) via the elementary
normalized-trace and `|f(0)|^s = u^m` + Bézout argument, yielding exact
`ℚ`-linear independence of `{b^(1/r) : b ∈ Core_r}` and injectivity of the
all-`d` extreme-ray frequency map with zero transcendental tilt. -/
public section
namespace CubicTheta.AllD
open Polynomial Algebra
noncomputable section

/-- A natural number `n` is `r`-free if no non-unit `k` satisfies `k^r ∣ n`.
For `r = 2` this agrees identically with Mathlib's `Squarefree`. -/
def RFree (r n : ℕ) : Prop := ∀ k : ℕ, k ^ r ∣ n → IsUnit k

/-- The subtype of `r`-free natural numbers (`Core_r`). -/
abbrev Core (r : ℕ) := {c : ℕ // RFree r c}

theorem rfree_two_iff_squarefree (n : ℕ) : RFree 2 n ↔ Squarefree n := by
  simp [RFree, Squarefree, sq]

theorem rfree_ne_zero {r n : ℕ} (h : RFree r n) : n ≠ 0 := by
  rintro rfl
  have hu : IsUnit (2 : ℕ) := h 2 (dvd_zero _)
  rw [Nat.isUnit_iff] at hu
  omega

theorem rfree_pos {r n : ℕ} (h : RFree r n) : 0 < n :=
  Nat.pos_of_ne_zero (rfree_ne_zero h)

theorem rfree_one {r : ℕ} (hr : 1 ≤ r) : RFree r 1 := by
  intro k hk
  exact isUnit_of_dvd_one ((dvd_pow_self k (by omega : r ≠ 0)).trans hk)

theorem rfree_of_prime {r p : ℕ} (hr : 2 ≤ r) (hp : p.Prime) : RFree r p := by
  intro k hk
  have hkp : k ∣ p := (dvd_pow_self k (by omega : r ≠ 0)).trans hk
  rcases hp.eq_one_or_self_of_dvd k hkp with rfl | rfl
  · exact isUnit_one
  · exfalso
    have h2 : k ^ 2 ∣ k := (pow_dvd_pow k hr).trans hk
    have hle : k ^ 2 ≤ k := Nat.le_of_dvd hp.pos h2
    have hp2 := hp.two_le
    nlinarith

theorem rfree_iff_factorization_lt {r n : ℕ} (hr : 1 ≤ r) (hn : n ≠ 0) :
    RFree r n ↔ ∀ p : ℕ, n.factorization p < r := by
  constructor
  · intro h p
    by_contra hge
    push Not at hge
    have hpos : 0 < n.factorization p := lt_of_lt_of_le (by omega) hge
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hpos.ne')
    have hdvd : p ^ r ∣ n := (hp.pow_dvd_iff_le_factorization hn).mpr hge
    exact hp.not_isUnit (h p hdvd)
  · intro hlt k hk
    by_contra hnu
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega : r ≠ 0)] at hk
      exact hn (zero_dvd_iff.mp hk)
    have hk1 : k ≠ 1 := fun h1 ↦ hnu (h1 ▸ isUnit_one)
    obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
    have hpr : p ^ r ∣ n := (pow_dvd_pow_of_dvd hpk r).trans hk
    have hle : r ≤ n.factorization p := (hp.pow_dvd_iff_le_factorization hn).mp hpr
    exact not_lt_of_ge hle (hlt p)

theorem rfree_mul_of_coprime {r a b : ℕ} (hr : 1 ≤ r) (ha : RFree r a) (hb : RFree r b)
    (hcop : a.Coprime b) : RFree r (a * b) := by
  have ha0 : a ≠ 0 := rfree_ne_zero ha
  have hb0 : b ≠ 0 := rfree_ne_zero hb
  rw [rfree_iff_factorization_lt hr (mul_ne_zero ha0 hb0)]
  rw [rfree_iff_factorization_lt hr ha0] at ha
  rw [rfree_iff_factorization_lt hr hb0] at hb
  intro p
  rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply]
  by_cases hpa : a.factorization p = 0
  · rw [hpa, zero_add]; exact hb p
  · have hprime : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr hpa)
    have hda : p ∣ a := (hprime.dvd_iff_one_le_factorization ha0).mpr (Nat.pos_of_ne_zero hpa)
    have hnb : ¬ p ∣ b := fun hdb ↦ hprime.not_isUnit (isUnit_of_dvd_one (hcop ▸ Nat.dvd_gcd hda hdb))
    have hpb : b.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnb
    rw [hpb, add_zero]; exact ha p

/-- Unique factorization of every positive natural number into an `r`-th power
and an `r`-free core. -/
theorem rfree_factorization {r : ℕ} (hr : 1 ≤ r) :
    ∀ n : ℕ, 0 < n → ∃ c : Core r, ∃ m : ℕ, 0 < m ∧ m ^ r * c.val = n := by
  by_cases hr1 : r = 1
  · subst hr1
    intro n hn
    exact ⟨⟨1, rfree_one le_rfl⟩, n, hn, by simp⟩
  have hr2 : 2 ≤ r := by omega
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro hn
    by_cases hrf : RFree r n
    · exact ⟨⟨n, hrf⟩, 1, one_pos, by simp⟩
    · unfold RFree at hrf
      push Not at hrf
      obtain ⟨k, ⟨q, hq⟩, hnu⟩ := hrf
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [zero_pow (by omega : r ≠ 0), zero_mul] at hq
        omega
      have hk1 : k ≠ 1 := fun h1 ↦ hnu (h1 ▸ isUnit_one)
      have hk2 : 2 ≤ k := by omega
      have hkr_gt : 1 < k ^ r := one_lt_pow₀ (by omega) (by omega : r ≠ 0)
      have hq_pos : 0 < q := by
        by_contra hq0
        have : q = 0 := by omega
        subst this; simp at hq; omega
      have hq_lt : q < n := by nlinarith
      obtain ⟨c, m, hm, hmc⟩ := ih q hq_lt hq_pos
      refine ⟨c, k * m, Nat.mul_pos (by omega) hm, ?_⟩
      rw [mul_pow, mul_assoc, hmc, hq]

theorem rfree_factor_unique {r : ℕ} (hr : 1 ≤ r) {c₁ c₂ : Core r} {m₁ m₂ : ℕ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (heq : m₁ ^ r * c₁.val = m₂ ^ r * c₂.val) :
    c₁ = c₂ ∧ m₁ = m₂ := by
  have hc₁0 : c₁.val ≠ 0 := rfree_ne_zero c₁.property
  have hc₂0 : c₂.val ≠ 0 := rfree_ne_zero c₂.property
  have hlt₁ := (rfree_iff_factorization_lt hr hc₁0).mp c₁.property
  have hlt₂ := (rfree_iff_factorization_lt hr hc₂0).mp c₂.property
  have hfac : ∀ p : ℕ,
      r * m₁.factorization p + c₁.val.factorization p =
      r * m₂.factorization p + c₂.val.factorization p := by
    intro p
    have h := congrArg (fun x : ℕ ↦ x.factorization p) heq
    rw [Nat.factorization_mul (pow_ne_zero r hm₁.ne') hc₁0,
        Nat.factorization_mul (pow_ne_zero r hm₂.ne') hc₂0] at h
    simpa [Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply] using h
  have hcore_fac : c₁.val.factorization = c₂.val.factorization := by
    ext p
    have h1 := hfac p
    have h2 := hlt₁ p
    have h3 := hlt₂ p
    have hdiv := congrArg (· % r) h1
    simp only [Nat.mul_add_mod] at hdiv
    rwa [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3] at hdiv
  have hc_eq : c₁.val = c₂.val := Nat.eq_of_factorization_eq hc₁0 hc₂0 (fun p ↦ by rw [hcore_fac])
  have hm_eq : m₁ = m₂ := by
    apply Nat.eq_of_factorization_eq hm₁.ne' hm₂.ne'
    intro p
    have h1 := hfac p
    rw [hc_eq] at h1
    have hmul : r * m₁.factorization p = r * m₂.factorization p := Nat.add_right_cancel h1
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < r) hmul
  exact ⟨Subtype.ext hc_eq, hm_eq⟩

def rFreeCore (r : ℕ) (hr : 1 ≤ r) (n : ℕ+) : Core r :=
  (rfree_factorization hr n.val n.property).choose

def rFreeRoot (r : ℕ) (hr : 1 ≤ r) (n : ℕ+) : ℕ :=
  (rfree_factorization hr n.val n.property).choose_spec.choose

theorem rFreeRoot_pos (r : ℕ) (hr : 1 ≤ r) (n : ℕ+) : 0 < rFreeRoot r hr n :=
  (rfree_factorization hr n.val n.property).choose_spec.choose_spec.1

theorem rFreeRoot_pow_mul_core (r : ℕ) (hr : 1 ≤ r) (n : ℕ+) :
    (rFreeRoot r hr n) ^ r * (rFreeCore r hr n).val = n.val :=
  (rfree_factorization hr n.val n.property).choose_spec.choose_spec.2

/-! ### Elementary `|f(0)|^s = u^m` + Bézout Irreducibility of `X^s - u` over `ℚ` -/

private theorem exists_nat_pow_of_rat_pow {p u : ℕ} (hp : 1 ≤ p) {v : ℚ}
    (hv : v ^ p = (u : ℚ)) : ∃ w : ℕ, w ^ p = u := by
  have h1 : ((v.num : ℚ) / (v.den : ℚ)) ^ p = (u : ℚ) := by rwa [Rat.num_div_den]
  have hden0 : (v.den : ℚ) ≠ 0 := by exact_mod_cast v.den_nz
  rw [div_pow, div_eq_iff (pow_ne_zero p hden0)] at h1
  have hint : v.num ^ p = (u : ℤ) * (v.den : ℤ) ^ p := by exact_mod_cast h1
  have hnat : v.num.natAbs ^ p = u * v.den ^ p := by
    have := congrArg Int.natAbs hint
    simpa [Int.natAbs_pow, Int.natAbs_mul] using this
  have hcop : (v.num.natAbs ^ p).Coprime (v.den ^ p) := v.reduced.pow p p
  have hdvd : v.den ^ p ∣ v.num.natAbs ^ p := ⟨u, by rw [hnat, mul_comm]⟩
  have hdenp : v.den ^ p = 1 := Nat.eq_one_of_dvd_one (hcop.symm ▸ Nat.dvd_gcd (dvd_refl _) hdvd)
  have hden1 : v.den = 1 := by
    have hvd : v.den ∣ 1 := by
      rw [← hdenp]
      exact dvd_pow_self v.den (by omega : p ≠ 0)
    exact Nat.eq_one_of_dvd_one hvd
  refine ⟨v.num.natAbs, ?_⟩
  rw [hnat, hden1, one_pow, mul_one]

private theorem factor_const_pow_eq {s u : ℕ}
    {f : Polynomial ℚ} (hmon : f.Monic) (hdvd : f ∣ X ^ s - C (u : ℚ)) :
    |f.coeff 0| ^ s = (u : ℚ) ^ f.natDegree := by
  let ι : ℚ →+* ℂ := algebraMap ℚ ℂ
  let fc : Polynomial ℂ := f.map ι
  have hfc_mon : fc.Monic := hmon.map ι
  have hfc_deg : fc.natDegree = f.natDegree := hmon.natDegree_map ι
  have hcard : fc.roots.card = f.natDegree := by
    rw [← hfc_deg]
    exact (IsAlgClosed.splits fc).natDegree_eq_card_roots.symm
  have hprod : (fc.roots.map fun α ↦ X - C α).prod = fc :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hfc_mon (hcard.trans hfc_deg.symm)
  have heval0 : fc.eval 0 = (fc.roots.map fun α ↦ -α).prod := by
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro α _
    simp
  have hfc_dvd : fc ∣ X ^ s - C (u : ℂ) := by
    have hmap := Polynomial.map_dvd ι hdvd
    simpa [fc, ι] using hmap
  have hnorm_root : ∀ α ∈ fc.roots, ‖α‖ ^ s = (u : ℝ) := by
    intro α hα
    have hroot_f : fc.IsRoot α := Polynomial.isRoot_of_mem_roots hα
    have hroot_P : (X ^ s - C (u : ℂ)).IsRoot α := by
      obtain ⟨q, hq⟩ := hfc_dvd
      rw [Polynomial.IsRoot, hq, Polynomial.eval_mul, hroot_f, zero_mul]
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, sub_eq_zero] at hroot_P
    rw [← norm_pow, hroot_P, Complex.norm_natCast]
  have hreal : ((|f.coeff 0| : ℚ) : ℝ) ^ s = ((u : ℚ) : ℝ) ^ f.natDegree := by
    have h0 : fc.eval 0 = ((f.coeff 0 : ℚ) : ℂ) := by
      simp [fc, ι, Polynomial.eval_map, Polynomial.eval₂_at_zero]
    have hnorm0 : ‖fc.eval 0‖ = ((|f.coeff 0| : ℚ) : ℝ) := by
      rw [h0, Complex.norm_ratCast]
      push_cast
      rfl
    rw [← hnorm0, heval0, Multiset.norm_prod, Multiset.map_map, ← Multiset.prod_map_pow]
    have hmap_eq : (fc.roots.map fun α ↦ ‖-α‖ ^ s) = fc.roots.map fun _ ↦ (u : ℝ) := by
      apply Multiset.map_congr rfl
      intro α hα
      rw [norm_neg, hnorm_root α hα]
    change (fc.roots.map fun α ↦ ‖-α‖ ^ s).prod = _
    rw [hmap_eq, Multiset.map_const', Multiset.prod_replicate, hcard]
    simp
  exact_mod_cast hreal

/-- Elementary irreducibility of `X^s - u` over `ℚ` for positive integers `u ≥ 1`
that are not `p`-th powers for any prime `p ∣ s`. -/
theorem irreducible_X_pow_sub_C_rat {s u : ℕ} (hs : 1 ≤ s) (hu : 1 ≤ u)
    (hno : ∀ p : ℕ, p.Prime → p ∣ s → ¬ ∃ w : ℕ, w ^ p = u) :
    Irreducible (X ^ s - C (u : ℚ)) := by
  have hPdeg : (X ^ s - C (u : ℚ)).natDegree = s := Polynomial.natDegree_X_pow_sub_C (u : ℚ)
  have hPmon : (X ^ s - C (u : ℚ)).Monic := Polynomial.monic_X_pow_sub_C (u : ℚ) (by omega)
  have hPnu : ¬ IsUnit (X ^ s - C (u : ℚ)) := by
    intro h
    have := Polynomial.natDegree_eq_zero_of_isUnit h
    omega
  rw [irreducible_iff]
  refine ⟨hPnu, fun a b hab ↦ ?_⟩
  by_contra hboth
  push Not at hboth
  obtain ⟨hanu, hbnu⟩ := hboth
  have ha0 : a ≠ 0 := by rintro rfl; simp at hab; exact hPmon.ne_zero hab
  have hb0 : b ≠ 0 := by rintro rfl; simp at hab; exact hPmon.ne_zero hab
  have hadeg_pos : 0 < a.natDegree := by
    by_contra h0
    have ha_deg : a.natDegree = 0 := by omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero ha_deg] at ha0 hanu
    have hc0 : a.coeff 0 ≠ 0 := by simpa using ha0
    exact hanu (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
  have hbdeg_pos : 0 < b.natDegree := by
    by_contra h0
    have hb_deg : b.natDegree = 0 := by omega
    rw [Polynomial.eq_C_of_natDegree_eq_zero hb_deg] at hb0 hbnu
    have hc0 : b.coeff 0 ≠ 0 := by simpa using hb0
    exact hbnu (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc0))
  have hsum_deg : a.natDegree + b.natDegree = s := by
    rw [← hPdeg, hab, Polynomial.natDegree_mul ha0 hb0]
  let f : Polynomial ℚ := a * C a.leadingCoeff⁻¹
  have hf_mon : f.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
    exact mul_inv_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr ha0)
  have hf_deg : f.natDegree = a.natDegree := by
    rw [Polynomial.natDegree_mul ha0 (Polynomial.C_ne_zero.mpr (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr ha0))),
        Polynomial.natDegree_C, add_zero]
  have hf_dvd : f ∣ X ^ s - C (u : ℚ) := by
    refine ⟨C a.leadingCoeff * b, ?_⟩
    rw [hab]
    dsimp [f]
    have hlc : a.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ha0
    calc a * b = a * (C (a.leadingCoeff⁻¹ * a.leadingCoeff) * b) := by
          rw [inv_mul_cancel₀ hlc, map_one, one_mul]
      _ = a * C a.leadingCoeff⁻¹ * (C a.leadingCoeff * b) := by
          rw [map_mul]; ring
  let m := f.natDegree
  have hm_pos : 0 < m := by omega
  have hm_lt : m < s := by omega
  let c : ℚ := |f.coeff 0|
  have hcs : c ^ s = (u : ℚ) ^ m := factor_const_pow_eq hf_mon hf_dvd
  have huq_pos : (0 : ℚ) < u := by exact_mod_cast hu
  have hc_pos : 0 < c := by
    have hcn : 0 ≤ c := abs_nonneg _
    rcases hcn.eq_or_lt with h0 | hpos
    · exfalso
      rw [← h0, zero_pow (by omega : s ≠ 0)] at hcs
      exact (pow_pos huq_pos m).ne hcs
    · exact hpos
  let g := Nat.gcd m s
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left s hm_pos
  let a' := m / g
  let q := s / g
  have hga : g * a' = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m s)
  have hgq : g * q = s := Nat.mul_div_cancel' (Nat.gcd_dvd_right m s)
  have hq_dvd_s : q ∣ s := ⟨g, by rw [mul_comm, hgq]⟩
  have hcop : a'.Coprime q := Nat.coprime_div_gcd_div_gcd hg_pos
  have hq_pos : 0 < q := by
    by_contra hq0
    have hqz : q = 0 := Nat.eq_zero_of_not_pos hq0
    rw [hqz, mul_zero] at hgq
    omega
  have hq_gt_one : 1 < q := by
    by_contra hqle
    have hq1 : q = 1 := by omega
    rw [hq1, mul_one] at hgq
    have hsm : s ∣ m := hgq ▸ Nat.gcd_dvd_left m s
    have := Nat.le_of_dvd hm_pos hsm
    omega
  have hcq_eq : c ^ q = (u : ℚ) ^ a' := by
    have hpow : (c ^ q) ^ g = ((u : ℚ) ^ a') ^ g := by
      rw [← pow_mul, ← pow_mul, mul_comm q g, hgq, mul_comm a' g, hga, hcs]
    exact (pow_left_inj₀ (pow_nonneg hc_pos.le q) (pow_nonneg huq_pos.le a') hg_pos.ne').mp hpow
  -- Bézout combination gives an exact rational `q`-th root of `u`.
  let x : ℤ := Nat.gcdA a' q
  let y : ℤ := Nat.gcdB a' q
  have hbez : (1 : ℤ) = (a' : ℤ) * x + (q : ℤ) * y := by
    have h := Nat.gcd_eq_gcd_ab a' q
    rw [hcop.gcd_eq_one] at h
    exact_mod_cast h
  let w : ℚ := c ^ x * (u : ℚ) ^ y
  have hwq : w ^ q = (u : ℚ) := by
    calc w ^ q
        = (c ^ x) ^ (q : ℤ) * ((u : ℚ) ^ y) ^ (q : ℤ) := by rw [mul_pow, zpow_natCast, zpow_natCast]
      _ = (c ^ (q : ℤ)) ^ x * (u : ℚ) ^ (y * (q : ℤ)) := by
            rw [← zpow_mul, ← zpow_mul, mul_comm x (q : ℤ), zpow_mul]
      _ = ((u : ℚ) ^ a') ^ x * (u : ℚ) ^ ((q : ℤ) * y) := by
            rw [zpow_natCast, hcq_eq, mul_comm y (q : ℤ)]
      _ = (u : ℚ) ^ ((a' : ℤ) * x) * (u : ℚ) ^ ((q : ℤ) * y) := by
            rw [← zpow_natCast (u : ℚ) a', ← zpow_mul]
      _ = (u : ℚ) ^ ((a' : ℤ) * x + (q : ℤ) * y) := (zpow_add₀ huq_pos.ne' _ _).symm
      _ = (u : ℚ) ^ (1 : ℤ) := by rw [← hbez]
      _ = (u : ℚ) := zpow_one _
  obtain ⟨p, hp, hpq⟩ := Nat.exists_prime_and_dvd (by omega : q ≠ 1)
  have hps : p ∣ s := dvd_trans hpq hq_dvd_s
  obtain ⟨t, ht⟩ := hpq
  have hwp : (w ^ t) ^ p = (u : ℚ) := by rw [← pow_mul, mul_comm t p, ← ht, hwq]
  exact hno p hp hps (exists_nat_pow_of_rat_pow (by have := hp.two_le; omega) hwp)

/-! ### Normalized-Trace Vanishing and All-`r` Besicovitch Linear Independence -/

private abbrev AlgReal := algebraicClosure ℚ ℝ

private def rRootAlg (r : ℕ) (hr : 1 ≤ r) (n : ℕ) : AlgReal :=
  ⟨(n : ℝ) ^ (1 / (r : ℝ)), mem_algebraicClosure_iff'.mpr
    ⟨X ^ r - C (n : ℚ), Polynomial.monic_X_pow_sub_C _ (by omega), by
      have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
      have hpow : ((n : ℝ) ^ (r : ℝ)⁻¹) ^ r = (n : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n),
            inv_mul_cancel₀ hr0, Real.rpow_one]
      simp [hpow]⟩⟩

private theorem normalizedTrace_rRoot_eq_zero {r N : ℕ} (hr : 2 ≤ r) (hN : 1 ≤ N)
    (hnot : ¬ ∃ m : ℕ, m ^ r = N) :
    normalizedTrace ℚ AlgReal (rRootAlg r (by omega) N) = 0 := by
  classical
  let S : Finset ℕ := (Nat.divisors r).filter (fun k ↦ ∃ u : ℕ, u ^ k = N)
  have h1S : 1 ∈ S := by
    simp only [S, Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd r, by omega⟩, ⟨N, pow_one N⟩⟩
  let k := S.max' ⟨1, h1S⟩
  have hkS : k ∈ S := Finset.max'_mem S ⟨1, h1S⟩
  have hk_dvd : k ∣ r := (Nat.mem_divisors.mp (Finset.mem_filter.mp hkS).1).1
  obtain ⟨u, hu_eq⟩ := (Finset.mem_filter.mp hkS).2
  have hk_pos : 0 < k := Nat.pos_of_dvd_of_pos hk_dvd (by omega)
  let s := r / k
  have hks : k * s = r := Nat.mul_div_cancel' hk_dvd
  have hs_pos : 0 < s := by
    by_contra h0
    have hsz : s = 0 := Nat.eq_zero_of_not_pos h0
    rw [hsz, mul_zero] at hks
    omega
  have hs_ge2 : 2 ≤ s := by
    by_contra hlt
    have hs1 : s = 1 := by omega
    rw [hs1, mul_one] at hks
    exact hnot ⟨u, hks ▸ hu_eq⟩
  have hu_pos : 1 ≤ u := by
    by_contra h0
    have : u = 0 := by omega
    rw [this, zero_pow hk_pos.ne'] at hu_eq
    omega
  have hno_prime : ∀ p : ℕ, p.Prime → p ∣ s → ¬ ∃ w : ℕ, w ^ p = u := by
    intro p hp hps ⟨w, hw⟩
    have hpk_dvd : k * p ∣ r := by
      obtain ⟨t, ht⟩ := hps
      exact ⟨t, by rw [mul_assoc, ← ht, hks]⟩
    have hpk_mem : k * p ∈ S := by
      simp only [S, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨hpk_dvd, by omega⟩, ⟨w, by rw [mul_comm, pow_mul, hw, hu_eq]⟩⟩
    have hle : k * p ≤ k := Finset.le_max' S (k * p) hpk_mem
    have hp2 := hp.two_le
    nlinarith
  have hirr : Irreducible (X ^ s - C (u : ℚ)) :=
    irreducible_X_pow_sub_C_rat (by omega) hu_pos hno_prime
  have hmon : (X ^ s - C (u : ℚ)).Monic := Polynomial.monic_X_pow_sub_C _ (by omega)
  have hroot : aeval (rRootAlg r (by omega) N) (X ^ s - C (u : ℚ)) = 0 := by
    apply Subtype.ext
    have hpow : ((N : ℝ) ^ (r : ℝ)⁻¹) ^ s = (u : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N), ← hu_eq]
      have hsr : (r : ℝ)⁻¹ * (s : ℝ) = (k : ℝ)⁻¹ := by
        have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk_pos.ne'
        have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (show s ≠ 0 by omega)
        have hr_eq : (r : ℝ) = (k : ℝ) * (s : ℝ) := by exact_mod_cast hks.symm
        rw [hr_eq]; field_simp
      rw [hsr, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg u)]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk_pos.ne'
      rw [mul_inv_cancel₀ hk0, Real.rpow_one]
    simp [rRootAlg, hpow]
  rw [normalizedTrace_minpoly, ← minpoly.eq_of_irreducible_of_monic hirr hroot hmon]
  have hnext : (X ^ s - C (u : ℚ)).nextCoeff = 0 := by
    rw [Polynomial.nextCoeff, Polynomial.natDegree_X_pow_sub_C]
    simp only [show s ≠ 0 by omega, ↓reduceIte, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      Polynomial.coeff_C]
    have h1 : s - 1 ≠ s := by omega
    have h2 : s - 1 ≠ 0 := by omega
    simp [h1, h2]
  rw [hnext]
  simp

private theorem rfree_twist_not_rpow {r : ℕ} (hr : 2 ≤ r) {b₁ b₂ : Core r} (hne : b₁ ≠ b₂) :
    ¬ ∃ m : ℕ, m ^ r = b₁.val ^ (r - 1) * b₂.val := by
  rintro ⟨m, hm⟩
  have hb₁0 : b₁.val ≠ 0 := rfree_ne_zero b₁.property
  have hb₂0 : b₂.val ≠ 0 := rfree_ne_zero b₂.property
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega : r ≠ 0)] at hm
    exact mul_ne_zero (pow_ne_zero _ hb₁0) hb₂0 hm.symm
  have hlt₁ := (rfree_iff_factorization_lt (by omega) hb₁0).mp b₁.property
  have hlt₂ := (rfree_iff_factorization_lt (by omega) hb₂0).mp b₂.property
  apply hne
  apply Subtype.ext
  apply Nat.eq_of_factorization_eq hb₁0 hb₂0
  intro p
  have hfac := congrArg (fun x : ℕ ↦ x.factorization p) hm
  rw [Nat.factorization_pow, Nat.factorization_mul (pow_ne_zero _ hb₁0) hb₂0,
      Nat.factorization_pow] at hfac
  simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul] at hfac
  have h1 := hlt₁ p
  have h2 := hlt₂ p
  have hsum : r * m.factorization p + b₁.val.factorization p =
      r * b₁.val.factorization p + b₂.val.factorization p := by
    have : (r - 1) * b₁.val.factorization p + b₁.val.factorization p = r * b₁.val.factorization p := by
      calc (r - 1) * b₁.val.factorization p + b₁.val.factorization p
          = (r - 1 + 1) * b₁.val.factorization p := by ring
        _ = r * b₁.val.factorization p := by rw [Nat.sub_add_cancel (by omega)]
    linarith
  have hmod := congrArg (· % r) hsum
  simp only [Nat.mul_add_mod] at hmod
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hmod

/-- **Besicovitch's Theorem (1940) for all `r ≥ 2`**, proved unconditionally from
Mathlib via the elementary normalized-trace twist. -/
theorem besicovitch_rfree_linearIndependent (r : ℕ) (hr : 2 ≤ r) :
    LinearIndependent ℚ (fun b : Core r ↦ (b.val : ℝ) ^ (1 / (r : ℝ))) := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum j₀ hj₀
  have hb0_pos : 0 < (j₀.val : ℝ) := by exact_mod_cast rfree_pos j₀.property
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  let twist : ℝ := (j₀.val : ℝ) ^ (((r - 1 : ℕ) : ℝ) / (r : ℝ))
  have hmul : ∑ j ∈ s, (c j : ℝ) * (((j₀.val ^ (r - 1) * j.val : ℕ) : ℝ) ^ (1 / (r : ℝ))) = 0 := by
    have h0 := congrArg (· * twist) hsum
    rw [zero_mul, Finset.sum_mul] at h0
    refine (Finset.sum_congr rfl fun j _ ↦ ?_).trans h0
    have hpow : (((j₀.val ^ (r - 1) * j.val : ℕ) : ℝ) ^ (1 / (r : ℝ))) =
        (j.val : ℝ) ^ (1 / (r : ℝ)) * twist := by
      push_cast
      rw [Real.mul_rpow (pow_nonneg hb0_pos.le _) (Nat.cast_nonneg _),
          ← Real.rpow_natCast, ← Real.rpow_mul hb0_pos.le]
      dsimp [twist]
      rw [mul_one_div, mul_comm]
    rw [hpow, Rat.smul_def]
    ring
  have hdiag : (((j₀.val ^ (r - 1) * j₀.val : ℕ) : ℝ) ^ (1 / (r : ℝ))) = (j₀.val : ℝ) := by
    have hpow_nat : j₀.val ^ (r - 1) * j₀.val = j₀.val ^ r := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    rw [hpow_nat, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hb0_pos.le,
        mul_one_div_cancel hr0, Real.rpow_one]
  have hmul' : (c j₀ : ℝ) * (j₀.val : ℝ) +
      ∑ j ∈ s.erase j₀, (c j : ℝ) * (((j₀.val ^ (r - 1) * j.val : ℕ) : ℝ) ^ (1 / (r : ℝ))) = 0 := by
    rw [← hdiag, Finset.add_sum_erase s
      (fun j ↦ (c j : ℝ) * (((j₀.val ^ (r - 1) * j.val : ℕ) : ℝ) ^ (1 / (r : ℝ)))) hj₀]
    exact hmul
  have hAlg : algebraMap ℚ AlgReal (c j₀ * (j₀.val : ℚ)) +
      ∑ j ∈ s.erase j₀, c j • rRootAlg r (by omega) (j₀.val ^ (r - 1) * j.val) = 0 := by
    apply Subtype.ext
    simpa [Algebra.smul_def, rRootAlg] using hmul'
  have htr := congrArg (normalizedTrace ℚ AlgReal) hAlg
  simp only [map_add, map_sum, map_smul, map_zero, normalizedTrace_algebraMap_apply_eq_self] at htr
  have hrest : ∑ j ∈ s.erase j₀,
      c j • normalizedTrace ℚ AlgReal (rRootAlg r (by omega) (j₀.val ^ (r - 1) * j.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hne : j₀ ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hN : 1 ≤ j₀.val ^ (r - 1) * j.val :=
      Nat.mul_pos (pow_pos (rfree_pos j₀.property) _) (rfree_pos j.property)
    rw [normalizedTrace_rRoot_eq_zero hr hN (rfree_twist_not_rpow hr hne), smul_zero]
  rw [hrest, add_zero] at htr
  have hj₀q : (j₀.val : ℚ) ≠ 0 := by exact_mod_cast rfree_ne_zero j₀.property
  exact (mul_eq_zero.mp htr).resolve_right hj₀q

/-! ### All-`d` Actions, Frequency Lattice, and Zero-Tilt Injectivity (`d ≥ 3`) -/

/-- The dimensionless mode action `n^(d / (d - 1))` for all `d ≥ 3`. -/
def rAction (d n : ℕ) : ℝ := (n : ℝ) ^ ((d : ℝ) / ((d - 1 : ℕ) : ℝ))

theorem rAction_eq_mul_rpow {d : ℕ} (hd : 3 ≤ d) (n : ℕ) :
    rAction d n = (n : ℝ) * (n : ℝ) ^ (1 / ((d - 1 : ℕ) : ℝ)) := by
  by_cases hn : n = 0
  · subst hn
    have hpos1 : (0 : ℝ) < (d : ℝ) / ((d - 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
      positivity
    simp [rAction, Real.zero_rpow hpos1.ne']
  · have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hsplit : (d : ℝ) / ((d - 1 : ℕ) : ℝ) = 1 + 1 / ((d - 1 : ℕ) : ℝ) := by
      have hr0 : ((d - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show d - 1 ≠ 0 by omega)
      have hd_eq : (d : ℝ) = ((d - 1 : ℕ) : ℝ) + 1 := by exact_mod_cast (show d = d - 1 + 1 by omega)
      rw [hd_eq, add_div, div_self hr0]
    rw [rAction, hsplit, Real.rpow_add hpos, Real.rpow_one]

theorem rAction_three (n : ℕ) : rAction 3 n = (n : ℝ) * Real.sqrt n := by
  rw [rAction_eq_mul_rpow (by decide : 3 ≤ 3) n, Real.sqrt_eq_rpow]
  norm_num

/-- Unconditional `ℚ`-linear independence of the `(d-1)`-free actions `b^(d/(d-1))`
for EVERY integer `d ≥ 3`. -/
theorem rAction_linearIndependent (d : ℕ) (hd : 3 ≤ d) :
    LinearIndependent ℚ (fun b : Core (d - 1) ↦ rAction d b.val) := by
  have hbase := besicovitch_rfree_linearIndependent (d - 1) (by omega)
  rw [linearIndependent_iff'] at hbase ⊢
  intro s c hsum b hb
  have hsum' : ∑ i ∈ s, (c i * (i.val : ℚ)) • (i.val : ℝ) ^ (1 / ((d - 1 : ℕ) : ℝ)) = 0 := by
    refine (Finset.sum_congr rfl fun i _ ↦ ?_).trans hsum
    rw [rAction_eq_mul_rpow hd i.val, Rat.smul_def, Rat.smul_def, Rat.cast_mul, Rat.cast_natCast]
    ring
  have hmul := hbase s (fun i ↦ c i * (i.val : ℚ)) hsum' b hb
  have hb0 : (b.val : ℚ) ≠ 0 := by exact_mod_cast rfree_ne_zero b.property
  exact (mul_eq_zero.mp hmul).resolve_right hb0

abbrev ActionKey (d : ℕ) := Core (d - 1) →₀ ℕ

/-- The additive frequency map `(Core (d-1) →₀ ℕ) →+ ℝ` sending each `(d-1)`-free
core `b` to `b^(d/(d-1))`. -/
def readKey (d : ℕ) : ActionKey d →+ ℝ :=
  Finsupp.liftAddHom (fun b : Core (d - 1) ↦ multiplesHom ℝ (rAction d b.val))

theorem readKey_single (d : ℕ) (b : Core (d - 1)) (m : ℕ) :
    readKey d (Finsupp.single b m) = (m : ℝ) * rAction d b.val := by
  simp [readKey]

/-- Exact injectivity of `readKey d` for ALL `d ≥ 3` (zero transcendental tilt!). -/
theorem readKey_injective (d : ℕ) (hd : 3 ≤ d) : Function.Injective (readKey d) := by
  let rat (k : ActionKey d) : Core (d - 1) →₀ ℚ := k.mapRange Nat.cast (by simp)
  let L := Finsupp.linearCombination ℚ (fun b : Core (d - 1) ↦ rAction d b.val)
  have hrepr (k : ActionKey d) : L (rat k) = readKey d k := by
    induction k using Finsupp.induction with
    | zero => simp [rat, L]
    | single_add b v f _ _ ih =>
      have ha : rat (Finsupp.single b v + f) = Finsupp.single b (v : ℚ) + rat f := by
        classical
        ext i
        by_cases hi : b = i <;> simp [rat, hi]
      rw [ha, map_add, ih, map_add]
      congr 1
      simp [L, readKey, Algebra.smul_def]
  intro a b he
  have hlin := (rAction_linearIndependent d hd).finsuppLinearCombination_injective
    ((hrepr a).trans (he.trans (hrepr b).symm))
  ext i
  exact_mod_cast (show (a i : ℚ) = (b i : ℚ) from DFunLike.congr_fun hlin i)

/-- Injectivity of the complex extreme-ray frequency map `k ↦ (readKey d k : ℂ) * A`
for ANY nonzero complex direction `A ≠ 0` — ZERO transcendental tilt required! -/
theorem readKey_complex_injective (d : ℕ) (hd : 3 ≤ d) {A : ℂ} (hA : A ≠ 0) :
    Function.Injective (fun k : ActionKey d ↦ (readKey d k : ℂ) * A) := by
  intro a b he
  exact readKey_injective d hd (Complex.ofReal_injective (mul_right_cancel₀ hA he))

/-- The exact frequency key of mode `n ∈ ℕ+`: if `n = m^(d-1) * c`, then
`n^(d/(d-1)) = m^d * c^(d/(d-1))`. -/
def modeKey (d : ℕ) (hd : 3 ≤ d) (n : ℕ+) : ActionKey d :=
  Finsupp.single (rFreeCore (d - 1) (by omega) n) ((rFreeRoot (d - 1) (by omega) n) ^ d)

theorem readKey_modeKey (d : ℕ) (hd : 3 ≤ d) (n : ℕ+) :
    readKey d (modeKey d hd n) = rAction d n.val := by
  rw [modeKey, readKey_single]
  let c := rFreeCore (d - 1) (by omega) n
  let m := rFreeRoot (d - 1) (by omega) n
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hc0 : 0 ≤ (c.val : ℝ) := Nat.cast_nonneg c.val
  have hfac : (m ^ (d - 1) * c.val : ℕ) = n.val := rFreeRoot_pow_mul_core (d - 1) (by omega) n
  have hnat : rAction d n.val = (m ^ d : ℝ) * rAction d c.val := by
    rw [← hfac, rAction, Nat.cast_mul, Nat.cast_pow,
        Real.mul_rpow (pow_nonneg hm0 _) hc0, ← Real.rpow_natCast, ← Real.rpow_mul hm0]
    have hr0 : ((d - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show d - 1 ≠ 0 by omega)
    rw [mul_div_cancel₀ _ hr0, Real.rpow_natCast]
    rfl
  rw [hnat]
  simp [c, m]

theorem modeKey_of_core (d : ℕ) (hd : 3 ≤ d) (b : Core (d - 1)) :
    modeKey d hd ⟨b.val, rfree_pos b.property⟩ = Finsupp.single b 1 := by
  let n : ℕ+ := ⟨b.val, rfree_pos b.property⟩
  have huniq := rfree_factor_unique (r := d - 1) (by omega)
    (rFreeRoot_pos (d - 1) (by omega) n) one_pos
    (by simpa [n] using rFreeRoot_pow_mul_core (d - 1) (by omega) n)
  simp [modeKey, n, huniq.1, huniq.2]

/-- Uniqueness of fundamental unit coordinates: `modeKey d hd n = Finsupp.single b 1`
iff `n = b`! -/
theorem modeKey_eq_single_one (d : ℕ) (hd : 3 ≤ d) (n : ℕ+) (b : Core (d - 1)) :
    modeKey d hd n = Finsupp.single b 1 ↔ n.val = b.val := by
  constructor
  · intro hk
    have hval := DFunLike.congr_fun hk (rFreeCore (d - 1) (by omega) n)
    simp only [modeKey, Finsupp.single_eq_same, Finsupp.single_apply] at hval
    have hm_pos : 0 < rFreeRoot (d - 1) (by omega) n := rFreeRoot_pos (d - 1) (by omega) n
    by_cases hbc : b = rFreeCore (d - 1) (by omega) n
    · simp only [hbc, ↓reduceIte] at hval
      have hm1 : rFreeRoot (d - 1) (by omega) n = 1 := by
        by_contra hne
        have h2 : 2 ≤ rFreeRoot (d - 1) (by omega) n := by omega
        have : 1 < (rFreeRoot (d - 1) (by omega) n) ^ d := one_lt_pow₀ (by omega) (by omega)
        omega
      have hfac := rFreeRoot_pow_mul_core (d - 1) (by omega) n
      rw [hm1, one_pow, one_mul, ← hbc] at hfac
      exact hfac.symm
    · simp only [hbc, ↓reduceIte] at hval
      exact absurd hval (pow_ne_zero d hm_pos.ne')
  · intro hnb
    have hpn : n = ⟨b.val, rfree_pos b.property⟩ := Subtype.ext hnb
    rw [hpn]
    exact modeKey_of_core d hd b

/-- The scaled root-lattice map `(Core r →₀ ℕ) →+ ℝ` sending `b ↦ b^(1/r)`,
used for multi-dilation frequency marking. -/
def readRootKey (r : ℕ) : (Core r →₀ ℕ) →+ ℝ :=
  Finsupp.liftAddHom (fun b : Core r ↦ multiplesHom ℝ ((b.val : ℝ) ^ (1 / (r : ℝ))))

theorem readRootKey_single (r : ℕ) (b : Core r) (m : ℕ) :
    readRootKey r (Finsupp.single b m) = (m : ℝ) * (b.val : ℝ) ^ (1 / (r : ℝ)) := by
  simp [readRootKey]

theorem readRootKey_injective (r : ℕ) (hr : 2 ≤ r) : Function.Injective (readRootKey r) := by
  let rat (k : Core r →₀ ℕ) : Core r →₀ ℚ := k.mapRange Nat.cast (by simp)
  let L := Finsupp.linearCombination ℚ (fun b : Core r ↦ (b.val : ℝ) ^ (1 / (r : ℝ)))
  have hrepr (k : Core r →₀ ℕ) : L (rat k) = readRootKey r k := by
    induction k using Finsupp.induction with
    | zero => simp [rat, L]
    | single_add b v f _ _ ih =>
      have ha : rat (Finsupp.single b v + f) = Finsupp.single b (v : ℚ) + rat f := by
        classical
        ext i
        by_cases hi : b = i <;> simp [rat, hi]
      rw [ha, map_add, ih, map_add]
      congr 1
      simp [L, readRootKey, Algebra.smul_def]
  intro a b he
  have hlin := (besicovitch_rfree_linearIndependent r hr).finsuppLinearCombination_injective
    ((hrepr a).trans (he.trans (hrepr b).symm))
  ext i
  exact_mod_cast (show (a i : ℚ) = (b i : ℚ) from DFunLike.congr_fun hlin i)

end
end CubicTheta.AllD
