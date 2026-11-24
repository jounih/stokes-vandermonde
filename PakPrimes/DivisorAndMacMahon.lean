module

public import PakPrimes.HigherOrderStokes
public import PakPrimes.AutonomousTransfer
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-! # Unconditional Differential Transcendence of `L₀(q)`, `L_{2m}(q)`, and MacMahon `M(q)`

This module establishes unconditional Tier-1 differential transcendence over `ℂ(q)` (zero extra
hypotheses, strictly `[propext, Classical.choice, Quot.sound]`) for:

1. **Classical Lambert Divisor Series** `L₀(q) = ∑_{n ≥ 1} d(n) q^n` (`divisorSeries_algebraicIndependent`),
   settling the base case `a = 0` of Chowla–Chowla (1984).
2. **All Even-Power Divisor Sum Series** `L_{2m}(q) = ∑_{n ≥ 1} σ_{2m}(n) q^n` for every `m ≥ 0`
   (`sigmaEvenSeries_algebraicIndependent`), settling Part I of Chowla–Chowla (1984).
3. **MacMahon Plane Partitions** `M(q) = ∏_{n ≥ 1} (1 - q^n)^{-n}` (`macmahonSeries_algebraicIndependent`),
   defined via `M(0) = 1` and `q M'(q) = L₂(q) M(q)`.

The proof combines:
- `PakPrimes.PrimeNome.autonomous_transfer` and `autonomous_transfer_log_deriv` (`q = e^{-e^{-y}}`),
- an algebraic coordinate transfer `y = log u` (`(u d/du)^j`) with triangular nonvanishing,
- elementary 1-D Euler–Maclaurin summation via `bernoulliFun` on smooth exponentially decaying
  kernels (`q(x) = x / (e^x - 1)` for `L₀` via `(t L₀(e^{-t}))'`, and `x^{2m} / (e^x - 1)` for `m ≥ 1`),
- `PakPrimes.HigherOrderStokes.no_nonautonomous_ade_of_higher_order_borel` on explicit meromorphic
  Borel transforms (`ord = 3` at `4π² n` for `L₀`, `ord = 1` at `4π² n` for `L_{2m}`, `m ≥ 1`).
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.DivisorAndMacMahon

open Complex Real Filter MeasureTheory Set MvPolynomial
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
  PakPrimes.PrimeNome
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. Concrete Power Series (`divisorSeries`, `sigmaSeries`, `macmahonSeries`) & Growth Bounds -/

/-- Arithmetic divisor power sum `σ_k(n) = ∑_{d ∣ n} d^k` for `n ≥ 1`, and `0` for `n = 0`. -/
@[expose] def sigmaNat (k n : ℕ) : ℕ :=
  if n = 0 then 0 else ∑ d ∈ Nat.divisors n, d ^ k

/-- Classical Lambert divisor series `L₀(q) = ∑_{n ≥ 1} d(n) q^n`. -/
@[expose] def divisorSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 0 else ((Nat.divisors n).card : ℂ)

/-- Divisor power-sum generating series `L_k(q) = ∑_{n ≥ 1} σ_k(n) q^n`. -/
@[expose] def sigmaSeries (k : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => if n = 0 then 0 else ∑ d ∈ Nat.divisors n, (d : ℂ) ^ k

lemma sigmaSeries_zero : sigmaSeries 0 = divisorSeries := by
  ext n
  simp only [sigmaSeries, divisorSeries, PowerSeries.coeff_mk]
  split_ifs <;> simp

private lemma coeff_sigmaSeries (k n : ℕ) :
    PowerSeries.coeff n (sigmaSeries k) = (sigmaNat k n : ℂ) := by
  simp only [sigmaSeries, sigmaNat, PowerSeries.coeff_mk]
  split_ifs <;> simp

private lemma sigmaNat_pos {k n : ℕ} (hn : 1 ≤ n) : 1 ≤ sigmaNat k n := by
  have hn0 : n ≠ 0 := by omega
  simp only [sigmaNat, hn0, ↓reduceIte]
  have hmem : 1 ∈ Nat.divisors n := Nat.mem_divisors.mpr ⟨one_dvd n, hn0⟩
  calc 1 = 1 ^ k := (one_pow k).symm
    _ ≤ ∑ d ∈ Nat.divisors n, d ^ k :=
      Finset.single_le_sum (f := fun d => d ^ k) (fun _ _ => Nat.zero_le _) hmem

private lemma sigmaNat_le_pow {k n : ℕ} : sigmaNat k n ≤ n ^ (k + 1) := by
  by_cases hn0 : n = 0
  · subst hn0; simp [sigmaNat]
  · simp only [sigmaNat, hn0, ↓reduceIte]
    have hsub : Nat.divisors n ⊆ Finset.Icc 1 n := fun d hd =>
      Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hd)⟩
    have hsum_le : ∑ d ∈ Nat.divisors n, d ^ k ≤ ∑ _d ∈ Nat.divisors n, n ^ k := by
      refine Finset.sum_le_sum fun d hd => ?_
      exact Nat.pow_le_pow_left
        (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hd)) k
    have hcard_le : (Nat.divisors n).card ≤ n := by
      calc (Nat.divisors n).card ≤ (Finset.Icc 1 n).card := Finset.card_le_card hsub
        _ = n := by rw [Nat.card_Icc]; omega
    calc ∑ d ∈ Nat.divisors n, d ^ k ≤ ∑ _d ∈ Nat.divisors n, n ^ k := hsum_le
      _ = (Nat.divisors n).card * n ^ k := by simp
      _ ≤ n * n ^ k := Nat.mul_le_mul_right (n ^ k) hcard_le
      _ = n ^ (k + 1) := by ring

theorem sigmaSeries_polyBound (k : ℕ) : PolyCoeffBound (sigmaSeries k) := by
  refine ⟨1, k + 1, zero_le_one, fun n => ?_⟩
  rw [coeff_sigmaSeries, Complex.norm_natCast, one_mul]
  have hle : (sigmaNat k n : ℝ) ≤ (n : ℝ) ^ (k + 1) := by exact_mod_cast sigmaNat_le_pow (k := k) (n := n)
  refine hle.trans ?_
  exact pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) (k + 1)

/-- Plane partition numbers `p_plane(n)` (`M(q) = ∏_{n ≥ 1} (1 - q^n)^{-n}`), defined recursively
by `p_plane(0) = 1` and `(n + 1) * p_plane(n + 1) = ∑_{k=0}^n σ₂(k + 1) * p_plane(n - k)`. -/
@[expose] def macmahonCoeff : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
    (∑ k ∈ (Finset.range (n + 1)).attach,
      (sigmaNat 2 (k.1 + 1) : ℝ) * macmahonCoeff (n - k.1)) / ((n + 1 : ℕ) : ℝ)
termination_by n => n
decreasing_by
  have hk := Finset.mem_range.mp k.2
  omega

lemma macmahonCoeff_zero : macmahonCoeff 0 = 1 := by
  rw [macmahonCoeff]

lemma macmahonCoeff_succ (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * macmahonCoeff (n + 1) =
      ∑ k ∈ Finset.range (n + 1), (sigmaNat 2 (k + 1) : ℝ) * macmahonCoeff (n - k) := by
  conv_lhs => rw [macmahonCoeff]
  have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [mul_div_cancel₀ _ hne]
  rw [Finset.sum_attach (Finset.range (n + 1)) fun k =>
    (sigmaNat 2 (k + 1) : ℝ) * macmahonCoeff (n - k)]

lemma macmahonCoeff_nonneg (n : ℕ) : 0 ≤ macmahonCoeff n := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    cases n with
    | zero => rw [macmahonCoeff_zero]; exact zero_le_one
    | succ m =>
      have hmul : 0 ≤ ((m + 1 : ℕ) : ℝ) * macmahonCoeff (m + 1) := by
        rw [macmahonCoeff_succ]
        exact Finset.sum_nonneg fun k hk =>
          mul_nonneg (Nat.cast_nonneg _) (ih (m - k) (by omega))
      exact nonneg_of_mul_nonneg_right hmul (by positivity)

/-- Generating series for MacMahon plane partitions `M(q) = ∏_{n ≥ 1} (1 - q^n)^{-n}`,
characterized by `M(0) = 1` and `q M'(q) = L₂(q) M(q)`. -/
@[expose] def macmahonSeries : PowerSeries ℂ :=
  PowerSeries.mk fun n => (macmahonCoeff n : ℂ)

theorem macmahonSeries_constantCoeff :
    PowerSeries.constantCoeff macmahonSeries = 1 := by
  simp [macmahonSeries, macmahonCoeff_zero]

theorem macmahonSeries_ode :
    PowerSeries.X * PowerSeries.derivative macmahonSeries =
      sigmaSeries 2 * macmahonSeries := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, coeff_sigmaSeries 2 0]
    simp [sigmaNat]
  | succ m =>
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j =>
        PowerSeries.coeff i (sigmaSeries 2) * PowerSeries.coeff j macmahonSeries) (m + 1),
      Finset.sum_range_succ']
    have h0 : PowerSeries.coeff 0 (sigmaSeries 2) = 0 := by
      rw [coeff_sigmaSeries 2 0]; simp [sigmaNat]
    rw [h0, zero_mul, add_zero]
    simp only [macmahonSeries, PowerSeries.coeff_mk]
    have hL : (macmahonCoeff (m + 1) : ℂ) * ((m : ℂ) + 1) =
        ((∑ k ∈ Finset.range (m + 1),
          (sigmaNat 2 (k + 1) : ℝ) * macmahonCoeff (m - k) : ℝ) : ℂ) := by
      rw [← macmahonCoeff_succ m]
      push_cast; ring
    rw [hL, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [coeff_sigmaSeries 2 (k + 1), show m + 1 - (k + 1) = m - k by omega]
    push_cast; rfl

theorem macmahonSeries_diskBound : DiskCoeffBound macmahonSeries := by
  intro r hr0 hr1
  obtain ⟨Cg, pg, hCg, hbg⟩ := sigmaSeries_polyBound 2
  have hsum_g : Summable (fun k : ℕ => Cg * ((k + 2 : ℝ) ^ pg * r ^ (k + 1))) := by
    have hs := summable_pow_mul_geometric_of_norm_lt_one pg
      (show ‖r‖ < 1 by simpa [abs_of_pos hr0] using hr1)
    have h := (hs.comp_injective (show Function.Injective (fun k : ℕ => k + 2) from
      fun _ _ hh => Nat.add_right_cancel hh)).mul_right r⁻¹
    refine (h.mul_left Cg).congr fun k => ?_
    simp only [Function.comp_def, Nat.cast_add, Nat.cast_ofNat, pow_add, pow_two]
    field_simp [hr0.ne']
  have hsum_sig : Summable (fun k : ℕ => (sigmaNat 2 (k + 1) : ℝ) * r ^ (k + 1)) := by
    refine hsum_g.of_nonneg_of_le
      (fun k => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0.le _)) fun k => ?_
    have hcoeff := hbg (k + 1)
    rw [coeff_sigmaSeries 2 (k + 1), Complex.norm_natCast] at hcoeff
    have hcast : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [hcast] at hcoeff
    calc (sigmaNat 2 (k + 1) : ℝ) * r ^ (k + 1)
        ≤ (Cg * ((k : ℝ) + 2) ^ pg) * r ^ (k + 1) :=
          mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hr0.le _)
      _ = Cg * ((k + 2 : ℝ) ^ pg * r ^ (k + 1)) := by ring
  let B : ℝ := ∑' k : ℕ, (sigmaNat 2 (k + 1) : ℝ) * r ^ (k + 1)
  obtain ⟨N, hN⟩ := exists_nat_ge (max B 1)
  have hBN : B ≤ (N : ℝ) := (le_max_left B 1).trans hN
  let seq : ℕ → ℝ := fun n => macmahonCoeff n * r ^ n
  let M : ℝ := (Finset.range (N + 1)).sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N)) seq
  have hM_nonneg : 0 ≤ M := by
    have h0 : 0 ≤ seq 0 := mul_nonneg (macmahonCoeff_nonneg 0) (pow_nonneg hr0.le 0)
    exact h0.trans (Finset.le_sup' seq (Finset.mem_range.mpr (Nat.zero_lt_succ N)))
  have hseq_le : ∀ n : ℕ, seq n ≤ M := fun n => by
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      by_cases hnN : n ≤ N
      · exact Finset.le_sup' seq (Finset.mem_range.mpr (by omega))
      · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        have hmN : N ≤ m := by omega
        have hmul : ((m + 1 : ℕ) : ℝ) * seq (m + 1) ≤ ((m + 1 : ℕ) : ℝ) * M := by
          have heq_lhs : ((m + 1 : ℕ) : ℝ) * seq (m + 1) =
              ∑ k ∈ Finset.range (m + 1),
                ((sigmaNat 2 (k + 1) : ℝ) * r ^ (k + 1)) * seq (m - k) := by
            dsimp [seq]
            rw [← mul_assoc, macmahonCoeff_succ m, Finset.sum_mul]
            refine Finset.sum_congr rfl fun k hk => ?_
            have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            rw [show m + 1 = (k + 1) + (m - k) by omega, pow_add]
            ring
          rw [heq_lhs]
          have hsum_bd : ∑ k ∈ Finset.range (m + 1),
                ((sigmaNat 2 (k + 1) : ℝ) * r ^ (k + 1)) * seq (m - k) ≤
              (∑ k ∈ Finset.range (m + 1), (sigmaNat 2 (k + 1) : ℝ) * r ^ (k + 1)) * M := by
            rw [Finset.sum_mul]
            refine Finset.sum_le_sum fun k hk => ?_
            refine mul_le_mul_of_nonneg_left (ih (m - k) (by omega))
              (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0.le _))
          have hpart_le_B : ∑ k ∈ Finset.range (m + 1),
                (sigmaNat 2 (k + 1) : ℝ) * r ^ (k + 1) ≤ B :=
            hsum_sig.sum_le_tsum (Finset.range (m + 1)) fun k _ =>
              mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr0.le _)
          have hB_le_m1 : B ≤ ((m + 1 : ℕ) : ℝ) :=
            hBN.trans (by exact_mod_cast (by omega : N ≤ m + 1))
          calc _ ≤ (∑ k ∈ Finset.range (m + 1), (sigmaNat 2 (k + 1) : ℝ) * r ^ (k + 1)) * M := hsum_bd
            _ ≤ B * M := mul_le_mul_of_nonneg_right hpart_le_B hM_nonneg
            _ ≤ ((m + 1 : ℕ) : ℝ) * M := mul_le_mul_of_nonneg_right hB_le_m1 hM_nonneg
        exact le_of_mul_le_mul_left hmul (by positivity)
  refine ⟨M, hM_nonneg, fun n => ?_⟩
  simp only [macmahonSeries, PowerSeries.coeff_mk, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (macmahonCoeff_nonneg n)]
  have hrn_pos : 0 < r ^ n := pow_pos hr0 n
  rw [inv_pow]
  calc macmahonCoeff n = seq n * (r ^ n)⁻¹ := by dsimp [seq]; field_simp [hrn_pos.ne']
    _ ≤ M * (r ^ n)⁻¹ := mul_le_mul_of_nonneg_right (hseq_le n) (inv_nonneg.mpr hrn_pos.le)

theorem macmahonSeries_qRay_ne_zero (u : ℝ) :
    value macmahonSeries (qRay u) ≠ 0 := by
  have habs := seriesJet_abs macmahonSeries_diskBound 0 (qRay_disk u)
  let termR : ℕ → ℝ := fun n => macmahonCoeff n * (Real.exp (-Real.exp (-u))) ^ n
  have hsumR : Summable termR := by
    refine habs.of_nonneg_of_le (fun n =>
      mul_nonneg (macmahonCoeff_nonneg n) (pow_nonneg (Real.exp_pos _).le n)) fun n => ?_
    simp only [seriesJet, Function.iterate_zero, id_eq, PrimeNome.term, macmahonSeries,
      PowerSeries.coeff_mk, qRay, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (macmahonCoeff_nonneg n), norm_pow, abs_of_pos (Real.exp_pos _)]
    exact le_rfl
  have hval : value macmahonSeries (qRay u) = ((∑' n : ℕ, termR n : ℝ) : ℂ) := by
    unfold value
    rw [Complex.ofReal_tsum]
    congr 1; funext n
    simp [PrimeNome.term, macmahonSeries, qRay, termR]
  have hpos : 0 < ∑' n : ℕ, termR n := by
    have h0 : termR 0 = 1 := by simp [termR, macmahonCoeff_zero]
    calc (0 : ℝ) < 1 := zero_lt_one
      _ = termR 0 := h0.symm
      _ ≤ ∑' n : ℕ, termR n := hsumR.le_tsum 0 fun k _ =>
          mul_nonneg (macmahonCoeff_nonneg k) (pow_nonneg (Real.exp_pos _).le k)
  rw [hval]
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

/-! ### 2. Divisor-Pair Bijection, Lambert Series Identity, and Zeta Identities -/

private lemma sigma_div_ext {n₁ n₂ : ℕ} {d₁ : Nat.divisors (n₁ + 1)} {d₂ : Nat.divisors (n₂ + 1)}
    (hn : n₁ = n₂) (hd : d₁.1 = d₂.1) : (⟨n₁, d₁⟩ : Σ k, Nat.divisors (k + 1)) = ⟨n₂, d₂⟩ := by
  subst hn
  congr 1
  exact Subtype.ext hd

/-- Canonical bijection between pairs `(d, j) ∈ ℕ × ℕ` (representing `(d + 1, j + 1)`) and
`Σ n : ℕ, Nat.divisors (n + 1)` via `(d + 1) * (j + 1) = n + 1`. -/
private def divisorPairEquiv : ℕ × ℕ ≃ Σ n : ℕ, Nat.divisors (n + 1) where
  toFun p := ⟨(p.1 + 1) * (p.2 + 1) - 1,
    ⟨p.1 + 1, Nat.mem_divisors.mpr ⟨by
      have h1 : 1 ≤ (p.1 + 1) * (p.2 + 1) := Nat.succ_le_of_lt (by positivity)
      rw [Nat.sub_add_cancel h1]
      exact dvd_mul_right _ _, by omega⟩⟩⟩
  invFun s := (s.2.1 - 1, (s.1 + 1) / s.2.1 - 1)
  left_inv p := by
    ext <;> dsimp only
    · omega
    · have hmul : (p.1 + 1) * (p.2 + 1) - 1 + 1 = (p.1 + 1) * (p.2 + 1) :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt (by positivity))
      rw [hmul, Nat.mul_div_right _ (Nat.succ_pos _)]
      omega
  right_inv s := by
    rcases s with ⟨n, ⟨d, hd⟩⟩
    have hd_pos : 0 < d := Nat.pos_of_mem_divisors hd
    have hd_dvd : d ∣ n + 1 := Nat.dvd_of_mem_divisors hd
    have hq_pos : 0 < (n + 1) / d :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos n) hd_dvd) hd_pos
    have hfst : (d - 1 + 1) * ((n + 1) / d - 1 + 1) - 1 = n := by
      rw [Nat.sub_add_cancel hd_pos, Nat.sub_add_cancel hq_pos, Nat.mul_div_cancel' hd_dvd]
      omega
    exact sigma_div_ext hfst (Nat.sub_add_cancel hd_pos)

/-- General divisor-sum Fubini identity for nonnegative functions `w : ℕ → ℕ → ℝ`. -/
private lemma tsum_divisor_prod (w : ℕ → ℕ → ℝ) (hw : ∀ d n : ℕ, 0 ≤ w d n)
    (hrow : ∀ d : ℕ, Summable (fun j : ℕ => w (d + 1) ((d + 1) * (j + 1))))
    (hcol : Summable (fun d : ℕ => ∑' j : ℕ, w (d + 1) ((d + 1) * (j + 1)))) :
    (∑' n : ℕ, ∑ d ∈ Nat.divisors (n + 1), w d (n + 1)) =
      ∑' d : ℕ, ∑' j : ℕ, w (d + 1) ((d + 1) * (j + 1)) := by
  let g : ℕ × ℕ → ℝ := fun p => w (p.1 + 1) ((p.1 + 1) * (p.2 + 1))
  have hg_nonneg : ∀ p : ℕ × ℕ, 0 ≤ g p := fun p => hw _ _
  have hg_summ : Summable g :=
    (summable_prod_of_nonneg hg_nonneg).mpr ⟨hrow, hcol⟩
  have hg_sigma : Summable (fun s : Σ n : ℕ, Nat.divisors (n + 1) => g (divisorPairEquiv.symm s)) :=
    (divisorPairEquiv.symm.summable_iff).mpr hg_summ
  have heq_sigma : (∑' p : ℕ × ℕ, g p) =
      ∑' n : ℕ, ∑' d : Nat.divisors (n + 1), g (divisorPairEquiv.symm ⟨n, d⟩) := by
    rw [← divisorPairEquiv.symm.tsum_eq g]
    exact hg_sigma.tsum_sigma' (fun _ => Summable.of_finite)
  have hprod : (∑' p : ℕ × ℕ, g p) = ∑' d : ℕ, ∑' j : ℕ, g (d, j) :=
    hg_summ.tsum_prod' hrow
  rw [← hprod, heq_sigma]
  refine tsum_congr fun n => ?_
  rw [tsum_fintype]
  have hterm : (∑ d : Nat.divisors (n + 1), g (divisorPairEquiv.symm ⟨n, d⟩)) =
      ∑ d : Nat.divisors (n + 1), w d.1 (n + 1) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    have hd_pos : 0 < d.1 := Nat.pos_of_mem_divisors d.2
    have hd_dvd : d.1 ∣ n + 1 := Nat.dvd_of_mem_divisors d.2
    have hq_pos : 0 < (n + 1) / d.1 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos n) hd_dvd) hd_pos
    change w (d.1 - 1 + 1) ((d.1 - 1 + 1) * ((n + 1) / d.1 - 1 + 1)) = w d.1 (n + 1)
    rw [Nat.sub_add_cancel hd_pos, Nat.sub_add_cancel hq_pos, Nat.mul_div_cancel' hd_dvd]
  rw [hterm]
  exact (Finset.sum_coe_sort (Nat.divisors (n + 1)) (fun d => w d (n + 1))).symm

private lemma summable_sigma_mul_rpow (k : ℕ) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (sigmaNat k (n + 1) : ℝ) * r ^ (n + 1)) := by
  have hs := (sigmaSeries_polyBound k).to_diskCoeffBound
  have hnorm : Summable (fun n : ℕ => ‖PrimeNome.term (sigmaSeries k) (r : ℂ) (n + 1)‖) :=
    (seriesJet_abs hs 0 (by simpa [abs_of_pos hr0] using hr1)).comp_injective
      (fun _ _ h => Nat.add_right_cancel h)
  refine hnorm.congr fun n => ?_
  simp [PrimeNome.term, coeff_sigmaSeries, abs_of_pos hr0]

/-- Lambert identity for `t > 0`:
`value (sigmaSeries k) (exp (-t)) = ∑' d : ℕ, ((d + 1 : ℂ)^k / (exp ((d + 1) * t) - 1))`. -/
theorem value_sigmaSeries_exp_neg (k : ℕ) {t : ℝ} (ht : 0 < t) :
    value (sigmaSeries k) (Complex.exp (-(t : ℂ))) =
      ∑' d : ℕ, (((d + 1 : ℕ) : ℂ) ^ k / (Complex.exp (((d + 1 : ℕ) : ℂ) * (t : ℂ)) - 1)) := by
  let r : ℝ := Real.exp (-t)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  let w : ℕ → ℕ → ℝ := fun d n => (d : ℝ) ^ k * r ^ n
  have hw : ∀ d n : ℕ, 0 ≤ w d n := fun d n => by dsimp [w]; positivity
  have hrow : ∀ d : ℕ, Summable (fun j : ℕ => w (d + 1) ((d + 1) * (j + 1))) := fun d => by
    have hq_pos : 0 < r ^ (d + 1) := pow_pos hr0 _
    have hq_lt : r ^ (d + 1) < 1 := pow_lt_one₀ hr0.le hr1 (Nat.succ_ne_zero d)
    have hgeom := (summable_geometric_of_lt_one hq_pos.le hq_lt).mul_left
      ((d + 1 : ℝ) ^ k * r ^ (d + 1))
    refine hgeom.congr fun j => ?_
    dsimp [w]
    push_cast
    rw [show (d + 1) * (j + 1) = d + 1 + (d + 1) * j by ring,
      pow_add r (d + 1) ((d + 1) * j), pow_mul]
    ring
  have htsum_row : ∀ d : ℕ, (∑' j : ℕ, w (d + 1) ((d + 1) * (j + 1))) =
      (d + 1 : ℝ) ^ k * r ^ (d + 1) / (1 - r ^ (d + 1)) := fun d => by
    have hq_pos : 0 < r ^ (d + 1) := pow_pos hr0 _
    have hq_lt : r ^ (d + 1) < 1 := pow_lt_one₀ hr0.le hr1 (Nat.succ_ne_zero d)
    have heq : (fun j : ℕ => w (d + 1) ((d + 1) * (j + 1))) =
        fun j : ℕ => ((d + 1 : ℝ) ^ k * r ^ (d + 1)) * (r ^ (d + 1)) ^ j := by
      funext j; dsimp [w]
      push_cast
      rw [show (d + 1) * (j + 1) = d + 1 + (d + 1) * j by ring,
        pow_add r (d + 1) ((d + 1) * j), pow_mul]
      ring
    rw [heq, tsum_mul_left, tsum_geometric_of_lt_one hq_pos.le hq_lt]
    ring
  have hcol : Summable (fun d : ℕ => ∑' j : ℕ, w (d + 1) ((d + 1) * (j + 1))) := by
    have hdom : Summable (fun d : ℕ => ((d + 1 : ℝ) ^ k / (1 - r)) * r ^ (d + 1)) := by
      have h1 := ((summable_pow_mul_geometric_of_norm_lt_one k
        (show ‖r‖ < 1 by simpa [abs_of_pos hr0] using hr1)).comp_injective
        (show Function.Injective (fun d : ℕ => d + 1) from
          fun _ _ h => Nat.add_right_cancel h)).mul_right (1 - r)⁻¹
      refine h1.congr fun d => ?_
      simp only [Function.comp_def, Nat.cast_add, Nat.cast_one]
      ring
    refine hdom.of_nonneg_of_le
      (fun d => tsum_nonneg fun j => hw (d + 1) ((d + 1) * (j + 1))) fun d => ?_
    rw [htsum_row d]
    have hden : 1 - r ≤ 1 - r ^ (d + 1) := by
      have hp : r ^ (d + 1) ≤ r := by
        rw [pow_succ']
        exact mul_le_of_le_one_right hr0.le (pow_le_one₀ hr0.le hr1.le)
      linarith
    have h1mr : 0 < 1 - r := sub_pos.mpr hr1
    rw [div_eq_mul_inv, mul_assoc]
    calc (d + 1 : ℝ) ^ k * (r ^ (d + 1) * (1 - r ^ (d + 1))⁻¹)
        ≤ (d + 1 : ℝ) ^ k * (r ^ (d + 1) * (1 - r)⁻¹) := by gcongr
      _ = (d + 1 : ℝ) ^ k / (1 - r) * r ^ (d + 1) := by ring
  have hreal := tsum_divisor_prod w hw hrow hcol
  have hlhs : (∑' n : ℕ, ∑ d ∈ Nat.divisors (n + 1), w d (n + 1)) =
      ∑' n : ℕ, (sigmaNat k (n + 1) : ℝ) * r ^ (n + 1) := by
    refine tsum_congr fun n => ?_
    dsimp [w, sigmaNat]
    rw [← Finset.sum_mul]
    simp
  have hrhs : (∑' d : ℕ, ∑' j : ℕ, w (d + 1) ((d + 1) * (j + 1))) =
      ∑' d : ℕ, (d + 1 : ℝ) ^ k / (Real.exp ((d + 1 : ℝ) * t) - 1) := by
    refine tsum_congr fun d => ?_
    rw [htsum_row d]
    have hinv : r ^ (d + 1) = (Real.exp ((d + 1 : ℝ) * t))⁻¹ := by
      dsimp [r]
      rw [← Real.exp_nat_mul, ← Real.exp_neg]
      congr 1; push_cast; ring
    have hexp_gt : (1 : ℝ) < Real.exp ((d + 1 : ℝ) * t) :=
      Real.one_lt_exp_iff.mpr (mul_pos (by positivity) ht)
    rw [hinv]
    field_simp [(by positivity : Real.exp ((d + 1 : ℝ) * t) ≠ 0), (by linarith : Real.exp ((d + 1 : ℝ) * t) - 1 ≠ 0)]
  rw [hlhs, hrhs] at hreal
  have hval_c : value (sigmaSeries k) (Complex.exp (-(t : ℂ))) =
      ((∑' n : ℕ, (sigmaNat k (n + 1) : ℝ) * r ^ (n + 1) : ℝ) : ℂ) := by
    have hsum_c : Summable (fun n : ℕ => PrimeNome.term (sigmaSeries k) (Complex.exp (-(t : ℂ))) n) := by
      refine Summable.of_norm ?_
      exact seriesJet_abs (sigmaSeries_polyBound k).to_diskCoeffBound 0
        (by rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
    rw [value, ← hsum_c.sum_add_tsum_nat_add 1]
    have h0 : PrimeNome.term (sigmaSeries k) (Complex.exp (-(t : ℂ))) 0 = 0 := by
      simp [PrimeNome.term, coeff_sigmaSeries, sigmaNat]
    rw [Finset.sum_range_one, h0, zero_add, Complex.ofReal_tsum]
    congr 1; funext n
    simp only [PrimeNome.term, coeff_sigmaSeries, r, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
    push_cast; rfl
  rw [hval_c, hreal, Complex.ofReal_tsum]
  refine tsum_congr fun d => ?_
  push_cast
  simp

/-- Divisor zeta identity for `a ≥ 0`, `b ≥ 2`:
`∑' n, σ_a(n+1) / (n+1)^(a + b) = ζ(b) * ζ(a + b)`. -/
private lemma tsum_sigmaNat_div_pow (a b : ℕ) (hb : 2 ≤ b) :
    (∑' n : ℕ, ((sigmaNat a (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (a + b))) =
      riemannZeta (b : ℂ) * riemannZeta ((a + b : ℕ) : ℂ) := by
  let w : ℕ → ℕ → ℝ := fun d n => (d : ℝ) ^ a / (n : ℝ) ^ (a + b)
  have hw : ∀ d n : ℕ, 0 ≤ w d n := fun d n => by dsimp [w]; positivity
  have hs_b : Summable (fun d : ℕ => ((d + 1 : ℕ) : ℝ) ^ (-(b : ℝ))) := by
    have hlt : -(b : ℝ) < -1 := by
      have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      linarith
    exact (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr hlt)
  have hs_ab : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (-((a + b : ℕ) : ℝ))) := by
    have hlt : -((a + b : ℕ) : ℝ) < -1 := by
      have habR : (2 : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ a + b)
      linarith
    exact (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr hlt)
  have hfactor : ∀ d j : ℕ, w (d + 1) ((d + 1) * (j + 1)) =
      ((d + 1 : ℕ) : ℝ) ^ (-(b : ℝ)) * ((j + 1 : ℕ) : ℝ) ^ (-((a + b : ℕ) : ℝ)) := fun d j => by
    dsimp [w]
    have hd : (0 : ℝ) < (d + 1 : ℕ) := by positivity
    have hj : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    rw [Nat.cast_mul, mul_pow, pow_add, Real.rpow_neg hd.le, Real.rpow_neg hj.le,
      Real.rpow_natCast, Real.rpow_natCast]
    field_simp [hd.ne', hj.ne']
  have hrow : ∀ d : ℕ, Summable (fun j : ℕ => w (d + 1) ((d + 1) * (j + 1))) := fun d => by
    refine (hs_ab.mul_left (((d + 1 : ℕ) : ℝ) ^ (-(b : ℝ)))).congr fun j => (hfactor d j).symm
  have hcol : Summable (fun d : ℕ => ∑' j : ℕ, w (d + 1) ((d + 1) * (j + 1))) := by
    refine (hs_b.mul_right (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ (-((a + b : ℕ) : ℝ)))).congr fun d => ?_
    simp_rw [hfactor]
    rw [tsum_mul_left]
  have hreal := tsum_divisor_prod w hw hrow hcol
  have hlhs : (∑' n : ℕ, ∑ d ∈ Nat.divisors (n + 1), w d (n + 1)) =
      ∑' n : ℕ, (sigmaNat a (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (a + b) := by
    refine tsum_congr fun n => ?_
    dsimp [w, sigmaNat]
    rw [← Finset.sum_div]
    simp
  have hrhs : (∑' d : ℕ, ∑' j : ℕ, w (d + 1) ((d + 1) * (j + 1))) =
      (∑' d : ℕ, ((d + 1 : ℕ) : ℝ) ^ (-(b : ℝ))) *
        (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ (-((a + b : ℕ) : ℝ))) := by
    simp_rw [hfactor, tsum_mul_left, tsum_mul_right]
  rw [hlhs, hrhs] at hreal
  have hzeta_b : riemannZeta (b : ℂ) = ((∑' d : ℕ, ((d + 1 : ℕ) : ℝ) ^ (-(b : ℝ)) : ℝ) : ℂ) := by
    have hb1 : 1 < (b : ℂ).re := by simp; exact_mod_cast (by omega : 1 < b)
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hb1, Complex.ofReal_tsum]
    refine tsum_congr fun d => ?_
    have hd : (0 : ℝ) < (d + 1 : ℕ) := by positivity
    rw [one_div, Complex.cpow_natCast, Real.rpow_neg hd.le, Real.rpow_natCast]
    push_cast; rfl
  have hzeta_ab : riemannZeta ((a + b : ℕ) : ℂ) =
      ((∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ (-((a + b : ℕ) : ℝ)) : ℝ) : ℂ) := by
    have hab1 : 1 < ((a + b : ℕ) : ℂ).re := by simp; exact_mod_cast (by omega : 1 < a + b)
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hab1, Complex.ofReal_tsum]
    refine tsum_congr fun j => ?_
    have hj : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    rw [one_div, Complex.cpow_natCast, Real.rpow_neg hj.le, Real.rpow_natCast]
    push_cast; rfl
  rw [hzeta_b, hzeta_ab, ← Complex.ofReal_mul, ← hreal, Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  push_cast; rfl

/-! ### 3. Analytic Kernel `q(x) = x / (e^x - 1)`, Bernoulli Taylor Coefficients & `ExpDecaySmooth` -/

/-- Entire auxiliary function `E(z) = (e^z - 1)/z = ∑_{n ≥ 0} z^n / (n + 1)!`. -/
@[expose] def expAux (z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ n / ((n + 1).factorial : ℂ)

private lemma expAux_hasFPowerSeriesOnBall :
    HasFPowerSeriesOnBall expAux
      (.ofScalars ℂ (fun n : ℕ => ((n + 1).factorial : ℂ)⁻¹)) 0 ⊤ := by
  let c : ℕ → ℂ := fun n => ((n + 1).factorial : ℂ)⁻¹
  have hc_ne : ∀ᶠ n : ℕ in atTop, c n ≠ 0 := Eventually.of_forall fun n => by
    dsimp [c]; exact inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  have hc_lim : Tendsto (fun n : ℕ => ‖c n.succ‖ / ‖c n‖) atTop (𝓝 0) := by
    have heq : (fun n : ℕ => ‖c n.succ‖ / ‖c n‖) = fun n : ℕ => ((n : ℝ) + 2)⁻¹ := by
      funext n
      dsimp [c]
      rw [norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast,
        Nat.factorial_succ, Nat.cast_mul]
      have h1 : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
      have h2 : ((n + 1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [h1, h2]
      push_cast; ring
    rw [heq]
    exact tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ) tendsto_natCast_atTop_atTop)
  have hrad : (FormalMultilinearSeries.ofScalars ℂ c).radius = ⊤ :=
    FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto ℂ c hc_ne hc_lim
  have hball : HasFPowerSeriesOnBall (FormalMultilinearSeries.ofScalarsSum c)
      (FormalMultilinearSeries.ofScalars ℂ c) 0 ⊤ := by
    rw [← hrad]
    exact (FormalMultilinearSeries.ofScalars ℂ c).hasFPowerSeriesOnBall
      (hrad ▸ (by simp : (0 : ENNReal) < ⊤))
  refine hball.congr fun z _ => ?_
  rw [FormalMultilinearSeries.ofScalars_sum_eq]
  refine tsum_congr fun n => ?_
  dsimp [c]; simp [div_eq_mul_inv, mul_comm]

private lemma expAux_analytic (z : ℂ) : AnalyticAt ℂ expAux z :=
  expAux_hasFPowerSeriesOnBall.analyticOnNhd z (by simp)

private lemma expAux_zero : expAux 0 = 1 := by
  rw [expAux, tsum_eq_single 0]
  · simp
  · intro n hn; simp [hn]

private lemma expAux_mul_sub (z : ℂ) : z * expAux z = Complex.exp z - 1 := by
  by_cases hz : z = 0
  · subst hz; simp
  have hsum : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z) := by
    rw [Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp z
  have hsum_tail : HasSum (fun n : ℕ => z ^ (n + 1) / ((n + 1).factorial : ℂ)) (Complex.exp z - 1) := by
    have hsplit := (hasSum_nat_add_iff' (f := fun n : ℕ => z ^ n / (n.factorial : ℂ)) 1).mpr hsum
    simpa [Finset.sum_range_one] using hsplit
  have hsum_aux : HasSum (fun n : ℕ => z ^ n / ((n + 1).factorial : ℂ)) (z⁻¹ * (Complex.exp z - 1)) := by
    refine (hsum_tail.mul_left z⁻¹).congr_fun fun n => ?_
    rw [pow_succ']
    field_simp [hz]
  rw [expAux, hsum_aux.tsum_eq]
  field_simp [hz]

private lemma expAux_ofReal_ne_zero (x : ℝ) : expAux (x : ℂ) ≠ 0 := by
  by_cases hx0 : x = 0
  · subst hx0; simp [expAux_zero]
  intro h0
  have hmul := expAux_mul_sub (x : ℂ)
  rw [h0, mul_zero] at hmul
  have hexp1 : Complex.exp (x : ℂ) = 1 := sub_eq_zero.mp hmul.symm
  have hexpR : Real.exp x = 1 := by
    exact_mod_cast (by simpa [← Complex.ofReal_exp] using hexp1 : ((Real.exp x : ℝ) : ℂ) = (1 : ℂ))
  rcases lt_or_gt_of_ne hx0 with hlt | hgt
  · exact (Real.exp_lt_one_iff.mpr hlt).ne hexpR
  · exact (Real.one_lt_exp_iff.mpr hgt).ne' hexpR

/-- Complex analytic extension of `z / (e^z - 1)` (equals `1` at `z = 0`). -/
@[expose] def qComplex (z : ℂ) : ℂ := (expAux z)⁻¹

/-- Smooth real-line kernel `q(x) = x / (e^x - 1)` (extended smoothly to `q(0) = 1`). -/
@[expose] def qFun (x : ℝ) : ℂ := qComplex (x : ℂ)

/-- Smooth derivative kernel `g(x) = d/dx (x / (e^x - 1))` for `L₀`. -/
@[expose] def gFun (x : ℝ) : ℂ := deriv qFun x

/-- Smooth higher-weight kernel `h_{2m}(x) = x^{2m} / (e^x - 1) = x^{2m-1} q(x)` for `m ≥ 1`. -/
@[expose] def hFun (m : ℕ) (x : ℝ) : ℂ := (x : ℂ) ^ (2 * m - 1) * qFun x

private lemma qComplex_analytic_ofReal (x : ℝ) : AnalyticAt ℂ qComplex (x : ℂ) :=
  (expAux_analytic (x : ℂ)).inv (expAux_ofReal_ne_zero x)

private lemma qComplex_mul_exp_sub_one (z : ℂ) (hz : expAux z ≠ 0) :
    qComplex z * (Complex.exp z - 1) = z := by
  rw [qComplex, ← expAux_mul_sub z]
  field_simp [hz]

private lemma iteratedDeriv_cexp_zero (k : ℕ) : iteratedDeriv k Complex.exp 0 = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ']
    have h1 : deriv Complex.exp = Complex.exp := by ext z; simp
    rw [h1, ih]

private lemma iteratedDeriv_qComplex_zero (n : ℕ) :
    iteratedDeriv n qComplex 0 = (bernoulli n : ℂ) := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have hq_an : AnalyticAt ℂ qComplex 0 := by
      simpa using qComplex_analytic_ofReal 0
    have hexp_an : AnalyticAt ℂ (fun z : ℂ => Complex.exp z - 1) 0 := by fun_prop
    have heq_nhds : (fun z : ℂ => qComplex z * (Complex.exp z - 1)) =ᶠ[𝓝 (0 : ℂ)] id := by
      have hne : ∀ᶠ z in 𝓝 (0 : ℂ), expAux z ≠ 0 :=
        (expAux_analytic 0).continuousAt.eventually_ne (by rw [expAux_zero]; exact one_ne_zero)
      filter_upwards [hne] with z hz
      exact qComplex_mul_exp_sub_one z hz
    have hderiv_eq : iteratedDeriv (n + 1) (fun z : ℂ => qComplex z * (Complex.exp z - 1)) 0 =
        iteratedDeriv (n + 1) id (0 : ℂ) :=
      heq_nhds.iteratedDeriv_eq (n + 1)
    rw [iteratedDeriv_fun_mul hq_an.contDiffAt hexp_an.contDiffAt] at hderiv_eq
    have hexp_deriv : ∀ m : ℕ, iteratedDeriv m (fun z : ℂ => Complex.exp z - 1) 0 =
        if m = 0 then 0 else 1 := fun m => by
      cases m with
      | zero => simp
      | succ k =>
        rw [iteratedDeriv_succ']
        have h1 : deriv (fun z : ℂ => Complex.exp z - 1) = Complex.exp := by
          ext z; simp
        rw [h1, iteratedDeriv_cexp_zero k]
        simp
    have h_lhs : (∑ k ∈ Finset.range (n + 1 + 1),
        ((n + 1).choose k : ℂ) * iteratedDeriv k qComplex 0 *
          iteratedDeriv (n + 1 - k) (fun z : ℂ => Complex.exp z - 1) 0) =
        ∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℂ) * iteratedDeriv k qComplex 0 := by
      rw [Finset.sum_range_succ]
      simp only [Nat.sub_self, hexp_deriv 0, ↓reduceIte, mul_zero, add_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkne : n + 1 - k ≠ 0 := by
        have hklt := Finset.mem_range.mp hk
        omega
      simp [hexp_deriv (n + 1 - k), hkne]
    have h_rhs : iteratedDeriv (n + 1) (id : ℂ → ℂ) 0 = if n = 0 then 1 else 0 := by
      cases n with
      | zero => simp
      | succ m =>
        rw [iteratedDeriv_succ']
        have hid : deriv (id : ℂ → ℂ) = fun _ => 1 := by ext z; simp
        rw [hid, iteratedDeriv_const]
    rw [h_lhs, h_rhs] at hderiv_eq
    have hbern : (∑ k ∈ Finset.range (n + 1), ((n + 1).choose k : ℂ) * (bernoulli k : ℂ)) =
        if n = 0 then 1 else 0 := by
      have hb := congrArg (fun q : ℚ => (q : ℂ)) (sum_bernoulli (n + 1))
      cases n with
      | zero => simp
      | succ m =>
        have hne1 : m + 1 + 1 ≠ 1 := by omega
        simp only [hne1, ↓reduceIte, Rat.cast_zero, Rat.cast_sum, Rat.cast_mul,
          Rat.cast_natCast] at hb
        simpa [Nat.succ_ne_zero] using hb
    have hdiff : ∑ k ∈ Finset.range (n + 1),
        ((n + 1).choose k : ℂ) * (iteratedDeriv k qComplex 0 - (bernoulli k : ℂ)) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, hderiv_eq, hbern, sub_self]
    rw [Finset.sum_range_succ] at hdiff
    have htail : ∑ k ∈ Finset.range n,
        ((n + 1).choose k : ℂ) * (iteratedDeriv k qComplex 0 - (bernoulli k : ℂ)) = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [ih k (Finset.mem_range.mp hk), sub_self, mul_zero]
    rw [htail, zero_add, Nat.choose_succ_self_right] at hdiff
    have hne0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hne0)

private lemma iteratedDeriv_ofReal_comp {F : ℂ → ℂ} (hF : ∀ x : ℝ, AnalyticAt ℂ F (x : ℂ)) :
    ∀ (n : ℕ) (x : ℝ), iteratedDeriv n (fun t : ℝ => F (t : ℂ)) x = iteratedDeriv n F (x : ℂ) := by
  intro n
  induction n generalizing F with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have hderiv : (deriv fun t : ℝ => F (t : ℂ)) = fun t : ℝ => deriv F (t : ℂ) := by
      funext t
      simpa [Function.comp_def] using
        ((hF t).differentiableAt.hasDerivAt.scomp t (hasDerivAt_id t).ofReal_comp).deriv
    rw [hderiv]
    exact ih (fun t => (hF t).deriv) x

private lemma iteratedDeriv_qFun_zero (n : ℕ) :
    iteratedDeriv n qFun 0 = (bernoulli n : ℂ) := by
  change iteratedDeriv n (fun t : ℝ => qComplex (t : ℂ)) 0 = _
  rw [iteratedDeriv_ofReal_comp qComplex_analytic_ofReal n 0]
  exact iteratedDeriv_qComplex_zero n

private lemma contDiff_of_analytic_ofReal {F : ℂ → ℂ} (hF : ∀ x : ℝ, AnalyticAt ℂ F (x : ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => F (x : ℂ)) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  exact ((hF x).restrictScalars.contDiffAt.comp x
    (Complex.ofRealCLM.contDiff.contDiffAt)).of_le le_top

private lemma qFun_contDiff : ContDiff ℝ (⊤ : ℕ∞) qFun :=
  contDiff_of_analytic_ofReal qComplex_analytic_ofReal

private lemma qFun_eq_div_exp_sub_one {x : ℝ} (hx : x ≠ 0) :
    qFun x = (x : ℂ) / (Complex.exp (x : ℂ) - 1) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
  have h := qComplex_mul_exp_sub_one (x : ℂ) (expAux_ofReal_ne_zero x)
  have hden : Complex.exp (x : ℂ) - 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact hx0 h.symm
  exact eq_div_of_mul_eq hden h

/-- Exponentially decaying smooth functions on `[0, ∞)` (smooth on `ℝ` with all derivatives
decaying exponentially as `x → +∞`). -/
@[expose] def ExpDecaySmooth (h : ℝ → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) h ∧
    ∀ r : ℕ, ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
      ∀ x : ℝ, 0 ≤ x → ‖iteratedDeriv r h x‖ ≤ C * Real.exp (-c * x)

private lemma ExpDecaySmooth.deriv {h : ℝ → ℂ} (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (deriv h) := by
  refine ⟨(contDiff_infty_iff_deriv.mp hh.1).2, fun r => ?_⟩
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 (r + 1)
  refine ⟨C, c, hC, hc, fun x hx => ?_⟩
  rw [← iteratedDeriv_succ']
  exact hbd x hx

private lemma ExpDecaySmooth.const_mul {h : ℝ → ℂ} (a : ℂ) (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (fun x => a * h x) := by
  refine ⟨contDiff_const.mul hh.1, fun r => ?_⟩
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 r
  refine ⟨‖a‖ * C, c, mul_nonneg (norm_nonneg a) hC, hc, fun x hx => ?_⟩
  rw [iteratedDeriv_const_mul_field, norm_mul]
  calc ‖a‖ * ‖iteratedDeriv r h x‖
      ≤ ‖a‖ * (C * Real.exp (-c * x)) := mul_le_mul_of_nonneg_left (hbd x hx) (norm_nonneg a)
    _ = ‖a‖ * C * Real.exp (-c * x) := by ring

private lemma ExpDecaySmooth.sub {f g : ℝ → ℂ} (hf : ExpDecaySmooth f) (hg : ExpDecaySmooth g) :
    ExpDecaySmooth (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, fun r => ?_⟩
  obtain ⟨Cf, cf, hCf, hcf, hbf⟩ := hf.2 r
  obtain ⟨Cg, cg, hCg, hcg, hbg⟩ := hg.2 r
  refine ⟨Cf + Cg, min cf cg, by positivity, lt_min hcf hcg, fun x hx => ?_⟩
  have hsub : iteratedDeriv r (fun y => f y - g y) x = iteratedDeriv r f x - iteratedDeriv r g x :=
    iteratedDeriv_fun_sub (hf.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
      (hg.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [hsub]
  have hmin1 : Real.exp (-cf * x) ≤ Real.exp (-min cf cg * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_left cf cg]
  have hmin2 : Real.exp (-cg * x) ≤ Real.exp (-min cf cg * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith [min_le_right cf cg]
  calc ‖iteratedDeriv r f x - iteratedDeriv r g x‖
      ≤ ‖iteratedDeriv r f x‖ + ‖iteratedDeriv r g x‖ := norm_sub_le _ _
    _ ≤ Cf * Real.exp (-cf * x) + Cg * Real.exp (-cg * x) := add_le_add (hbf x hx) (hbg x hx)
    _ ≤ Cf * Real.exp (-min cf cg * x) + Cg * Real.exp (-min cf cg * x) :=
      add_le_add (mul_le_mul_of_nonneg_left hmin1 hCf) (mul_le_mul_of_nonneg_left hmin2 hCg)
    _ = (Cf + Cg) * Real.exp (-min cf cg * x) := by ring

private lemma real_mul_exp_neg_le_one {y : ℝ} (_hy : 0 ≤ y) :
    y * Real.exp (-y) ≤ 1 := by
  have h1 : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have h2 : y ≤ Real.exp y := by linarith
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact (div_le_one (Real.exp_pos y)).mpr h2

private lemma iteratedDeriv_ofReal_ge_two (k : ℕ) (hk : 2 ≤ k) (x : ℝ) :
    iteratedDeriv k (fun t : ℝ => (t : ℂ)) x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 2 := ⟨k - 2, by omega⟩
  have heq : (fun t : ℝ => (t : ℂ)) = fun t : ℝ => (id (t : ℂ)) := rfl
  rw [heq, iteratedDeriv_ofReal_comp (fun _ => analyticAt_id)]
  induction m with
  | zero =>
    rw [iteratedDeriv_succ']
    have hid : deriv (id : ℂ → ℂ) = fun _ => 1 := by ext z; simp
    rw [hid]
    simp
  | succ m _ =>
    have hm2 : 2 ≤ m + 2 := by omega
    rw [show m + 1 + 2 = (m + 2) + 1 by omega, iteratedDeriv_succ]
    have hf : (fun z : ℂ => iteratedDeriv (m + 2) (id : ℂ → ℂ) z) = 0 := by
      ext z
      rw [show m + 2 = (m + 1) + 1 by omega, iteratedDeriv_succ']
      have hid : deriv (id : ℂ → ℂ) = fun _ => 1 := by ext w; simp
      rw [hid]
      cases m with
      | zero => simp
      | succ k => simp [iteratedDeriv_const]
    have : iteratedDeriv (m + 2) (id : ℂ → ℂ) = 0 := hf
    rw [this]
    simp

private lemma ExpDecaySmooth.mul_ofReal {h : ℝ → ℂ} (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (fun x => (x : ℂ) * h x) := by
  refine ⟨(Complex.ofRealCLM.contDiff).mul hh.1, fun r => ?_⟩
  cases r with
  | zero =>
    obtain ⟨C0, c0, hC0, hc0, hb0⟩ := hh.2 0
    refine ⟨C0 * (2 / c0), c0 / 2, by positivity, by positivity, fun x hx => ?_⟩
    simp only [iteratedDeriv_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
    have h0 := hb0 x hx
    simp only [iteratedDeriv_zero] at h0
    have hmul : x * Real.exp (-c0 * x) ≤ (2 / c0) * Real.exp (-(c0 / 2) * x) := by
      have hy : 0 ≤ (c0 / 2) * x := by positivity
      have h1 := real_mul_exp_neg_le_one hy
      have hexp : Real.exp (-c0 * x) = Real.exp (-((c0 / 2) * x)) * Real.exp (-(c0 / 2) * x) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp, ← mul_assoc]
      calc (x * Real.exp (-((c0 / 2) * x))) * Real.exp (-(c0 / 2) * x)
          = ((2 / c0) * (((c0 / 2) * x) * Real.exp (-((c0 / 2) * x)))) * Real.exp (-(c0 / 2) * x) := by
            field_simp [hc0.ne']
        _ ≤ ((2 / c0) * 1) * Real.exp (-(c0 / 2) * x) := by gcongr
        _ = (2 / c0) * Real.exp (-(c0 / 2) * x) := by ring
    calc x * ‖h x‖ ≤ x * (C0 * Real.exp (-c0 * x)) := mul_le_mul_of_nonneg_left h0 hx
      _ = C0 * (x * Real.exp (-c0 * x)) := by ring
      _ ≤ C0 * ((2 / c0) * Real.exp (-(c0 / 2) * x)) := mul_le_mul_of_nonneg_left hmul hC0
      _ = C0 * (2 / c0) * Real.exp (-(c0 / 2) * x) := by ring
  | succ m =>
    obtain ⟨C0, c0, hC0, hc0, hb0⟩ := hh.2 m
    obtain ⟨C1, c1, hC1, hc1, hb1⟩ := hh.2 (m + 1)
    let c := min c0 (c1 / 2)
    have hc : 0 < c := lt_min hc0 (by positivity)
    refine ⟨C1 * (2 / c1) + (m + 1 : ℝ) * C0, c, by positivity, hc, fun x hx => ?_⟩
    have hleib : iteratedDeriv (m + 1) (fun t : ℝ => (t : ℂ) * h t) x =
        ∑ i ∈ Finset.range (m + 2),
          ((m + 1).choose i : ℂ) * iteratedDeriv i (fun t : ℝ => (t : ℂ)) x *
            iteratedDeriv (m + 1 - i) h x :=
      iteratedDeriv_fun_mul (f := fun t : ℝ => (t : ℂ)) (g := h) (n := m + 1) (x := x)
        ((Complex.ofRealCLM.contDiff.contDiffAt).of_le le_top)
        (hh.1.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
    have hsplit : ∑ i ∈ Finset.range (m + 2),
        ((m + 1).choose i : ℂ) * iteratedDeriv i (fun t : ℝ => (t : ℂ)) x *
          iteratedDeriv (m + 1 - i) h x =
        (x : ℂ) * iteratedDeriv (m + 1) h x + ((m + 1 : ℕ) : ℂ) * iteratedDeriv m h x := by
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero]
      rw [Finset.sum_range_succ']
      have hd1 : iteratedDeriv 1 (fun t : ℝ => (t : ℂ)) x = 1 := by
        rw [iteratedDeriv_one]
        exact (hasDerivAt_id x).ofReal_comp.deriv
      have hzero : ∀ i ∈ Finset.range m,
          ((m + 1).choose (i + 1 + 1) : ℂ) *
            iteratedDeriv (i + 1 + 1) (fun t : ℝ => (t : ℂ)) x *
            iteratedDeriv (m + 1 - (i + 1 + 1)) h x = 0 := by
        intro i _
        rw [iteratedDeriv_ofReal_ge_two (i + 1 + 1) (by omega) x, mul_zero, zero_mul]
      rw [Finset.sum_eq_zero hzero, zero_add, Nat.choose_one_right, hd1, mul_one,
        show m + 1 - 1 = m by omega]
      push_cast; ring
    rw [hleib, hsplit]
    have hmul : x * Real.exp (-c1 * x) ≤ (2 / c1) * Real.exp (-(c1 / 2) * x) := by
      have hy : 0 ≤ (c1 / 2) * x := by positivity
      have h1 := real_mul_exp_neg_le_one hy
      have hexp : Real.exp (-c1 * x) = Real.exp (-((c1 / 2) * x)) * Real.exp (-(c1 / 2) * x) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp, ← mul_assoc]
      calc (x * Real.exp (-((c1 / 2) * x))) * Real.exp (-(c1 / 2) * x)
          = ((2 / c1) * (((c1 / 2) * x) * Real.exp (-((c1 / 2) * x)))) * Real.exp (-(c1 / 2) * x) := by
            field_simp [hc1.ne']
        _ ≤ ((2 / c1) * 1) * Real.exp (-(c1 / 2) * x) := by gcongr
        _ = (2 / c1) * Real.exp (-(c1 / 2) * x) := by ring
    have he1 : Real.exp (-(c1 / 2) * x) ≤ Real.exp (-c * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [min_le_right c0 (c1 / 2)]
    have he0 : Real.exp (-c0 * x) ≤ Real.exp (-c * x) := by
      apply Real.exp_le_exp.mpr
      nlinarith [min_le_left c0 (c1 / 2)]
    calc ‖(x : ℂ) * iteratedDeriv (m + 1) h x + ((m + 1 : ℕ) : ℂ) * iteratedDeriv m h x‖
        ≤ ‖(x : ℂ) * iteratedDeriv (m + 1) h x‖ + ‖((m + 1 : ℕ) : ℂ) * iteratedDeriv m h x‖ :=
          norm_add_le _ _
      _ = x * ‖iteratedDeriv (m + 1) h x‖ + (m + 1 : ℝ) * ‖iteratedDeriv m h x‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
            Complex.norm_natCast]
          push_cast; rfl
      _ ≤ x * (C1 * Real.exp (-c1 * x)) + (m + 1 : ℝ) * (C0 * Real.exp (-c0 * x)) := by
          gcongr
          · exact hb1 x hx
          · exact hb0 x hx
      _ = C1 * (x * Real.exp (-c1 * x)) + (m + 1 : ℝ) * C0 * Real.exp (-c0 * x) := by ring
      _ ≤ C1 * ((2 / c1) * Real.exp (-(c1 / 2) * x)) + (m + 1 : ℝ) * C0 * Real.exp (-c0 * x) := by
          gcongr
      _ ≤ C1 * ((2 / c1) * Real.exp (-c * x)) + (m + 1 : ℝ) * C0 * Real.exp (-c * x) := by
          gcongr
      _ = (C1 * (2 / c1) + (m + 1 : ℝ) * C0) * Real.exp (-c * x) := by ring

private lemma ExpDecaySmooth.pow_ofReal_mul {h : ℝ → ℂ} (k : ℕ) (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (fun x => (x : ℂ) ^ k * h x) := by
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    have heq : (fun x : ℝ => (x : ℂ) ^ (k + 1) * h x) =
        fun x : ℝ => (x : ℂ) * ((x : ℂ) ^ k * h x) := by
      funext x; rw [pow_succ']; ring
    rw [heq]
    exact ih.mul_ofReal

private lemma exp_sub_one_ge_half_exp {x : ℝ} (hx : 1 ≤ x) :
    Real.exp x / 2 ≤ Real.exp x - 1 := by
  have h2 : (2 : ℝ) ≤ Real.exp x := by
    have := Real.add_one_le_exp x
    linarith
  linarith

private lemma v_iteratedDeriv_poly (r : ℕ) :
    ∃ P : Polynomial ℝ, ∀ x : ℝ, 0 < x →
      iteratedDeriv r (fun y : ℝ => (Real.exp y - 1)⁻¹) x =
        (Real.exp x - 1)⁻¹ * P.eval ((Real.exp x - 1)⁻¹) := by
  let v : ℝ → ℝ := fun y => (Real.exp y - 1)⁻¹
  have hv_deriv : ∀ x : ℝ, 0 < x → HasDerivAt v (-(v x + v x ^ 2)) x := fun x hx => by
    have hexp : Real.exp x - 1 ≠ 0 := (sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)).ne'
    have h1 : HasDerivAt (fun y : ℝ => Real.exp y - 1) (Real.exp x) x :=
      (Real.hasDerivAt_exp x).sub_const 1
    have h2 : HasDerivAt v (-Real.exp x / (Real.exp x - 1) ^ 2) x :=
      h1.inv hexp
    convert h2 using 1
    dsimp [v]
    field_simp [hexp]
    ring
  induction r with
  | zero =>
    refine ⟨1, fun x _ => by simp⟩
  | succ r ih =>
    obtain ⟨P, hP⟩ := ih
    refine ⟨-(1 + Polynomial.X) * (P + Polynomial.X * P.derivative), fun x hx => ?_⟩
    have hopen : IsOpen (Ioi (0 : ℝ)) := isOpen_Ioi
    have heq_nhds : iteratedDeriv r v =ᶠ[𝓝 x] fun y => v y * P.eval (v y) :=
      Filter.eventually_of_mem (hopen.mem_nhds hx) hP
    rw [iteratedDeriv_succ, heq_nhds.deriv_eq]
    have hvd := hv_deriv x hx
    have hPd : HasDerivAt (fun y => P.eval (v y)) (P.derivative.eval (v x) * -(v x + v x ^ 2)) x :=
      (Polynomial.hasDerivAt P (v x)).comp x hvd
    have hmul : deriv (fun y => v y * P.eval (v y)) x =
        -(v x + v x ^ 2) * P.eval (v x) + v x * (P.derivative.eval (v x) * -(v x + v x ^ 2)) :=
      (hvd.mul hPd).deriv
    rw [hmul]
    simp only [Polynomial.eval_mul, Polynomial.eval_neg, Polynomial.eval_add, Polynomial.eval_one,
      Polynomial.eval_X]
    ring

private lemma poly_eval_bound_unit (P : Polynomial ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    |P.eval t| ≤ ∑ i ∈ P.support, |P.coeff i| := by
  rw [Polynomial.eval_eq_sum]
  dsimp only [Polynomial.sum, Finsupp.sum]
  calc |∑ i ∈ P.support, P.coeff i * t ^ i|
      ≤ ∑ i ∈ P.support, |P.coeff i * t ^ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ P.support, |P.coeff i| := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_pow, abs_of_nonneg ht0]
        exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ ht0 ht1)

private lemma iteratedDeriv_ofReal_comp_real {v : ℝ → ℝ} {k : ℕ} {x : ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (Ioi 0)) (hx : 0 < x) :
    iteratedDeriv k (fun y : ℝ => (v y : ℂ)) x = ((iteratedDeriv k v x : ℝ) : ℂ) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    have hdv : ContDiffOn ℝ (⊤ : ℕ∞) (deriv v) (Ioi 0) :=
      ((contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mp hv).2
    have heq : (deriv fun y : ℝ => (v y : ℂ)) =ᶠ[𝓝 x] fun y : ℝ => ((deriv v y : ℝ) : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      have hd : DifferentiableAt ℝ v y :=
        ((hv.differentiableOn (by simp)) y hy).differentiableAt (isOpen_Ioi.mem_nhds hy)
      exact (hd.hasDerivAt.ofReal_comp).deriv
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq k, iteratedDeriv_succ']
    exact ih hdv

private lemma qFun_expDecaySmooth : ExpDecaySmooth qFun := by
  refine ⟨qFun_contDiff, fun r => ?_⟩
  obtain ⟨P, hP⟩ := v_iteratedDeriv_poly r
  obtain ⟨P1, hP1⟩ := v_iteratedDeriv_poly (r - 1)
  let B0 : ℝ := ∑ i ∈ P.support, |P.coeff i|
  let B1 : ℝ := ∑ i ∈ P1.support, |P1.coeff i|
  have hcont_r : ContinuousOn (fun x : ℝ => ‖iteratedDeriv r qFun x‖) (Icc 0 1) :=
    ((qFun_contDiff.continuous_iteratedDeriv r (WithTop.coe_le_coe.mpr le_top)).norm).continuousOn
  obtain ⟨xm, _, hxm⟩ := isCompact_Icc.exists_isMaxOn ⟨0, left_mem_Icc.mpr zero_le_one⟩ hcont_r
  let M0 : ℝ := ‖iteratedDeriv r qFun xm‖
  let C_tail : ℝ := 2 * B0 * 2 + (r : ℝ) * (2 * B1)
  refine ⟨max (M0 * Real.exp (1 / 2)) C_tail, 1 / 2, by positivity, by norm_num, fun x hx => ?_⟩
  by_cases hx1 : x ≤ 1
  · have hm : ‖iteratedDeriv r qFun x‖ ≤ M0 := hxm ⟨hx, hx1⟩
    have hexp : 1 ≤ Real.exp (1 / 2) * Real.exp (-(1 / 2) * x) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc ‖iteratedDeriv r qFun x‖ ≤ M0 := hm
      _ = M0 * 1 := (mul_one M0).symm
      _ ≤ M0 * (Real.exp (1 / 2) * Real.exp (-(1 / 2) * x)) :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = (M0 * Real.exp (1 / 2)) * Real.exp (-(1 / 2) * x) := by ring
      _ ≤ max (M0 * Real.exp (1 / 2)) C_tail * Real.exp (-(1 / 2) * x) := by
          gcongr; exact le_max_left _ _
  · have hx_gt1 : 1 ≤ x := by linarith
    have hx_pos : 0 < x := by linarith
    let v : ℝ → ℝ := fun y => (Real.exp y - 1)⁻¹
    have hv_le1 : v x ≤ 1 := by
      dsimp [v]
      have h2 : (2 : ℝ) ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
      exact inv_le_one_of_one_le₀ (by linarith)
    have hv_pos : 0 ≤ v x := by
      dsimp [v]; exact inv_nonneg.mpr (sub_nonneg.mpr (Real.one_le_exp hx))
    have hv_exp : v x ≤ 2 * Real.exp (-x) := by
      dsimp [v]
      have hge := exp_sub_one_ge_half_exp hx_gt1
      have hpos_den : 0 < Real.exp x / 2 := by positivity
      calc (Real.exp x - 1)⁻¹ ≤ (Real.exp x / 2)⁻¹ := inv_anti₀ hpos_den hge
        _ = 2 * Real.exp (-x) := by rw [Real.exp_neg]; field_simp [(Real.exp_pos x).ne']
    have heq_on : qFun =ᶠ[𝓝 x] fun y : ℝ => (y : ℂ) * ((v y : ℝ) : ℂ) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx_pos] with y hy
      rw [qFun_eq_div_exp_sub_one hy.ne']
      simp [v, div_eq_mul_inv, Complex.ofReal_exp]
    have hv_smooth_on : ContDiffOn ℝ (⊤ : ℕ∞) v (Ioi 0) :=
      ContDiffOn.inv ((Real.contDiff_exp.sub contDiff_const).contDiffOn.of_le le_top)
        fun y hy => (sub_pos.mpr (Real.one_lt_exp_iff.mpr hy)).ne'
    have hv_smooth : ContDiffAt ℝ r (fun y : ℝ => (v y : ℂ)) x := by
      have h1 : ContDiffAt ℝ r v x :=
        (hv_smooth_on.contDiffAt (isOpen_Ioi.mem_nhds hx_pos)).of_le (WithTop.coe_le_coe.mpr le_top)
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp x h1
    have hid_smooth : ContDiffAt ℝ r (fun y : ℝ => (y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top
    have hmul_deriv : iteratedDeriv r qFun x =
        ∑ i ∈ Finset.range (r + 1),
          ((r.choose i : ℂ) * iteratedDeriv i (fun t : ℝ => (t : ℂ)) x *
            iteratedDeriv (r - i) (fun y : ℝ => (v y : ℂ)) x) := by
      rw [heq_on.iteratedDeriv_eq r]
      simpa using iteratedDeriv_fun_mul hid_smooth hv_smooth
    have hofReal_v : ∀ k : ℕ, iteratedDeriv k (fun y : ℝ => (v y : ℂ)) x =
        ((iteratedDeriv k v x : ℝ) : ℂ) := fun k =>
      iteratedDeriv_ofReal_comp_real hv_smooth_on hx_pos
    have hval_r : ‖iteratedDeriv r v x‖ ≤ 2 * B0 * Real.exp (-x) := by
      rw [hP x hx_pos, Real.norm_eq_abs, abs_mul, abs_of_nonneg hv_pos]
      calc v x * |P.eval (v x)| ≤ (2 * Real.exp (-x)) * B0 :=
            mul_le_mul hv_exp (poly_eval_bound_unit P hv_pos hv_le1) (abs_nonneg _) (by positivity)
        _ = 2 * B0 * Real.exp (-x) := by ring
    have hbd_sum : ‖iteratedDeriv r qFun x‖ ≤
        x * (2 * B0 * Real.exp (-x)) + (r : ℝ) * (2 * B1 * Real.exp (-x)) := by
      rw [hmul_deriv]
      cases r with
      | zero =>
        simp [hofReal_v 0, abs_of_nonneg hx]
        have h0 : |v x| ≤ 2 * B0 * Real.exp (-x) := by
          simpa [iteratedDeriv_zero] using hval_r
        exact mul_le_mul_of_nonneg_left h0 hx
      | succ m =>
        have hsplit : ∑ i ∈ Finset.range (m + 2),
            ((m + 1).choose i : ℂ) * iteratedDeriv i (fun t : ℝ => (t : ℂ)) x *
              iteratedDeriv (m + 1 - i) (fun y : ℝ => (v y : ℂ)) x =
            (x : ℂ) * ((iteratedDeriv (m + 1) v x : ℝ) : ℂ) +
              ((m + 1 : ℕ) : ℂ) * ((iteratedDeriv m v x : ℝ) : ℂ) := by
          rw [Finset.sum_range_succ']
          simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero]
          rw [Finset.sum_range_succ']
          have hd1 : iteratedDeriv 1 (fun t : ℝ => (t : ℂ)) x = 1 := by
            rw [iteratedDeriv_one]; exact (hasDerivAt_id x).ofReal_comp.deriv
          have hzero : ∀ i ∈ Finset.range m,
              ((m + 1).choose (i + 1 + 1) : ℂ) *
                iteratedDeriv (i + 1 + 1) (fun t : ℝ => (t : ℂ)) x *
                iteratedDeriv (m + 1 - (i + 1 + 1)) (fun y : ℝ => (v y : ℂ)) x = 0 := by
            intro i _
            rw [iteratedDeriv_ofReal_ge_two (i + 1 + 1) (by omega) x, mul_zero, zero_mul]
          rw [Finset.sum_eq_zero hzero, zero_add, Nat.choose_one_right, hd1, mul_one,
            show m + 1 - 1 = m by omega, hofReal_v (m + 1), hofReal_v m]
          push_cast; ring
        rw [hsplit]
        have hval_m : |iteratedDeriv m v x| ≤ 2 * B1 * Real.exp (-x) := by
          have hPm := hP1 x hx_pos
          simp only [Nat.add_one_sub_one] at hPm
          rw [hPm, abs_mul, abs_of_nonneg hv_pos]
          calc v x * |P1.eval (v x)| ≤ (2 * Real.exp (-x)) * B1 :=
                mul_le_mul hv_exp (poly_eval_bound_unit P1 hv_pos hv_le1) (abs_nonneg _) (by positivity)
            _ = 2 * B1 * Real.exp (-x) := by ring
        have hval_m1 : |iteratedDeriv (m + 1) v x| ≤ 2 * B0 * Real.exp (-x) := by
          simpa [Real.norm_eq_abs] using hval_r
        calc ‖(x : ℂ) * ((iteratedDeriv (m + 1) v x : ℝ) : ℂ) +
              ((m + 1 : ℕ) : ℂ) * ((iteratedDeriv m v x : ℝ) : ℂ)‖
            ≤ ‖(x : ℂ) * ((iteratedDeriv (m + 1) v x : ℝ) : ℂ)‖ +
              ‖((m + 1 : ℕ) : ℂ) * ((iteratedDeriv m v x : ℝ) : ℂ)‖ := norm_add_le _ _
          _ = x * |iteratedDeriv (m + 1) v x| + (m + 1 : ℝ) * |iteratedDeriv m v x| := by
              simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast,
                abs_of_nonneg hx]
              push_cast; rfl
          _ ≤ x * (2 * B0 * Real.exp (-x)) + (m + 1 : ℝ) * (2 * B1 * Real.exp (-x)) := by
              gcongr
          _ = x * (2 * B0 * Real.exp (-x)) + ((m + 1 : ℕ) : ℝ) * (2 * B1 * Real.exp (-x)) := by
              push_cast; rfl
    have hx_half : x * Real.exp (-x) ≤ 2 * Real.exp (-(1 / 2) * x) := by
      have h1 := real_mul_exp_neg_le_one (by positivity : 0 ≤ (1 / 2) * x)
      have hexp : Real.exp (-x) = Real.exp (-((1 / 2) * x)) * Real.exp (-(1 / 2) * x) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp, ← mul_assoc]
      calc (x * Real.exp (-((1 / 2) * x))) * Real.exp (-(1 / 2) * x)
          = (2 * (((1 / 2) * x) * Real.exp (-((1 / 2) * x)))) * Real.exp (-(1 / 2) * x) := by ring
        _ ≤ (2 * 1) * Real.exp (-(1 / 2) * x) := by gcongr
        _ = 2 * Real.exp (-(1 / 2) * x) := by ring
    have hexp_half : Real.exp (-x) ≤ Real.exp (-(1 / 2) * x) := by
      apply Real.exp_le_exp.mpr; linarith
    calc ‖iteratedDeriv r qFun x‖
        ≤ x * (2 * B0 * Real.exp (-x)) + (r : ℝ) * (2 * B1 * Real.exp (-x)) := hbd_sum
      _ = 2 * B0 * (x * Real.exp (-x)) + (r : ℝ) * (2 * B1) * Real.exp (-x) := by ring
      _ ≤ 2 * B0 * (2 * Real.exp (-(1 / 2) * x)) + (r : ℝ) * (2 * B1) * Real.exp (-(1 / 2) * x) := by
          gcongr
      _ = C_tail * Real.exp (-(1 / 2) * x) := by dsimp [C_tail]; ring
      _ ≤ max (M0 * Real.exp (1 / 2)) C_tail * Real.exp (-(1 / 2) * x) := by
          gcongr; exact le_max_right _ _

private lemma gFun_expDecaySmooth : ExpDecaySmooth gFun :=
  qFun_expDecaySmooth.deriv

private lemma hFun_expDecaySmooth (m : ℕ) : ExpDecaySmooth (hFun m) :=
  qFun_expDecaySmooth.pow_ofReal_mul (2 * m - 1)

private lemma iteratedDeriv_gFun_zero (r : ℕ) :
    iteratedDeriv r gFun 0 = (bernoulli (r + 1) : ℂ) := by
  change iteratedDeriv r (deriv qFun) 0 = _
  rw [← iteratedDeriv_succ']
  exact iteratedDeriv_qFun_zero (r + 1)

private lemma iteratedDeriv_hFun_zero (m r : ℕ) :
    iteratedDeriv r (hFun m) 0 =
      if r < 2 * m - 1 then 0
      else ((r.factorial : ℂ) / ((r - (2 * m - 1)).factorial : ℂ)) *
        (bernoulli (r - (2 * m - 1)) : ℂ) := by
  unfold hFun
  have hpow : ContDiffAt ℝ r (fun x : ℝ => (x : ℂ) ^ (2 * m - 1)) 0 :=
    (Complex.ofRealCLM.contDiff.pow (2 * m - 1)).contDiffAt.of_le le_top
  have hq : ContDiffAt ℝ r qFun 0 := qFun_contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDeriv_fun_mul hpow hq]
  have hid : ∀ i : ℕ, iteratedDeriv i (fun x : ℝ => (x : ℂ) ^ (2 * m - 1)) 0 =
      if i = 2 * m - 1 then ((2 * m - 1).factorial : ℂ) else 0 := fun i => by
    have hcomp := iteratedDeriv_ofReal_comp (F := fun z : ℂ => z ^ (2 * m - 1))
      (fun _ => by fun_prop) i 0
    change iteratedDeriv i (fun x : ℝ => (fun z : ℂ => z ^ (2 * m - 1)) (x : ℂ)) 0 = _
    rw [hcomp, iteratedDeriv_pow]
    by_cases hi : i = 2 * m - 1
    · subst hi; simp [Nat.descFactorial_self]
    · simp only [hi, ↓reduceIte]
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · have hne : 2 * m - 1 - i ≠ 0 := by omega
        simp [zero_pow hne]
      · simp [Nat.descFactorial_of_lt hgt]
  split_ifs with hlt
  · refine Finset.sum_eq_zero fun i hi => ?_
    have hi_lt : i < 2 * m - 1 := (Finset.mem_range.mp hi).trans_le (by omega)
    simp [hid i, hi_lt.ne]
  · have hle : 2 * m - 1 ≤ r := by omega
    rw [Finset.sum_eq_single (2 * m - 1)]
    · rw [hid (2 * m - 1)]
      simp only [↓reduceIte, iteratedDeriv_qFun_zero]
      have hch := congrArg (fun k : ℕ => (k : ℂ)) (Nat.choose_mul_factorial_mul_factorial hle)
      push_cast at hch
      have hfac1 : ((2 * m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      have hfac2 : ((r - (2 * m - 1)).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      field_simp [hfac1, hfac2]
      linear_combination hch * (bernoulli (r - (2 * m - 1)) : ℂ)
    · intro i _ hine
      simp [hid i, hine]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (by omega)) hnot

/-! ### 4. 1-D Euler–Maclaurin Summation & All-Orders Derivative Asymptotics -/

private lemma ExpDecaySmooth.continuous {h : ℝ → ℂ} (hh : ExpDecaySmooth h) :
    Continuous h := hh.1.continuous

private lemma ExpDecaySmooth.differentiable {h : ℝ → ℂ} (hh : ExpDecaySmooth h) :
    Differentiable ℝ h := (contDiff_infty_iff_deriv.mp hh.1).1

private lemma ExpDecaySmooth.iteratedDeriv_smooth {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (r : ℕ) :
    ExpDecaySmooth (_root_.iteratedDeriv r h) := by
  induction r generalizing h with
  | zero => simpa using hh
  | succ r ih =>
    rw [iteratedDeriv_succ']
    exact ih hh.deriv

private lemma integrableOn_of_expDecaySmooth {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (r : ℕ) :
    IntegrableOn (iteratedDeriv r h) (Ioi (0 : ℝ)) := by
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 r
  have hint_exp : IntegrableOn (fun x : ℝ => C * Real.exp (-c * x)) (Ioi (0 : ℝ)) :=
    (integrableOn_exp_mul_Ioi (by linarith) (0 : ℝ)).const_mul C
  refine hint_exp.mono' (hh.iteratedDeriv_smooth r).continuous.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hle := hbd x (le_of_lt hx)
  simpa [Real.norm_of_nonneg (mul_nonneg hC (Real.exp_pos _).le)] using hle

private lemma tendsto_expDecaySmooth_atTop {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (r : ℕ) :
    Tendsto (iteratedDeriv r h) atTop (𝓝 0) := by
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 r
  have hlim : Tendsto (fun x : ℝ => C * Real.exp (-c * x)) atTop (𝓝 0) := by
    simpa [mul_zero] using tendsto_const_nhds.mul
      (Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop (by linarith : -c < 0) tendsto_id))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  exact hbd x hx

private lemma hasAsympExp_const_mul (c : ℂ) {f : ℝ → ℂ} {S : PowerSeries ℂ}
    (hf : HasAsympExp f S) :
    HasAsympExp (fun u => c * f u) (PowerSeries.C c * S) :=
  (HasAsympExp.const c).mul hf

private lemma hasAsympExp_sub {f g : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExp f S) (hg : HasAsympExp g T) :
    HasAsympExp (fun u => f u - g u) (S - T) := by
  have heq_f : (fun u => f u - g u) = fun u => f u + (-1 : ℂ) * g u := by
    funext u; ring
  have heq_S : S - T = S + PowerSeries.C (-1 : ℂ) * T := by
    rw [map_neg, map_one, neg_one_mul, sub_eq_add_neg]
  rw [heq_f, heq_S]
  exact hf.add (hasAsympExp_const_mul (-1) hg)

private lemma hasAsympExp_unique {f : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExp f S) (hg : HasAsympExp f T) : S = T := by
  have h0 : HasAsympExp (fun _ : ℝ => (0 : ℂ)) (S - T) := by
    simpa [sub_self] using hasAsympExp_sub hf hg
  have hflat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in atTop, ‖(0 : ℂ)‖ ≤ C / u ^ M := fun _ =>
    ⟨0, Eventually.of_forall fun _ => by simp⟩
  exact sub_eq_zero.mp (h0.eq_zero_of_flat hflat)

private lemma hasAsympExp_inv_pow (k : ℕ) :
    HasAsympExp (fun u : ℝ => (u : ℂ)⁻¹ ^ k) (PowerSeries.X ^ k) := by
  intro M
  by_cases hkM : k < M
  · refine ⟨0, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hsum : ∑ j ∈ Finset.range M, PowerSeries.coeff j (PowerSeries.X ^ k : PowerSeries ℂ) *
        (u : ℂ)⁻¹ ^ j = (u : ℂ)⁻¹ ^ k := by
      rw [Finset.sum_eq_single k]
      · simp [PowerSeries.coeff_X_pow]
      · intro j _ hjk; simp [PowerSeries.coeff_X_pow, hjk]
      · intro hnot; exact absurd (Finset.mem_range.mpr hkM) hnot
    rw [hsum, sub_self, norm_zero, zero_div]
  · refine ⟨1, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
    have hsum : ∑ j ∈ Finset.range M, PowerSeries.coeff j (PowerSeries.X ^ k : PowerSeries ℂ) *
        (u : ℂ)⁻¹ ^ j = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hjk : j ≠ k := by
        have hjlt := Finset.mem_range.mp hj
        omega
      simp [PowerSeries.coeff_X_pow, hjk]
    rw [hsum, sub_zero, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith), _root_.inv_pow, one_div]
    refine inv_anti₀ (by positivity) ?_
    exact pow_le_pow_right₀ hu (by omega)

private lemma hasAsympExp_inv_pow_mul (k : ℕ) {f : ℝ → ℂ} {S : PowerSeries ℂ}
    (hf : HasAsympExp f S) :
    HasAsympExp (fun u : ℝ => (u : ℂ)⁻¹ ^ k * f u) (PowerSeries.X ^ k * S) :=
  (hasAsympExp_inv_pow k).mul hf

private lemma hasDerivAt_inv_pow_complex {j : ℕ} {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun v : ℝ => (v : ℂ)⁻¹ ^ j) (-(j : ℂ) * (y : ℂ)⁻¹ ^ (j + 1)) y := by
  have h0 : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 y := by
    simpa using (hasDerivAt_id y).ofReal_comp
  have h1 : HasDerivAt (fun v : ℝ => (v : ℂ)⁻¹) (-((y : ℂ)⁻¹ ^ 2)) y := by
    refine (h0.inv (Complex.ofReal_ne_zero.mpr hy)).congr_deriv ?_
    ring
  have h2 := h1.pow j
  refine h2.congr_deriv ?_
  cases j with
  | zero => simp
  | succ k =>
    rw [Nat.add_one_sub_one, show k + 1 + 1 = k + 2 by omega, pow_add _ k 2]
    push_cast; ring

private lemma intervalIntegral_inv_pow_real {m : ℕ} {u R : ℝ} (hu : 0 < u) (hR : u ≤ R) :
    ∫ x in u..R, (1 : ℝ) / x ^ (m + 2) =
      ((m + 1 : ℕ) : ℝ)⁻¹ * (u⁻¹ ^ (m + 1) - R⁻¹ ^ (m + 1)) := by
  let F : ℝ → ℝ := fun x => -(((m + 1 : ℕ) : ℝ)⁻¹ * x⁻¹ ^ (m + 1))
  have hF : ∀ x ∈ [[u, R]], HasDerivAt F ((1 : ℝ) / x ^ (m + 2)) x := fun x hx => by
    rw [Set.uIcc_of_le hR] at hx
    have hx_pos : 0 < x := hu.trans_le hx.1
    have h1 : HasDerivAt (fun y : ℝ => y⁻¹ ^ (m + 1))
        (-(m + 1 : ℝ) * x⁻¹ ^ (m + 2)) x := by
      have hinv : HasDerivAt (fun y : ℝ => y⁻¹) (-(x⁻¹ ^ 2)) x := by
        refine (hasDerivAt_inv hx_pos.ne').congr_deriv ?_
        ring
      refine (hinv.pow (m + 1)).congr_deriv ?_
      rw [Nat.add_one_sub_one, pow_add x⁻¹ m 2]
      push_cast; ring
    have h2 := (h1.const_mul (((m + 1 : ℕ) : ℝ)⁻¹)).neg
    refine h2.congr_deriv ?_
    have hm0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [one_div, ← _root_.inv_pow]
    push_cast
    field_simp [hm0]
  have hint : IntervalIntegrable (fun x : ℝ => (1 : ℝ) / x ^ (m + 2)) volume u R := by
    refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
    have hx_ne : x ^ (m + 2) ≠ 0 := pow_ne_zero _ (hu.trans_le hx.1).ne'
    exact (continuousAt_const.div (continuousAt_id.pow _) hx_ne).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  dsimp only [F]
  ring

private lemma intervalIntegral_inv_pow_complex {m : ℕ} {u R : ℝ} (hu : 0 < u) (hR : u ≤ R) :
    ∫ x in u..R, (x : ℂ)⁻¹ ^ (m + 2) =
      (((m + 1 : ℕ) : ℂ)⁻¹ * ((u : ℂ)⁻¹ ^ (m + 1) - (R : ℂ)⁻¹ ^ (m + 1))) := by
  let F : ℝ → ℂ := fun x => -(((m + 1 : ℕ) : ℂ)⁻¹ * (x : ℂ)⁻¹ ^ (m + 1))
  have hF : ∀ x ∈ [[u, R]], HasDerivAt F ((x : ℂ)⁻¹ ^ (m + 2)) x := fun x hx => by
    rw [Set.uIcc_of_le hR] at hx
    have hx_pos : 0 < x := hu.trans_le hx.1
    have h1 := (hasDerivAt_inv_pow_complex (j := m + 1) hx_pos.ne').const_mul (((m + 1 : ℕ) : ℂ)⁻¹)
    refine h1.neg.congr_deriv ?_
    have hm0 : ((m + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    push_cast
    field_simp [hm0]
  have hint : IntervalIntegrable (fun x : ℝ => (x : ℂ)⁻¹ ^ (m + 2)) volume u R := by
    refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
    have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu.trans_le hx.1).ne'
    exact (((Complex.continuous_ofReal.continuousAt.inv₀ hxc).pow (m + 2))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF hint]
  dsimp only [F]
  ring

private lemma tendsto_log_div_self_atTop :
    Tendsto (fun R : ℝ => Real.log R / R) atTop (𝓝 0) := by
  have hbd : ∀ᶠ R : ℝ in atTop, ‖Real.log R / R‖ ≤ 2 / Real.sqrt R := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    have hR0 : 0 < R := by linarith
    have hs : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
    have hlog_nn : 0 ≤ Real.log R := Real.log_nonneg hR
    have hle_sqrt : Real.log (Real.sqrt R) ≤ Real.sqrt R := by
      linarith [Real.log_le_sub_one_of_pos hs]
    have hlog2 : Real.log R = 2 * Real.log (Real.sqrt R) := by
      have hsq : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0.le
      rw [← hsq, Real.log_pow]
      norm_num
    rw [Real.norm_of_nonneg (div_nonneg hlog_nn hR0.le), hlog2]
    have hR_eq : R = Real.sqrt R * Real.sqrt R := (Real.mul_self_sqrt hR0.le).symm
    calc 2 * Real.log (Real.sqrt R) / R
        ≤ 2 * Real.sqrt R / R := by gcongr
      _ = 2 * Real.sqrt R / (Real.sqrt R * Real.sqrt R) := by rw [← hR_eq]
      _ = 2 / Real.sqrt R := by field_simp [hs.ne']
  have hlim : Tendsto (fun R : ℝ => 2 / Real.sqrt R) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop)
  exact squeeze_zero_norm' hbd hlim

private lemma coeff_d_u (S : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.coeff n (d_u S) = match n with
      | 0 => 0
      | 1 => 0
      | k + 2 => -(((k + 1 : ℕ) : ℂ) * PowerSeries.coeff (k + 1) S) := by
  rw [d_u, map_neg]
  rcases n with _ | _ | k
  · simp [PowerSeries.coeff_mul, PowerSeries.coeff_X_pow]
  · simp [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, PowerSeries.coeff_X_pow]
  · change -(PowerSeries.coeff (k + 2) (PowerSeries.X ^ 2 * PowerSeries.derivative S)) =
      -(((k + 1 : ℕ) : ℂ) * PowerSeries.coeff (k + 1) S)
    rw [PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_derivative]
    push_cast; ring

private lemma HasAsympExp.deriv_of_hasAsympExp {f : ℝ → ℂ} {S T : PowerSeries ℂ}
    (hf : HasAsympExp f S) (hdf : HasAsympExp (deriv f) T)
    (hsmooth : ∀ᶠ u : ℝ in atTop, DifferentiableAt ℝ f u ∧ ContinuousAt (deriv f) u) :
    T = d_u S := by
  obtain ⟨u_sm, hu_sm⟩ := eventually_atTop.mp hsmooth
  obtain ⟨Cf1, hCf1⟩ := hf 1
  obtain ⟨u_f1, hu_f1⟩ := eventually_atTop.mp hCf1
  obtain ⟨Ct2, hCt2⟩ := hdf 2
  obtain ⟨u_t2, hu_t2⟩ := eventually_atTop.mp hCt2
  let u0 : ℝ := max (max u_sm 1) (max u_f1 u_t2)
  have hu0_pos : 0 < u0 := by
    have : 1 ≤ u0 := (le_max_right u_sm 1).trans (le_max_left _ _)
    linarith
  have hftc : ∀ u R : ℝ, u0 ≤ u → u ≤ R →
      f R - f u = ∫ x in u..R, deriv f x := fun u R hu hR => by
    have hderiv : ∀ x ∈ [[u, R]], HasDerivAt f (deriv f x) x := fun x hx => by
      rw [Set.uIcc_of_le hR] at hx
      have hge : u_sm ≤ x := ((le_max_left u_sm 1).trans (le_max_left _ _)).trans (hu.trans hx.1)
      exact (hu_sm x hge).1.hasDerivAt
    have hint : IntervalIntegrable (deriv f) volume u R := by
      refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
      have hge : u_sm ≤ x := ((le_max_left u_sm 1).trans (le_max_left _ _)).trans (hu.trans hx.1)
      exact (hu_sm x hge).2.continuousWithinAt
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint).symm
  let b0 : ℂ := PowerSeries.coeff 0 T
  let b1 : ℂ := PowerSeries.coeff 1 T
  let a0 : ℂ := PowerSeries.coeff 0 S
  have hmain_bound : ∀ R : ℝ, u0 ≤ R →
      ‖b0 * ((R : ℂ) - (u0 : ℂ)) + b1 * ((Real.log R : ℂ) - (Real.log u0 : ℂ))‖ ≤
        (2 * max Cf1 0 + max Ct2 0) / u0 := by
    intro R hR
    have hf_R : ‖f R - a0‖ ≤ Cf1 / R := by
      have h := hu_f1 R (((le_max_left u_f1 u_t2).trans (le_max_right _ _)).trans hR)
      simpa [Finset.range_one, a0] using h
    have hf_u0 : ‖f u0 - a0‖ ≤ Cf1 / u0 := by
      have h := hu_f1 u0 ((le_max_left u_f1 u_t2).trans (le_max_right _ _))
      simpa [Finset.range_one, a0] using h
    have hf_diff : ‖f R - f u0‖ ≤ 2 * max Cf1 0 / u0 := by
      have hRu0_pos : 0 < R := hu0_pos.trans_le hR
      have h1 : Cf1 / R ≤ max Cf1 0 / R := div_le_div_of_nonneg_right (le_max_left Cf1 0) hRu0_pos.le
      have h2 : Cf1 / u0 ≤ max Cf1 0 / u0 := div_le_div_of_nonneg_right (le_max_left Cf1 0) hu0_pos.le
      have h3 : max Cf1 0 / R ≤ max Cf1 0 / u0 := div_le_div_of_nonneg_left (le_max_right Cf1 0) hu0_pos hR
      calc ‖f R - f u0‖ = ‖(f R - a0) - (f u0 - a0)‖ := by congr 1; ring
        _ ≤ ‖f R - a0‖ + ‖f u0 - a0‖ := norm_sub_le _ _
        _ ≤ Cf1 / R + Cf1 / u0 := add_le_add hf_R hf_u0
        _ ≤ max Cf1 0 / R + max Cf1 0 / u0 := add_le_add h1 h2
        _ ≤ max Cf1 0 / u0 + max Cf1 0 / u0 := add_le_add h3 le_rfl
        _ = 2 * max Cf1 0 / u0 := by ring
    let p2 : ℝ → ℂ := fun x => b0 + b1 * (x : ℂ)⁻¹
    have hp2_int : ∫ x in u0..R, p2 x =
        b0 * ((R : ℂ) - (u0 : ℂ)) + b1 * ((Real.log R : ℂ) - (Real.log u0 : ℂ)) := by
      let P : ℝ → ℂ := fun x => b0 * (x : ℂ) + b1 * (Real.log x : ℂ)
      have hP : ∀ x ∈ [[u0, R]], HasDerivAt P (p2 x) x := fun x hx => by
        rw [Set.uIcc_of_le hR] at hx
        have hx_pos : 0 < x := hu0_pos.trans_le hx.1
        have hd1 : HasDerivAt (fun y : ℝ => b0 * (y : ℂ)) b0 x := by
          simpa using ((hasDerivAt_id x).ofReal_comp).const_mul b0
        have hd2 : HasDerivAt (fun y : ℝ => b1 * (Real.log y : ℂ)) (b1 * (x : ℂ)⁻¹) x := by
          have hl := (Real.hasDerivAt_log hx_pos.ne').ofReal_comp
          simpa [Function.comp_def, Complex.ofReal_inv] using hl.const_mul b1
        exact hd1.add hd2
      have hint_p2 : IntervalIntegrable p2 volume u0 R := by
        refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
        have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu0_pos.trans_le hx.1).ne'
        exact (continuousAt_const.add
          (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.inv₀ hxc))).continuousWithinAt
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hP hint_p2]
      dsimp only [P]; ring
    have hrem_bd : ‖∫ x in u0..R, (deriv f x - p2 x)‖ ≤ max Ct2 0 / u0 := by
      have hint_rem : IntervalIntegrable (fun x => deriv f x - p2 x) volume u0 R := by
        have h1 : IntervalIntegrable (deriv f) volume u0 R := by
          refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
          have hge : u_sm ≤ x := ((le_max_left u_sm 1).trans (le_max_left _ _)).trans hx.1
          exact (hu_sm x hge).2.continuousWithinAt
        have h2 : IntervalIntegrable p2 volume u0 R := by
          refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
          have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu0_pos.trans_le hx.1).ne'
          exact (continuousAt_const.add
            (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.inv₀ hxc))).continuousWithinAt
        exact h1.sub h2
      have hint_dom : IntervalIntegrable (fun x : ℝ => max Ct2 0 * (1 / x ^ 2)) volume u0 R := by
        refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
        have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 (hu0_pos.trans_le hx.1).ne'
        exact (continuousAt_const.mul (continuousAt_const.div (continuousAt_id.pow 2) hx2)).continuousWithinAt
      have hmono : ∫ x in u0..R, ‖deriv f x - p2 x‖ ≤
          ∫ x in u0..R, max Ct2 0 * (1 / x ^ 2) := by
        refine intervalIntegral.integral_mono_on hR hint_rem.norm hint_dom fun x hx => ?_
        have hge : u_t2 ≤ x := ((le_max_right u_f1 u_t2).trans (le_max_right _ _)).trans hx.1
        have h := hu_t2 x hge
        have hsum : ∑ k ∈ Finset.range 2, PowerSeries.coeff k T * (x : ℂ)⁻¹ ^ k = p2 x := by
          rw [Finset.sum_range_succ, Finset.sum_range_one]
          simp [p2, b0, b1]
        rw [hsum] at h
        have h' := h.trans (div_le_div_of_nonneg_right (le_max_left Ct2 0) (by positivity))
        simpa [one_div, div_eq_mul_inv] using h'
      have hdom_eval : ∫ x in u0..R, max Ct2 0 * (1 / x ^ 2) =
          max Ct2 0 * (u0⁻¹ - R⁻¹) := by
        rw [intervalIntegral.integral_const_mul]
        have hi := intervalIntegral_inv_pow_real (m := 0) hu0_pos hR
        simpa using congrArg (fun z => max Ct2 0 * z) hi
      calc ‖∫ x in u0..R, (deriv f x - p2 x)‖
          ≤ ∫ x in u0..R, ‖deriv f x - p2 x‖ := intervalIntegral.norm_integral_le_integral_norm hR
        _ ≤ ∫ x in u0..R, max Ct2 0 * (1 / x ^ 2) := hmono
        _ = max Ct2 0 * (u0⁻¹ - R⁻¹) := hdom_eval
        _ ≤ max Ct2 0 * u0⁻¹ := by
            have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr (hu0_pos.trans_le hR).le
            exact mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)
        _ = max Ct2 0 / u0 := by rw [div_eq_mul_inv]
    have hsplit_int : ∫ x in u0..R, deriv f x =
        (∫ x in u0..R, p2 x) + ∫ x in u0..R, (deriv f x - p2 x) := by
      have hint1 : IntervalIntegrable p2 volume u0 R := by
        refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
        have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu0_pos.trans_le hx.1).ne'
        exact (continuousAt_const.add
          (continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.inv₀ hxc))).continuousWithinAt
      have hint2 : IntervalIntegrable (deriv f) volume u0 R := by
        refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
        have hge : u_sm ≤ x := ((le_max_left u_sm 1).trans (le_max_left _ _)).trans hx.1
        exact (hu_sm x hge).2.continuousWithinAt
      rw [← intervalIntegral.integral_add hint1 (hint2.sub hint1)]
      refine intervalIntegral.integral_congr fun x _ => by ring
    have heq_p2 : b0 * ((R : ℂ) - (u0 : ℂ)) + b1 * ((Real.log R : ℂ) - (Real.log u0 : ℂ)) =
        (f R - f u0) - ∫ x in u0..R, (deriv f x - p2 x) := by
      rw [← hp2_int, hftc u0 R le_rfl hR, hsplit_int]
      ring
    calc ‖b0 * ((R : ℂ) - (u0 : ℂ)) + b1 * ((Real.log R : ℂ) - (Real.log u0 : ℂ))‖
        = ‖(f R - f u0) - ∫ x in u0..R, (deriv f x - p2 x)‖ := by rw [heq_p2]
      _ ≤ ‖f R - f u0‖ + ‖∫ x in u0..R, (deriv f x - p2 x)‖ := norm_sub_le _ _
      _ ≤ 2 * max Cf1 0 / u0 + max Ct2 0 / u0 := add_le_add hf_diff hrem_bd
      _ = (2 * max Cf1 0 + max Ct2 0) / u0 := by ring
  let K : ℝ := (2 * max Cf1 0 + max Ct2 0) / u0
  have hb0 : b0 = 0 := by
    have hdivR : ∀ᶠ R : ℝ in atTop,
        ‖b0 * (1 - ((u0 / R : ℝ) : ℂ)) + b1 * (((Real.log R / R : ℝ) : ℂ) - ((Real.log u0 / R : ℝ) : ℂ))‖ ≤
          K / R := by
      filter_upwards [eventually_ge_atTop (max u0 1)] with R hR
      have hRu0 : u0 ≤ R := (le_max_left u0 1).trans hR
      have hRpos : 0 < R := by linarith [le_max_right u0 1 |>.trans hR]
      have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRpos.ne'
      have hmul : ‖(R : ℂ)⁻¹ * (b0 * ((R : ℂ) - (u0 : ℂ)) +
          b1 * ((Real.log R : ℂ) - (Real.log u0 : ℂ)))‖ ≤ K / R := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, inv_mul_eq_div]
        exact div_le_div_of_nonneg_right (hmain_bound R hRu0) hRpos.le
      refine (le_of_eq ?_).trans hmul
      congr 1
      push_cast
      field_simp [hRc]
    have hlimL : Tendsto (fun R : ℝ =>
        ‖b0 * (1 - ((u0 / R : ℝ) : ℂ)) + b1 * (((Real.log R / R : ℝ) : ℂ) - ((Real.log u0 / R : ℝ) : ℂ))‖)
        atTop (𝓝 ‖b0‖) := by
      have h1 : Tendsto (fun R : ℝ => u0 / R) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have h2 : Tendsto (fun R : ℝ => Real.log u0 / R) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hc1 : Tendsto (fun R : ℝ => 1 - ((u0 / R : ℝ) : ℂ)) atTop (𝓝 (1 - ((0 : ℝ) : ℂ))) :=
        tendsto_const_nhds.sub (Complex.continuous_ofReal.continuousAt.tendsto.comp h1)
      have hc2 : Tendsto (fun R : ℝ => ((Real.log R / R : ℝ) : ℂ) - ((Real.log u0 / R : ℝ) : ℂ))
          atTop (𝓝 (((0 : ℝ) : ℂ) - ((0 : ℝ) : ℂ))) :=
        (Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_log_div_self_atTop).sub
          (Complex.continuous_ofReal.continuousAt.tendsto.comp h2)
      have htot := ((tendsto_const_nhds (x := b0)).mul hc1).add ((tendsto_const_nhds (x := b1)).mul hc2)
      simpa using htot.norm
    have hlimR : Tendsto (fun R : ℝ => K / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have hle0 : ‖b0‖ ≤ 0 := le_of_tendsto_of_tendsto hlimL hlimR hdivR
    exact norm_le_zero_iff.mp hle0
  have hb1 : b1 = 0 := by
    have hdivLog : ∀ᶠ R : ℝ in atTop,
        ‖b1 * (1 - ((Real.log u0 / Real.log R : ℝ) : ℂ))‖ ≤ K / Real.log R := by
      filter_upwards [eventually_ge_atTop (max u0 2)] with R hR
      have hRu0 : u0 ≤ R := (le_max_left u0 2).trans hR
      have hR1 : 1 < R := by linarith [le_max_right u0 2 |>.trans hR]
      have hlog_pos : 0 < Real.log R := Real.log_pos hR1
      have hlog_c : (Real.log R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlog_pos.ne'
      have hbd := hmain_bound R hRu0
      rw [hb0, zero_mul, zero_add] at hbd
      have hmul : ‖(Real.log R : ℂ)⁻¹ * (b1 * ((Real.log R : ℂ) - (Real.log u0 : ℂ)))‖ ≤
          K / Real.log R := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog_pos, inv_mul_eq_div]
        exact div_le_div_of_nonneg_right hbd hlog_pos.le
      refine (le_of_eq ?_).trans hmul
      congr 1
      push_cast
      field_simp [hlog_c]
    have hlimL : Tendsto (fun R : ℝ => ‖b1 * (1 - ((Real.log u0 / Real.log R : ℝ) : ℂ))‖)
        atTop (𝓝 ‖b1‖) := by
      have h1 : Tendsto (fun R : ℝ => Real.log u0 / Real.log R) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
      have hc1 : Tendsto (fun R : ℝ => 1 - ((Real.log u0 / Real.log R : ℝ) : ℂ)) atTop
          (𝓝 (1 - ((0 : ℝ) : ℂ))) :=
        tendsto_const_nhds.sub (Complex.continuous_ofReal.continuousAt.tendsto.comp h1)
      simpa using ((tendsto_const_nhds (x := b1)).mul hc1).norm
    have hlimR : Tendsto (fun R : ℝ => K / Real.log R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto hlimL hlimR hdivLog)
  ext n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simp [coeff_d_u, b0, hb0]
    | 1 => simp [coeff_d_u, b1, hb1]
    | k + 2 =>
      have hd_coeff : PowerSeries.coeff (k + 2) (d_u S) =
          -(((k + 1 : ℕ) : ℂ) * PowerSeries.coeff (k + 1) S) := coeff_d_u S (k + 2)
      rw [hd_coeff]
      obtain ⟨Ct, hCt⟩ := hdf (k + 3)
      obtain ⟨u_t, hu_t⟩ := eventually_atTop.mp hCt
      obtain ⟨Cf, hCf⟩ := hf (k + 2)
      obtain ⟨u_f, hu_f⟩ := eventually_atTop.mp hCf
      let C_t : ℝ := max Ct 0
      let C_f : ℝ := max Cf 0
      let U : ℝ := max u0 (max u_t u_f)
      have h_u_bd : ∀ u : ℝ, U ≤ u →
          ‖(PowerSeries.coeff (k + 1) S +
              PowerSeries.coeff (k + 2) T / ((k + 1 : ℕ) : ℂ)) * (u : ℂ)⁻¹ ^ (k + 1)‖ ≤
            (C_f + C_t / ((k + 2 : ℕ) : ℝ)) / u ^ (k + 2) := by
        intro u hu
        have hu0 : u0 ≤ u := (le_max_left _ _).trans hu
        have hu_pos : 0 < u := hu0_pos.trans_le hu0
        have hut : u_t ≤ u := ((le_max_left _ _).trans (le_max_right _ _)).trans hu
        have huf : u_f ≤ u := ((le_max_right _ _).trans (le_max_right _ _)).trans hu
        let q : ℝ → ℂ := fun x =>
          ∑ j ∈ Finset.Ico 2 (k + 3), PowerSeries.coeff j T * (x : ℂ)⁻¹ ^ j
        have hq_eq : ∀ x : ℝ, ∑ j ∈ Finset.range (k + 3), PowerSeries.coeff j T * (x : ℂ)⁻¹ ^ j =
            q x := fun x => by
          have hsub : Finset.range (k + 3) = {0, 1} ∪ Finset.Ico 2 (k + 3) := by
            ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_insert,
              Finset.mem_singleton, Finset.mem_Ico]; omega
          rw [hsub, Finset.sum_union (by simp), Finset.sum_pair (by omega)]
          simp [b0, b1, hb0, hb1, q]
        have hR_bound : ∀ R : ℝ, u ≤ R →
            ‖(f R - f u) - ∑ j ∈ Finset.Ico 2 (k + 3),
                PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ *
                  ((u : ℂ)⁻¹ ^ (j - 1) - (R : ℂ)⁻¹ ^ (j - 1)))‖ ≤
              (C_t / ((k + 2 : ℕ) : ℝ)) / u ^ (k + 2) := by
          intro R hR
          have hint_term : ∀ j ∈ Finset.Ico 2 (k + 3),
              IntervalIntegrable (fun x : ℝ => PowerSeries.coeff j T * (x : ℂ)⁻¹ ^ j) volume u R :=
            fun j _ => by
              refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
              have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu_pos.trans_le hx.1).ne'
              exact (continuousAt_const.mul ((Complex.continuous_ofReal.continuousAt.inv₀ hxc).pow j)).continuousWithinAt
          have hq_int : ∫ x in u..R, q x =
              ∑ j ∈ Finset.Ico 2 (k + 3),
                PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ *
                  ((u : ℂ)⁻¹ ^ (j - 1) - (R : ℂ)⁻¹ ^ (j - 1))) := by
            dsimp only [q]
            rw [intervalIntegral.integral_finsetSum hint_term]
            refine Finset.sum_congr rfl fun j hj => ?_
            have hj2 : 2 ≤ j := (Finset.mem_Ico.mp hj).1
            rw [intervalIntegral.integral_const_mul]
            have hintj := intervalIntegral_inv_pow_complex (m := j - 2) hu_pos hR
            rw [show j - 2 + 2 = j by omega, show j - 2 + 1 = j - 1 by omega] at hintj
            rw [hintj]
          have hint_q : IntervalIntegrable q volume u R := by
            have hq_fun : q = ∑ j ∈ Finset.Ico 2 (k + 3),
                fun x : ℝ => PowerSeries.coeff j T * (x : ℂ)⁻¹ ^ j := by
              ext x; simp [q]
            rw [hq_fun]
            exact IntervalIntegrable.sum (Finset.Ico 2 (k + 3)) hint_term
          have hint_df : IntervalIntegrable (deriv f) volume u R := by
            refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
            have hge : u_sm ≤ x := ((le_max_left u_sm 1).trans (le_max_left _ _)).trans (hu0.trans hx.1)
            exact (hu_sm x hge).2.continuousWithinAt
          have hsplit : ∫ x in u..R, deriv f x = (∫ x in u..R, q x) + ∫ x in u..R, (deriv f x - q x) := by
            rw [← intervalIntegral.integral_add hint_q (hint_df.sub hint_q)]
            refine intervalIntegral.integral_congr fun x _ => by ring
          have heq_sub : (f R - f u) - ∑ j ∈ Finset.Ico 2 (k + 3),
                PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ *
                  ((u : ℂ)⁻¹ ^ (j - 1) - (R : ℂ)⁻¹ ^ (j - 1))) =
              ∫ x in u..R, (deriv f x - q x) := by
            rw [← hq_int, hftc u R hu0 hR, hsplit]
            ring
          rw [heq_sub]
          have hint_dom : IntervalIntegrable (fun x : ℝ => C_t * (1 / x ^ (k + 3))) volume u R := by
            refine ContinuousOn.intervalIntegrable_of_Icc hR fun x hx => ?_
            have hx_ne : x ^ (k + 3) ≠ 0 := pow_ne_zero _ (hu_pos.trans_le hx.1).ne'
            exact (continuousAt_const.mul (continuousAt_const.div (continuousAt_id.pow _) hx_ne)).continuousWithinAt
          have hmono : ∫ x in u..R, ‖deriv f x - q x‖ ≤
              ∫ x in u..R, C_t * (1 / x ^ (k + 3)) := by
            refine intervalIntegral.integral_mono_on hR (hint_df.sub hint_q).norm hint_dom fun x hx => ?_
            have hge : u_t ≤ x := hut.trans hx.1
            have hx_pos : 0 < x := hu_pos.trans_le hx.1
            have h := hu_t x hge
            rw [hq_eq x] at h
            have h' := h.trans (div_le_div_of_nonneg_right (le_max_left Ct 0) (by positivity))
            simpa [one_div, div_eq_mul_inv] using h'
          have hdom_eval : ∫ x in u..R, C_t * (1 / x ^ (k + 3)) =
              C_t * (((k + 2 : ℕ) : ℝ)⁻¹ * (u⁻¹ ^ (k + 2) - R⁻¹ ^ (k + 2))) := by
            rw [intervalIntegral.integral_const_mul]
            exact congrArg (fun z => C_t * z) (intervalIntegral_inv_pow_real (m := k + 1) hu_pos hR)
          have hk2_pos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
          calc ‖∫ x in u..R, (deriv f x - q x)‖
              ≤ ∫ x in u..R, ‖deriv f x - q x‖ := intervalIntegral.norm_integral_le_integral_norm hR
            _ ≤ ∫ x in u..R, C_t * (1 / x ^ (k + 3)) := hmono
            _ = C_t * (((k + 2 : ℕ) : ℝ)⁻¹ * (u⁻¹ ^ (k + 2) - R⁻¹ ^ (k + 2))) := hdom_eval
            _ ≤ C_t * (((k + 2 : ℕ) : ℝ)⁻¹ * u⁻¹ ^ (k + 2)) := by
                have hRinv : 0 ≤ R⁻¹ ^ (k + 2) := pow_nonneg (inv_nonneg.mpr (hu_pos.trans_le hR).le) _
                exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hk2_pos.le))
                  (le_max_right _ _)
            _ = (C_t / ((k + 2 : ℕ) : ℝ)) / u ^ (k + 2) := by
                rw [_root_.inv_pow]; ring
        have hlim_a0 : Tendsto f atTop (𝓝 a0) := by
          have h_bd : ∀ᶠ R : ℝ in atTop, ‖f R - a0‖ ≤ max Cf1 0 / R := by
            filter_upwards [eventually_ge_atTop (max u_f1 1)] with R hR
            have h := hu_f1 R ((le_max_left u_f1 1).trans hR)
            have hRpos : 0 < R := by linarith [(le_max_right u_f1 1).trans hR]
            simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_one] at h
            rw [pow_one] at h
            exact h.trans (div_le_div_of_nonneg_right (le_max_left Cf1 0) hRpos.le)
          have hlim_0 : Tendsto (fun R : ℝ => max Cf1 0 / R) atTop (𝓝 0) :=
            tendsto_const_nhds.div_atTop tendsto_id
          have hsub0 : Tendsto (fun R : ℝ => f R - a0) atTop (𝓝 0) :=
            squeeze_zero_norm' h_bd hlim_0
          have h_add : Tendsto (fun R : ℝ => (f R - a0) + a0) atTop (𝓝 (0 + a0)) :=
            hsub0.add tendsto_const_nhds
          simpa using h_add
        have hlim_lhs : Tendsto (fun R : ℝ =>
            ‖(f R - f u) - ∑ j ∈ Finset.Ico 2 (k + 3),
              PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ *
                ((u : ℂ)⁻¹ ^ (j - 1) - (R : ℂ)⁻¹ ^ (j - 1)))‖)
            atTop
            (𝓝 ‖(a0 - f u) - ∑ j ∈ Finset.Ico 2 (k + 3),
              PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ (j - 1))‖) := by
          have hlim_sum : Tendsto (fun R : ℝ => ∑ j ∈ Finset.Ico 2 (k + 3),
              PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ *
                ((u : ℂ)⁻¹ ^ (j - 1) - (R : ℂ)⁻¹ ^ (j - 1))))
              atTop
              (𝓝 (∑ j ∈ Finset.Ico 2 (k + 3),
                PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ (j - 1)))) := by
            refine tendsto_finsetSum _ fun j hj => ?_
            have hj2 : 2 ≤ j := (Finset.mem_Ico.mp hj).1
            have hj1 : j - 1 ≠ 0 := by omega
            have hR_inv : Tendsto (fun R : ℝ => (R : ℂ)⁻¹) atTop (𝓝 0) := by
              have h := Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_inv_atTop_zero
              simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using h
            have hR_pow : Tendsto (fun R : ℝ => (R : ℂ)⁻¹ ^ (j - 1)) atTop (𝓝 0) := by
              simpa [zero_pow hj1] using hR_inv.pow (j - 1)
            simpa using tendsto_const_nhds.mul (tendsto_const_nhds.mul (tendsto_const_nhds.sub hR_pow))
          exact ((hlim_a0.sub tendsto_const_nhds).sub hlim_sum).norm
        have h_lim_le : ‖(a0 - f u) - ∑ j ∈ Finset.Ico 2 (k + 3),
              PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ (j - 1))‖ ≤
            (C_t / ((k + 2 : ℕ) : ℝ)) / u ^ (k + 2) :=
          le_of_tendsto hlim_lhs (eventually_atTop.mpr ⟨u, hR_bound⟩)
        have h_reindex : ∑ j ∈ Finset.Ico 2 (k + 3),
              PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ (j - 1)) =
            ∑ m ∈ Finset.Ico 1 (k + 2),
              PowerSeries.coeff (m + 1) T * ((m : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ m) := by
          refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
          · intro j hj; simp only [Finset.mem_Ico] at hj ⊢; omega
          · intro j1 hj1 j2 hj2 heq; simp only [Finset.mem_Ico] at hj1 hj2; omega
          · intro m hm
            refine ⟨m + 1, ?_, by omega⟩
            simp only [Finset.mem_Ico] at hm ⊢; omega
          · intro j hj
            have hj2 : 2 ≤ j := (Finset.mem_Ico.mp hj).1
            rw [show j - 1 + 1 = j by omega]
        have h_fu_exp := (hu_f u huf).trans (div_le_div_of_nonneg_right (le_max_left Cf 0) (by positivity))
        have h_split_S : ∑ m ∈ Finset.range (k + 2), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m =
            a0 + ∑ m ∈ Finset.Ico 1 (k + 2), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m := by
          have hunion : Finset.range (k + 2) = insert 0 (Finset.Ico 1 (k + 2)) := by
            ext m; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
          rw [hunion, Finset.sum_insert (by simp)]
          simp [a0]
        have h_diff_sum : (∑ m ∈ Finset.Ico 1 (k + 2), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m) +
              ∑ m ∈ Finset.Ico 1 (k + 2),
                PowerSeries.coeff (m + 1) T * ((m : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ m) =
            (PowerSeries.coeff (k + 1) S +
              PowerSeries.coeff (k + 2) T / ((k + 1 : ℕ) : ℂ)) * (u : ℂ)⁻¹ ^ (k + 1) := by
          rw [← Finset.sum_add_distrib, Finset.sum_Ico_succ_top (by omega : 1 ≤ k + 1)]
          have hlow : ∑ m ∈ Finset.Ico 1 (k + 1),
              (PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m +
                PowerSeries.coeff (m + 1) T * ((m : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ m)) = 0 := by
            refine Finset.sum_eq_zero fun m hm => ?_
            have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
            have hmlt : m + 1 < k + 2 := by
              have := (Finset.mem_Ico.mp hm).2; omega
            have hih := ih (m + 1) hmlt
            have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hdu_m : PowerSeries.coeff (m + 1) (d_u S) = -((m : ℂ) * PowerSeries.coeff m S) := by
              obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
              simpa using coeff_d_u S (m' + 2)
            rw [hih, hdu_m]
            field_simp [hm_ne]
            ring
          rw [hlow, zero_add]
          push_cast; rw [div_eq_mul_inv]; ring
        let Xsum : ℂ := ∑ m ∈ Finset.Ico 1 (k + 2), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m
        let Ysum : ℂ := ∑ m ∈ Finset.Ico 1 (k + 2),
          PowerSeries.coeff (m + 1) T * ((m : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ m)
        have htri : (PowerSeries.coeff (k + 1) S +
              PowerSeries.coeff (k + 2) T / ((k + 1 : ℕ) : ℂ)) * (u : ℂ)⁻¹ ^ (k + 1) =
            -((f u - ∑ m ∈ Finset.range (k + 2), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m) +
              ((a0 - f u) - ∑ j ∈ Finset.Ico 2 (k + 3),
                PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ (j - 1)))) := by
          rw [h_split_S, h_reindex, ← h_diff_sum]
          change Xsum + Ysum = -((f u - (a0 + Xsum)) + ((a0 - f u) - Ysum))
          ring
        rw [htri, norm_neg]
        exact (norm_add_le _ _).trans (by
          calc ‖f u - ∑ m ∈ Finset.range (k + 2), PowerSeries.coeff m S * (u : ℂ)⁻¹ ^ m‖ +
                ‖(a0 - f u) - ∑ j ∈ Finset.Ico 2 (k + 3),
                  PowerSeries.coeff j T * (((j - 1 : ℕ) : ℂ)⁻¹ * (u : ℂ)⁻¹ ^ (j - 1))‖
              ≤ C_f / u ^ (k + 2) + (C_t / ((k + 2 : ℕ) : ℝ)) / u ^ (k + 2) :=
                add_le_add h_fu_exp h_lim_le
            _ = (C_f + C_t / ((k + 2 : ℕ) : ℝ)) / u ^ (k + 2) := by ring)
      have h_coeff_bd : ∀ u : ℝ, max U 1 ≤ u →
          ‖PowerSeries.coeff (k + 1) S + PowerSeries.coeff (k + 2) T / ((k + 1 : ℕ) : ℂ)‖ ≤
            (C_f + C_t / ((k + 2 : ℕ) : ℝ)) / u := by
        intro u hu
        have hu_pos : 0 < u := by linarith [le_max_right U 1 |>.trans hu]
        have h1 := h_u_bd u ((le_max_left U 1).trans hu)
        rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos,
          _root_.inv_pow] at h1
        have hupow : (0 : ℝ) < u ^ (k + 1) := by positivity
        have hmul := mul_le_mul_of_nonneg_right h1 hupow.le
        rw [mul_assoc, inv_mul_cancel₀ hupow.ne', mul_one] at hmul
        refine hmul.trans_eq ?_
        rw [pow_succ]
        field_simp [hu_pos.ne']
      have hlim_0 : Tendsto (fun u : ℝ => (C_f + C_t / ((k + 2 : ℕ) : ℝ)) / u) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hle0 : ‖PowerSeries.coeff (k + 1) S +
          PowerSeries.coeff (k + 2) T / ((k + 1 : ℕ) : ℂ)‖ ≤ 0 :=
        le_of_tendsto_of_tendsto tendsto_const_nhds hlim_0 (eventually_atTop.mpr ⟨max U 1, h_coeff_bd⟩)
      have hz := add_eq_zero_iff_eq_neg.mp (norm_le_zero_iff.mp hle0)
      have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      have hz2 := congrArg (fun z : ℂ => ((k + 1 : ℕ) : ℂ) * z) hz
      field_simp [hk1] at hz2
      linear_combination hz2

/-- Scaled positive-integer sum `∑_{n ≥ 1} h(n / u)`. -/
@[expose] def sumScale (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ, h ((n + 1 : ℝ) / u)

/-- Euler–Maclaurin `1/u^r` coefficient `(-1)^r * B_{r+1} / (r+1)! * h^{(r)}(0)`. -/
@[expose] def emTerm (h : ℝ → ℂ) (r : ℕ) : ℂ :=
  (-1 : ℂ) ^ r * ((bernoulli (r + 1) : ℂ) / ((r + 1).factorial : ℂ)) * iteratedDeriv r h 0

/-- Formal Euler–Maclaurin power series `∑_{r ≥ 0} emTerm h r * u^{-r}` in `w = 1/u`. -/
@[expose] def emSeries (h : ℝ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (emTerm h)

private lemma summable_sumScale {h : ℝ → ℂ} (hh : ExpDecaySmooth h) {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => h ((n + 1 : ℝ) / u)) := by
  obtain ⟨C, c, hC, hc, hbd⟩ := hh.2 0
  have hlt : Real.exp (-c / u) < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hu)
  have hgeom : Summable (fun n : ℕ => (C * Real.exp (-c / u)) * (Real.exp (-c / u)) ^ n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left (C * Real.exp (-c / u))
  refine hgeom.of_norm_bounded fun n => ?_
  have h0 := hbd ((n + 1 : ℝ) / u) (by positivity)
  simp only [iteratedDeriv_zero] at h0
  refine h0.trans_eq ?_
  have hexp : Real.exp (-c * ((n + 1 : ℝ) / u)) = Real.exp (-c / u) * Real.exp (-c / u) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1; ring
  rw [hexp, mul_assoc]

private def emIntTerm (h : ℝ → ℂ) (u : ℝ) (r n : ℕ) : ℂ :=
  (u : ℂ)⁻¹ ^ r *
    ∫ t in (0 : ℝ)..1, ((bernoulliFun r t / (r.factorial : ℝ) : ℝ) : ℂ) *
      iteratedDeriv r h (((n : ℝ) + t) / u)

private lemma summable_emIntTerm {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (r : ℕ)
    {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => emIntTerm h u r n) := by
  obtain ⟨Cr, cr, hCr, hcr, hbd⟩ := hh.2 r
  let Br : ℝ := ∫ t in (0 : ℝ)..1, |bernoulliFun r t / (r.factorial : ℝ)|
  have hBr_nn : 0 ≤ Br :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => abs_nonneg _
  have hlt : Real.exp (-cr / u) < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hu)
  have hgeom : Summable (fun n : ℕ => (u⁻¹ ^ r * (Cr * Br)) * (Real.exp (-cr / u)) ^ n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left _
  refine hgeom.of_norm_bounded fun n => ?_
  dsimp only [emIntTerm]
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
  have hint_fn : IntervalIntegrable (fun t : ℝ =>
      ((bernoulliFun r t / (r.factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv r h (((n : ℝ) + t) / u)) volume 0 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one fun t _ => ?_
    have hc1 : Continuous fun s : ℝ => ((bernoulliFun r s / (r.factorial : ℝ) : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp ((continuous_bernoulliFun r).div_const _)
    have hc2 : Continuous fun s : ℝ => iteratedDeriv r h (((n : ℝ) + s) / u) :=
      (hh.iteratedDeriv_smooth r).continuous.comp ((continuous_const.add continuous_id).div_const _)
    exact (hc1.mul hc2).continuousAt.continuousWithinAt
  have hint_dom : IntervalIntegrable
      (fun t : ℝ => (Cr * Real.exp (-cr * n / u)) * |bernoulliFun r t / (r.factorial : ℝ)|)
      volume 0 1 :=
    ((continuous_const.mul ((continuous_bernoulliFun r).div_const _).abs).continuousOn).intervalIntegrable_of_Icc
      zero_le_one
  have hmono : ∫ t in (0 : ℝ)..1, ‖((bernoulliFun r t / (r.factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv r h (((n : ℝ) + t) / u)‖ ≤
      ∫ t in (0 : ℝ)..1, (Cr * Real.exp (-cr * n / u)) * |bernoulliFun r t / (r.factorial : ℝ)| := by
    refine intervalIntegral.integral_mono_on zero_le_one hint_fn.norm hint_dom fun t ht => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hx_nn : 0 ≤ ((n : ℝ) + t) / u := div_nonneg (by linarith [ht.1]) hu.le
    have h1 := hbd (((n : ℝ) + t) / u) hx_nn
    have hexp : Real.exp (-cr * (((n : ℝ) + t) / u)) ≤ Real.exp (-cr * n / u) := by
      apply Real.exp_le_exp.mpr
      have hdiv : ((n : ℝ)) / u ≤ ((n : ℝ) + t) / u := div_le_div_of_nonneg_right (by linarith [ht.1]) hu.le
      calc -cr * (((n : ℝ) + t) / u) ≤ -cr * ((n : ℝ) / u) :=
            mul_le_mul_of_nonpos_left hdiv (by linarith : -cr ≤ 0)
        _ = -cr * n / u := by ring
    calc |bernoulliFun r t / (r.factorial : ℝ)| * ‖iteratedDeriv r h (((n : ℝ) + t) / u)‖
        ≤ |bernoulliFun r t / (r.factorial : ℝ)| * (Cr * Real.exp (-cr * (((n : ℝ) + t) / u))) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ ≤ |bernoulliFun r t / (r.factorial : ℝ)| * (Cr * Real.exp (-cr * n / u)) := by
          gcongr
      _ = (Cr * Real.exp (-cr * n / u)) * |bernoulliFun r t / (r.factorial : ℝ)| := by ring
  have hnorm_le : ‖∫ t in (0 : ℝ)..1, ((bernoulliFun r t / (r.factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv r h (((n : ℝ) + t) / u)‖ ≤
      (Cr * Br) * (Real.exp (-cr / u)) ^ n := by
    calc ‖∫ t in (0 : ℝ)..1, _‖
        ≤ ∫ t in (0 : ℝ)..1, ‖_‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ t in (0 : ℝ)..1, (Cr * Real.exp (-cr * n / u)) * |bernoulliFun r t / (r.factorial : ℝ)| := hmono
      _ = (Cr * Real.exp (-cr * n / u)) * Br := intervalIntegral.integral_const_mul _ _
      _ = (Cr * Br) * Real.exp ((n : ℝ) * (-cr / u)) := by
          rw [show -cr * n / u = (n : ℝ) * (-cr / u) by ring]; ring
      _ = (Cr * Br) * (Real.exp (-cr / u)) ^ n := by rw [Real.exp_nat_mul]
  calc u⁻¹ ^ r * ‖∫ t in (0 : ℝ)..1, _‖
      ≤ u⁻¹ ^ r * ((Cr * Br) * (Real.exp (-cr / u)) ^ n) := mul_le_mul_of_nonneg_left hnorm_le (by positivity)
    _ = (u⁻¹ ^ r * (Cr * Br)) * (Real.exp (-cr / u)) ^ n := by ring

private lemma sum_emIntTerm_zero {h : ℝ → ℂ} (hh : ExpDecaySmooth h) {u : ℝ} (hu : 0 < u) (N : ℕ) :
    ∑ n ∈ Finset.range N, emIntTerm h u 0 n = (u : ℂ) * (∫ y in (0 : ℝ)..((N : ℝ) / u), h y) := by
  have heach : ∀ n ∈ Finset.range N,
      emIntTerm h u 0 n = ∫ x in ((n : ℕ) : ℝ)..((n + 1 : ℕ) : ℝ), h (x / u) := fun n _ => by
    dsimp only [emIntTerm]
    simp only [pow_zero, one_mul, bernoulliFun_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      Complex.ofReal_one]
    have hcomp := intervalIntegral.integral_comp_add_left (fun x : ℝ => h (x / u)) (n : ℝ)
      (a := (0 : ℝ)) (b := 1)
    simpa [add_zero, Nat.cast_add, Nat.cast_one] using hcomp
  rw [Finset.sum_congr rfl heach]
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun x : ℝ => h (x / u)) (a := fun k : ℕ => (k : ℝ)) (n := N) fun k _ =>
      ((hh.continuous.comp (continuous_id.div_const u)).continuousOn).intervalIntegrable_of_Icc
        (by push_cast; linarith)
  simp only [Nat.cast_zero] at hadj
  rw [hadj]
  have hdiv := intervalIntegral.integral_comp_div h hu.ne' (a := (0 : ℝ)) (b := (N : ℝ))
  rw [zero_div] at hdiv
  rw [hdiv, Complex.real_smul]

private lemma emIntTerm_ibp_zero {h : ℝ → ℂ} (hh : ExpDecaySmooth h) {u : ℝ} (_hu : 0 < u) (n : ℕ) :
    h (((n + 1 : ℕ) : ℝ) / u) =
      emIntTerm h u 0 n + (1 / 2 : ℂ) * (h (((n + 1 : ℕ) : ℝ) / u) - h ((n : ℝ) / u)) +
        emIntTerm h u 1 n := by
  let F : ℝ → ℂ := fun t => ((bernoulliFun 1 t : ℝ) : ℂ) * h (((n : ℝ) + t) / u)
  let F' : ℝ → ℂ := fun t => h (((n : ℝ) + t) / u) +
    ((bernoulliFun 1 t : ℝ) : ℂ) * ((u : ℂ)⁻¹ * deriv h (((n : ℝ) + t) / u))
  have hderiv : ∀ t ∈ [[(0 : ℝ), 1]], HasDerivAt F (F' t) t := fun t _ => by
    have hb : HasDerivAt (fun s : ℝ => ((bernoulliFun 1 s : ℝ) : ℂ)) (1 : ℂ) t := by
      have h1 := (antideriv_bernoulliFun 0 t).ofReal_comp
      simpa using h1
    have hg : HasDerivAt (fun s : ℝ => h (((n : ℝ) + s) / u))
        ((u : ℂ)⁻¹ * deriv h (((n : ℝ) + t) / u)) t := by
      have harg : HasDerivAt (fun s : ℝ => ((n : ℝ) + s) / u) (1 / u) t := by
        simpa using (((hasDerivAt_id t).const_add (n : ℝ)).div_const u)
      have hh' := (hh.differentiable (((n : ℝ) + t) / u)).hasDerivAt.scomp t harg
      refine hh'.congr_deriv ?_
      rw [Complex.real_smul]
      push_cast; rw [one_div, mul_comm]
    exact (hb.mul hg).congr_deriv (by ring)
  have hi1 : IntervalIntegrable (fun t : ℝ => h (((n : ℝ) + t) / u)) volume 0 1 :=
    ((hh.continuous.comp ((continuous_const.add continuous_id).div_const u)).continuousOn).intervalIntegrable_of_Icc
      zero_le_one
  have hi2 : IntervalIntegrable (fun t : ℝ =>
      ((bernoulliFun 1 t : ℝ) : ℂ) * ((u : ℂ)⁻¹ * deriv h (((n : ℝ) + t) / u))) volume 0 1 := by
    have hc : Continuous fun t : ℝ =>
        ((bernoulliFun 1 t : ℝ) : ℂ) * ((u : ℂ)⁻¹ * deriv h (((n : ℝ) + t) / u)) :=
      (Complex.continuous_ofReal.comp (continuous_bernoulliFun 1)).mul
        (continuous_const.mul (hh.deriv.continuous.comp ((continuous_const.add continuous_id).div_const u)))
    exact hc.continuousOn.intervalIntegrable_of_Icc zero_le_one
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hftc
  have hF1 : F 1 = (1 / 2 : ℂ) * h (((n + 1 : ℕ) : ℝ) / u) := by
    dsimp only [F]; rw [bernoulliFun_one]; push_cast; norm_num
  have hF0 : F 0 = -(1 / 2 : ℂ) * h ((n : ℝ) / u) := by
    dsimp only [F]; rw [bernoulliFun_one]; push_cast; norm_num
  have hI0 : emIntTerm h u 0 n = ∫ t in (0 : ℝ)..1, h (((n : ℝ) + t) / u) := by
    dsimp only [emIntTerm]
    simp
  have hI1 : emIntTerm h u 1 n =
      ∫ t in (0 : ℝ)..1, ((bernoulliFun 1 t : ℝ) : ℂ) * ((u : ℂ)⁻¹ * deriv h (((n : ℝ) + t) / u)) := by
    dsimp only [emIntTerm]
    rw [pow_one, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Nat.factorial_one, Nat.cast_one, div_one, iteratedDeriv_one]
    ring
  rw [hF1, hF0, ← hI0, ← hI1] at hftc
  linear_combination -hftc

private lemma emIntTerm_ibp_succ {h : ℝ → ℂ} (hh : ExpDecaySmooth h) {u : ℝ} (_hu : 0 < u)
    (r n : ℕ) :
    emIntTerm h u (r + 1) n =
      (u : ℂ)⁻¹ ^ (r + 1) * ((bernoulli (r + 2) : ℂ) / ((r + 2).factorial : ℂ)) *
        (iteratedDeriv (r + 1) h (((n + 1 : ℕ) : ℝ) / u) - iteratedDeriv (r + 1) h ((n : ℝ) / u)) -
      emIntTerm h u (r + 2) n := by
  let F : ℝ → ℂ := fun t =>
    ((bernoulliFun (r + 2) t / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
      iteratedDeriv (r + 1) h (((n : ℝ) + t) / u)
  let F' : ℝ → ℂ := fun t =>
    ((bernoulliFun (r + 1) t / ((r + 1).factorial : ℝ) : ℝ) : ℂ) *
      iteratedDeriv (r + 1) h (((n : ℝ) + t) / u) +
    ((bernoulliFun (r + 2) t / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
      ((u : ℂ)⁻¹ * iteratedDeriv (r + 2) h (((n : ℝ) + t) / u))
  have hderiv : ∀ t ∈ [[(0 : ℝ), 1]], HasDerivAt F (F' t) t := fun t _ => by
    have hbR : HasDerivAt (fun s : ℝ => bernoulliFun (r + 2) s / ((r + 2).factorial : ℝ))
        (bernoulliFun (r + 1) t / ((r + 1).factorial : ℝ)) t := by
      have h1 := (hasDerivAt_bernoulliFun (r + 2) t).div_const ((r + 2).factorial : ℝ)
      refine h1.congr_deriv ?_
      rw [show r + 2 - 1 = r + 1 by omega, Nat.factorial_succ (r + 1)]
      push_cast
      have hr2 : ((r : ℝ) + 1 + 1) ≠ 0 := by positivity
      have hfac : ((r + 1).factorial : ℝ) ≠ 0 := by positivity
      field_simp [hr2, hfac]
      ring
    have hb : HasDerivAt (fun s : ℝ => ((bernoulliFun (r + 2) s / ((r + 2).factorial : ℝ) : ℝ) : ℂ))
        ((bernoulliFun (r + 1) t / ((r + 1).factorial : ℝ) : ℝ) : ℂ) t := hbR.ofReal_comp
    have hg : HasDerivAt (fun s : ℝ => iteratedDeriv (r + 1) h (((n : ℝ) + s) / u))
        ((u : ℂ)⁻¹ * iteratedDeriv (r + 2) h (((n : ℝ) + t) / u)) t := by
      have harg : HasDerivAt (fun s : ℝ => ((n : ℝ) + s) / u) (1 / u) t := by
        simpa using (((hasDerivAt_id t).const_add (n : ℝ)).div_const u)
      have hh' := ((hh.iteratedDeriv_smooth (r + 1)).differentiable (((n : ℝ) + t) / u)).hasDerivAt.scomp
        t harg
      refine hh'.congr_deriv ?_
      rw [Complex.real_smul, ← iteratedDeriv_succ]
      push_cast; rw [one_div, mul_comm]
    exact (hb.mul hg).congr_deriv (by ring)
  have hi1 : IntervalIntegrable (fun t : ℝ =>
      ((bernoulliFun (r + 1) t / ((r + 1).factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv (r + 1) h (((n : ℝ) + t) / u)) volume 0 1 := by
    have hc : Continuous fun t : ℝ =>
        ((bernoulliFun (r + 1) t / ((r + 1).factorial : ℝ) : ℝ) : ℂ) *
          iteratedDeriv (r + 1) h (((n : ℝ) + t) / u) :=
      (Complex.continuous_ofReal.comp ((continuous_bernoulliFun (r + 1)).div_const _)).mul
        ((hh.iteratedDeriv_smooth (r + 1)).continuous.comp
          ((continuous_const.add continuous_id).div_const u))
    exact hc.continuousOn.intervalIntegrable_of_Icc zero_le_one
  have hi2 : IntervalIntegrable (fun t : ℝ =>
      ((bernoulliFun (r + 2) t / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
        ((u : ℂ)⁻¹ * iteratedDeriv (r + 2) h (((n : ℝ) + t) / u))) volume 0 1 := by
    have hc : Continuous fun t : ℝ =>
        ((bernoulliFun (r + 2) t / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
          ((u : ℂ)⁻¹ * iteratedDeriv (r + 2) h (((n : ℝ) + t) / u)) :=
      (Complex.continuous_ofReal.comp ((continuous_bernoulliFun (r + 2)).div_const _)).mul
        (continuous_const.mul ((hh.iteratedDeriv_smooth (r + 2)).continuous.comp
          ((continuous_const.add continuous_id).div_const u)))
    exact hc.continuousOn.intervalIntegrable_of_Icc zero_le_one
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hftc
  have hF1 : F 1 = ((bernoulli (r + 2) : ℂ) / ((r + 2).factorial : ℂ)) *
      iteratedDeriv (r + 1) h (((n + 1 : ℕ) : ℝ) / u) := by
    dsimp only [F]
    rw [bernoulliFun_endpoints_eq_of_ne_one (by omega), bernoulliFun_eval_zero]
    push_cast; rfl
  have hF0 : F 0 = ((bernoulli (r + 2) : ℂ) / ((r + 2).factorial : ℂ)) *
      iteratedDeriv (r + 1) h ((n : ℝ) / u) := by
    dsimp only [F]
    rw [bernoulliFun_eval_zero]
    push_cast; simp only [add_zero]
  have hI1 : (u : ℂ)⁻¹ ^ (r + 1) * ∫ t in (0 : ℝ)..1,
      ((bernoulliFun (r + 1) t / ((r + 1).factorial : ℝ) : ℝ) : ℂ) *
        iteratedDeriv (r + 1) h (((n : ℝ) + t) / u) =
      emIntTerm h u (r + 1) n := rfl
  have hI2 : (u : ℂ)⁻¹ ^ (r + 1) * ∫ t in (0 : ℝ)..1,
      ((bernoulliFun (r + 2) t / ((r + 2).factorial : ℝ) : ℝ) : ℂ) *
        ((u : ℂ)⁻¹ * iteratedDeriv (r + 2) h (((n : ℝ) + t) / u)) =
      emIntTerm h u (r + 2) n := by
    dsimp only [emIntTerm]
    rw [pow_succ (u : ℂ)⁻¹ (r + 1), mul_assoc]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => by ring
  rw [hF1, hF0] at hftc
  have hm := congrArg (fun z : ℂ => (u : ℂ)⁻¹ ^ (r + 1) * z) hftc
  rw [mul_add, hI1, hI2] at hm
  linear_combination hm

private lemma euler_maclaurin_finite {h : ℝ → ℂ} (hh : ExpDecaySmooth h) {u : ℝ} (hu : 0 < u)
    (N K : ℕ) :
    ∑ n ∈ Finset.range N, h (((n + 1 : ℕ) : ℝ) / u) =
      (u : ℂ) * (∫ y in (0 : ℝ)..((N : ℝ) / u), h y) +
        (1 / 2 : ℂ) * (h ((N : ℝ) / u) - h 0) +
        (∑ k ∈ Finset.Ico 1 (K + 1),
          (-1 : ℂ) ^ (k - 1) * ((bernoulli (k + 1) : ℂ) / ((k + 1).factorial : ℂ)) *
            (u : ℂ)⁻¹ ^ k * (iteratedDeriv k h ((N : ℝ) / u) - iteratedDeriv k h 0)) +
        (-1 : ℂ) ^ K * ∑ n ∈ Finset.range N, emIntTerm h u (K + 1) n := by
  induction K with
  | zero =>
    simp only [Nat.zero_add, Finset.Ico_self, Finset.sum_empty, add_zero, pow_zero, one_mul]
    have hsum : ∑ n ∈ Finset.range N, h (((n + 1 : ℕ) : ℝ) / u) =
        (∑ n ∈ Finset.range N, emIntTerm h u 0 n) +
        (∑ n ∈ Finset.range N,
          (1 / 2 : ℂ) * (h (((n + 1 : ℕ) : ℝ) / u) - h ((n : ℝ) / u))) +
        (∑ n ∈ Finset.range N, emIntTerm h u 1 n) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun n _ => emIntTerm_ibp_zero hh hu n
    have htele : (∑ n ∈ Finset.range N,
        (1 / 2 : ℂ) * (h (((n + 1 : ℕ) : ℝ) / u) - h ((n : ℝ) / u))) =
        (1 / 2 : ℂ) * (h ((N : ℝ) / u) - h 0) := by
      rw [← Finset.mul_sum]
      have hsub := Finset.sum_range_sub (fun n : ℕ => h ((n : ℝ) / u)) N
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at hsub ⊢
      rw [hsub]
    rw [hsum, sum_emIntTerm_zero hh hu N, htele]
  | succ K ih =>
    have hsplit : ∑ n ∈ Finset.range N, emIntTerm h u (K + 1) n =
        (u : ℂ)⁻¹ ^ (K + 1) * ((bernoulli (K + 2) : ℂ) / ((K + 2).factorial : ℂ)) *
          (iteratedDeriv (K + 1) h ((N : ℝ) / u) - iteratedDeriv (K + 1) h 0) -
        ∑ n ∈ Finset.range N, emIntTerm h u (K + 2) n := by
      have hterm : ∑ n ∈ Finset.range N, emIntTerm h u (K + 1) n =
          ∑ n ∈ Finset.range N,
            ((u : ℂ)⁻¹ ^ (K + 1) * ((bernoulli (K + 2) : ℂ) / ((K + 2).factorial : ℂ)) *
              (iteratedDeriv (K + 1) h (((n + 1 : ℕ) : ℝ) / u) -
                iteratedDeriv (K + 1) h ((n : ℝ) / u)) -
            emIntTerm h u (K + 2) n) :=
        Finset.sum_congr rfl fun n _ => emIntTerm_ibp_succ hh hu K n
      rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
      have hsub := Finset.sum_range_sub (fun n : ℕ => iteratedDeriv (K + 1) h ((n : ℝ) / u)) N
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_div] at hsub ⊢
      rw [hsub]
    have hIco : ∑ k ∈ Finset.Ico 1 (K + 2),
          (-1 : ℂ) ^ (k - 1) * ((bernoulli (k + 1) : ℂ) / ((k + 1).factorial : ℂ)) *
            (u : ℂ)⁻¹ ^ k * (iteratedDeriv k h ((N : ℝ) / u) - iteratedDeriv k h 0) =
        (∑ k ∈ Finset.Ico 1 (K + 1),
          (-1 : ℂ) ^ (k - 1) * ((bernoulli (k + 1) : ℂ) / ((k + 1).factorial : ℂ)) *
            (u : ℂ)⁻¹ ^ k * (iteratedDeriv k h ((N : ℝ) / u) - iteratedDeriv k h 0)) +
        (-1 : ℂ) ^ K * ((bernoulli (K + 2) : ℂ) / ((K + 2).factorial : ℂ)) *
          (u : ℂ)⁻¹ ^ (K + 1) * (iteratedDeriv (K + 1) h ((N : ℝ) / u) - iteratedDeriv (K + 1) h 0) := by
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ K + 1)]
      simp only [Nat.add_one_sub_one, show K + 1 + 1 = K + 2 by omega]
    rw [ih, hsplit, hIco]
    ring

private lemma euler_maclaurin_tsum {h : ℝ → ℂ} (hh : ExpDecaySmooth h) {u : ℝ} (hu : 0 < u)
    (K : ℕ) :
    sumScale h u =
      (u : ℂ) * (∫ y in Ioi (0 : ℝ), h y) +
        ∑ r ∈ Finset.range (K + 1), emTerm h r * (u : ℂ)⁻¹ ^ r +
        (-1 : ℂ) ^ K * ∑' n : ℕ, emIntTerm h u (K + 1) n := by
  let L_rhs : ℂ :=
    (u : ℂ) * (∫ y in Ioi (0 : ℝ), h y) +
      ∑ r ∈ Finset.range (K + 1), emTerm h r * (u : ℂ)⁻¹ ^ r +
      (-1 : ℂ) ^ K * ∑' n : ℕ, emIntTerm h u (K + 1) n
  have hL : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, h (((n + 1 : ℕ) : ℝ) / u))
      atTop (𝓝 (sumScale h u)) := by
    have hsum := (summable_sumScale hh hu).hasSum.tendsto_sum_nat
    refine hsum.congr fun N => ?_
    refine Finset.sum_congr rfl fun n _ => by push_cast; rfl
  have hDiv : Tendsto (fun N : ℕ => (N : ℝ) / u) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const hu
  have hInt : Tendsto (fun N : ℕ => (u : ℂ) * (∫ y in (0 : ℝ)..((N : ℝ) / u), h y))
      atTop (𝓝 ((u : ℂ) * (∫ y in Ioi (0 : ℝ), h y))) := by
    have hi := intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
      (by simpa using integrableOn_of_expDecaySmooth hh 0) hDiv
    exact tendsto_const_nhds.mul hi
  have hTerm0 : Tendsto (fun N : ℕ => (1 / 2 : ℂ) * (h ((N : ℝ) / u) - h 0))
      atTop (𝓝 (emTerm h 0 * (u : ℂ)⁻¹ ^ 0)) := by
    have hl := (tendsto_expDecaySmooth_atTop hh 0).comp hDiv
    simp only [iteratedDeriv_zero] at hl
    have heq : (1 / 2 : ℂ) * ((0 : ℂ) - h 0) = emTerm h 0 * (u : ℂ)⁻¹ ^ 0 := by
      rw [emTerm, pow_zero, pow_zero, one_mul, mul_one, bernoulli_one]
      norm_num
    rw [← heq]
    exact tendsto_const_nhds.mul (hl.sub tendsto_const_nhds)
  have hSumK : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Ico 1 (K + 1),
        (-1 : ℂ) ^ (k - 1) * ((bernoulli (k + 1) : ℂ) / ((k + 1).factorial : ℂ)) *
          (u : ℂ)⁻¹ ^ k * (iteratedDeriv k h ((N : ℝ) / u) - iteratedDeriv k h 0))
      atTop (𝓝 (∑ k ∈ Finset.Ico 1 (K + 1), emTerm h k * (u : ℂ)⁻¹ ^ k)) := by
    refine tendsto_finsetSum _ fun k hk => ?_
    have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
    have hl := (tendsto_expDecaySmooth_atTop hh k).comp hDiv
    have heq : (-1 : ℂ) ^ (k - 1) * ((bernoulli (k + 1) : ℂ) / ((k + 1).factorial : ℂ)) *
          (u : ℂ)⁻¹ ^ k * ((0 : ℂ) - iteratedDeriv k h 0) = emTerm h k * (u : ℂ)⁻¹ ^ k := by
      have hpow : (-1 : ℂ) ^ (k - 1) * (-1 : ℂ) = (-1 : ℂ) ^ k := by
        rw [← pow_succ, Nat.sub_add_cancel hk1]
      rw [zero_sub, emTerm]
      calc (-1 : ℂ) ^ (k - 1) * ((bernoulli (k + 1) : ℂ) / ((k + 1).factorial : ℂ)) *
            (u : ℂ)⁻¹ ^ k * (-iteratedDeriv k h 0)
          = ((-1 : ℂ) ^ (k - 1) * (-1 : ℂ)) *
              ((bernoulli (k + 1) : ℂ) / ((k + 1).factorial : ℂ)) *
              iteratedDeriv k h 0 * (u : ℂ)⁻¹ ^ k := by ring
        _ = _ := by rw [hpow]
    rw [← heq]
    exact tendsto_const_nhds.mul (hl.sub tendsto_const_nhds)
  have hRem : Tendsto (fun N : ℕ => (-1 : ℂ) ^ K * ∑ n ∈ Finset.range N, emIntTerm h u (K + 1) n)
      atTop (𝓝 ((-1 : ℂ) ^ K * ∑' n : ℕ, emIntTerm h u (K + 1) n)) :=
    tendsto_const_nhds.mul (summable_emIntTerm hh (K + 1) hu).hasSum.tendsto_sum_nat
  have hR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, h (((n + 1 : ℕ) : ℝ) / u))
      atTop (𝓝 L_rhs) := by
    have hcongr : (fun N : ℕ => ∑ n ∈ Finset.range N, h (((n + 1 : ℕ) : ℝ) / u)) = fun N : ℕ =>
        (u : ℂ) * (∫ y in (0 : ℝ)..((N : ℝ) / u), h y) +
          ((1 / 2 : ℂ) * (h ((N : ℝ) / u) - h 0) +
          ∑ k ∈ Finset.Ico 1 (K + 1),
            (-1 : ℂ) ^ (k - 1) * ((bernoulli (k + 1) : ℂ) / ((k + 1).factorial : ℂ)) *
              (u : ℂ)⁻¹ ^ k * (iteratedDeriv k h ((N : ℝ) / u) - iteratedDeriv k h 0)) +
          (-1 : ℂ) ^ K * ∑ n ∈ Finset.range N, emIntTerm h u (K + 1) n := by
      funext N; rw [euler_maclaurin_finite hh hu N K]; ring
    have hsplit : (∑ r ∈ Finset.range (K + 1), emTerm h r * (u : ℂ)⁻¹ ^ r) =
        emTerm h 0 * (u : ℂ)⁻¹ ^ 0 +
          ∑ k ∈ Finset.Ico 1 (K + 1), emTerm h k * (u : ℂ)⁻¹ ^ k := by
      have hunion : Finset.range (K + 1) = insert 0 (Finset.Ico 1 (K + 1)) := by
        ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
      rw [hunion, Finset.sum_insert (by simp)]
    rw [hcongr]
    have htot := (hInt.add (hTerm0.add hSumK)).add hRem
    simpa only [L_rhs, hsplit, add_assoc] using htot
  exact tendsto_nhds_unique hL hR

theorem sumScale_hasAsympExp {h : ℝ → ℂ} (hh : ExpDecaySmooth h) :
    HasAsympExp (fun u : ℝ => sumScale h u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), h y))
      (emSeries h) := by
  intro M
  obtain ⟨Cm, cm, hCm, hcm, hbd⟩ := hh.2 (M + 1)
  let Bm : ℝ := ∫ t in (0 : ℝ)..1, |bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ)|
  have hBm_nn : 0 ≤ Bm :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => abs_nonneg _
  let C_rem : ℝ := Cm * Bm * ((1 + cm) / cm)
  refine ⟨C_rem + ‖emTerm h M‖, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  have hu_pos : 0 < u := by linarith
  have hEM := euler_maclaurin_tsum hh hu_pos M
  have hsplit_sum : (∑ r ∈ Finset.range (M + 1), emTerm h r * (u : ℂ)⁻¹ ^ r) =
      (∑ r ∈ Finset.range M, PowerSeries.coeff r (emSeries h) * (u : ℂ)⁻¹ ^ r) +
        emTerm h M * (u : ℂ)⁻¹ ^ M := by
    rw [Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [emSeries]
  have h_id : (sumScale h u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), h y)) -
        ∑ r ∈ Finset.range M, PowerSeries.coeff r (emSeries h) * (u : ℂ)⁻¹ ^ r =
      emTerm h M * (u : ℂ)⁻¹ ^ M + (-1 : ℂ) ^ M * ∑' n : ℕ, emIntTerm h u (M + 1) n := by
    rw [hEM, hsplit_sum]; ring
  have hnorm_m : ‖emTerm h M * (u : ℂ)⁻¹ ^ M‖ = ‖emTerm h M‖ / u ^ M := by
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos,
      _root_.inv_pow, div_eq_mul_inv]
  have h_tsum_bd : ‖∑' n : ℕ, emIntTerm h u (M + 1) n‖ ≤ C_rem / u ^ M := by
    have hlt : Real.exp (-cm / u) < 1 :=
      Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) hu_pos)
    have hgeom : Summable (fun n : ℕ => (u⁻¹ ^ (M + 1) * (Cm * Bm)) * (Real.exp (-cm / u)) ^ n) :=
      (summable_geometric_of_lt_one (Real.exp_pos _).le hlt).mul_left _
    have hterm_bd : ∀ n : ℕ, ‖emIntTerm h u (M + 1) n‖ ≤
        (u⁻¹ ^ (M + 1) * (Cm * Bm)) * (Real.exp (-cm / u)) ^ n := fun n => by
      dsimp only [emIntTerm]
      rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu_pos]
      have hint_fn : IntervalIntegrable (fun t : ℝ =>
          ((bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv (M + 1) h (((n : ℝ) + t) / u)) volume 0 1 := by
        refine ContinuousOn.intervalIntegrable_of_Icc zero_le_one fun t _ => ?_
        have hc1 : Continuous fun s : ℝ =>
            ((bernoulliFun (M + 1) s / ((M + 1).factorial : ℝ) : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp ((continuous_bernoulliFun (M + 1)).div_const _)
        have hc2 : Continuous fun s : ℝ => iteratedDeriv (M + 1) h (((n : ℝ) + s) / u) :=
          (hh.iteratedDeriv_smooth (M + 1)).continuous.comp
            ((continuous_const.add continuous_id).div_const _)
        exact (hc1.mul hc2).continuousAt.continuousWithinAt
      have hint_dom : IntervalIntegrable
          (fun t : ℝ => (Cm * Real.exp (-cm * n / u)) * |bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ)|)
          volume 0 1 :=
        ((continuous_const.mul ((continuous_bernoulliFun (M + 1)).div_const _).abs).continuousOn).intervalIntegrable_of_Icc
          zero_le_one
      have hmono : ∫ t in (0 : ℝ)..1, ‖((bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv (M + 1) h (((n : ℝ) + t) / u)‖ ≤
          ∫ t in (0 : ℝ)..1, (Cm * Real.exp (-cm * n / u)) *
            |bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ)| := by
        refine intervalIntegral.integral_mono_on zero_le_one hint_fn.norm hint_dom fun t ht => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hx_nn : 0 ≤ ((n : ℝ) + t) / u := div_nonneg (by linarith [ht.1]) hu_pos.le
        have h1 := hbd (((n : ℝ) + t) / u) hx_nn
        have hexp : Real.exp (-cm * (((n : ℝ) + t) / u)) ≤ Real.exp (-cm * n / u) := by
          apply Real.exp_le_exp.mpr
          have hdiv : (n : ℝ) / u ≤ ((n : ℝ) + t) / u := div_le_div_of_nonneg_right (by linarith [ht.1]) hu_pos.le
          calc -cm * (((n : ℝ) + t) / u) ≤ -cm * ((n : ℝ) / u) :=
                mul_le_mul_of_nonpos_left hdiv (by linarith : -cm ≤ 0)
            _ = -cm * n / u := by ring
        calc |bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ)| *
              ‖iteratedDeriv (M + 1) h (((n : ℝ) + t) / u)‖
            ≤ |bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ)| *
                (Cm * Real.exp (-cm * (((n : ℝ) + t) / u))) :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ ≤ |bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ)| *
                (Cm * Real.exp (-cm * n / u)) := by gcongr
          _ = (Cm * Real.exp (-cm * n / u)) *
                |bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ)| := by ring
      have hnorm_le : ‖∫ t in (0 : ℝ)..1, ((bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ) : ℝ) : ℂ) *
            iteratedDeriv (M + 1) h (((n : ℝ) + t) / u)‖ ≤
          (Cm * Bm) * (Real.exp (-cm / u)) ^ n := by
        calc ‖∫ t in (0 : ℝ)..1, _‖
            ≤ ∫ t in (0 : ℝ)..1, ‖_‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
          _ ≤ ∫ t in (0 : ℝ)..1, (Cm * Real.exp (-cm * n / u)) *
                |bernoulliFun (M + 1) t / ((M + 1).factorial : ℝ)| := hmono
          _ = (Cm * Real.exp (-cm * n / u)) * Bm := intervalIntegral.integral_const_mul _ _
          _ = (Cm * Bm) * Real.exp ((n : ℝ) * (-cm / u)) := by
              rw [show -cm * n / u = (n : ℝ) * (-cm / u) by ring]; ring
          _ = (Cm * Bm) * (Real.exp (-cm / u)) ^ n := by rw [Real.exp_nat_mul]
      calc u⁻¹ ^ (M + 1) * ‖∫ t in (0 : ℝ)..1, _‖
          ≤ u⁻¹ ^ (M + 1) * ((Cm * Bm) * (Real.exp (-cm / u)) ^ n) :=
            mul_le_mul_of_nonneg_left hnorm_le (by positivity)
        _ = (u⁻¹ ^ (M + 1) * (Cm * Bm)) * (Real.exp (-cm / u)) ^ n := by ring
    have hnorm_sum : ‖∑' n : ℕ, emIntTerm h u (M + 1) n‖ ≤
        (u⁻¹ ^ (M + 1) * (Cm * Bm)) / (1 - Real.exp (-cm / u)) := by
      have h1 := norm_tsum_le_tsum_norm (summable_emIntTerm hh (M + 1) hu_pos).norm
      have h2 := ((summable_emIntTerm hh (M + 1) hu_pos).norm).tsum_le_tsum hterm_bd hgeom
      rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le hlt, div_eq_mul_inv] at h2
      exact h1.trans h2
    have h_inv_geom : (1 - Real.exp (-cm / u))⁻¹ ≤ ((1 + cm) / cm) * u := by
      have h_add_exp : 1 + cm / u ≤ Real.exp (cm / u) := by
        linarith [Real.add_one_le_exp (cm / u)]
      have hexp_le : Real.exp (-cm / u) ≤ (1 + cm / u)⁻¹ := by
        have heq : Real.exp (-cm / u) = (Real.exp (cm / u))⁻¹ := by
          rw [← Real.exp_neg]; congr 1; ring
        rw [heq]
        exact inv_anti₀ (by positivity) h_add_exp
      have h1m_ge : cm / (u + cm) ≤ 1 - Real.exp (-cm / u) := by
        have heq1 : 1 - (1 + cm / u)⁻¹ = cm / (u + cm) := by
          field_simp [hu_pos.ne', (by positivity : u + cm ≠ 0)]
          ring
        linarith
      have h_u_cm : u + cm ≤ (1 + cm) * u := by nlinarith
      have h1m_ge2 : cm / ((1 + cm) * u) ≤ 1 - Real.exp (-cm / u) := by
        have : cm / ((1 + cm) * u) ≤ cm / (u + cm) :=
          div_le_div_of_nonneg_left hcm.le (by positivity) h_u_cm
        exact this.trans h1m_ge
      calc (1 - Real.exp (-cm / u))⁻¹ ≤ (cm / ((1 + cm) * u))⁻¹ :=
            inv_anti₀ (by positivity) h1m_ge2
        _ = ((1 + cm) / cm) * u := by field_simp [hcm.ne', hu_pos.ne']
    calc ‖∑' n : ℕ, emIntTerm h u (M + 1) n‖
        ≤ (u⁻¹ ^ (M + 1) * (Cm * Bm)) * (1 - Real.exp (-cm / u))⁻¹ := by
          simpa [div_eq_mul_inv] using hnorm_sum
      _ ≤ (u⁻¹ ^ (M + 1) * (Cm * Bm)) * (((1 + cm) / cm) * u) := by gcongr
      _ = C_rem / u ^ M := by
          dsimp only [C_rem]
          rw [_root_.inv_pow, pow_succ]
          field_simp [hu_pos.ne']
  rw [h_id]
  calc ‖emTerm h M * (u : ℂ)⁻¹ ^ M + (-1 : ℂ) ^ M * ∑' n : ℕ, emIntTerm h u (M + 1) n‖
      ≤ ‖emTerm h M * (u : ℂ)⁻¹ ^ M‖ + ‖(-1 : ℂ) ^ M * ∑' n : ℕ, emIntTerm h u (M + 1) n‖ :=
        norm_add_le _ _
    _ = ‖emTerm h M‖ / u ^ M + ‖∑' n : ℕ, emIntTerm h u (M + 1) n‖ := by
        rw [hnorm_m, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    _ ≤ ‖emTerm h M‖ / u ^ M + C_rem / u ^ M := add_le_add le_rfl h_tsum_bd
    _ = (C_rem + ‖emTerm h M‖) / u ^ M := by ring

/-- Differential step operator on kernels: `(T_a H)(x) = -a H(x) - x H'(x)`. -/
@[expose] def emStep (a : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(a : ℂ) * h x - (x : ℂ) * deriv h x

/-- Iterated differential kernel `emIter j h`. -/
@[expose] def emIter : ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, h => h
  | j + 1, h => emStep j (emIter j h)

private lemma ExpDecaySmooth.emStep_smooth {h : ℝ → ℂ} (a : ℕ) (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (emStep a h) :=
  (hh.const_mul (-(a : ℂ))).sub (hh.deriv.mul_ofReal)

private lemma ExpDecaySmooth.emIter_smooth {h : ℝ → ℂ} (j : ℕ) (hh : ExpDecaySmooth h) :
    ExpDecaySmooth (emIter j h) := by
  induction j with
  | zero => exact hh
  | succ j ih => exact ih.emStep_smooth j

private lemma sumScale_hasDerivAt {H : ℝ → ℂ} (hH : ExpDecaySmooth H) (j : ℕ)
    {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => (v : ℂ)⁻¹ ^ j * sumScale H v)
      ((u : ℂ)⁻¹ ^ (j + 1) * sumScale (emStep j H) u) u := by
  let t : Set ℝ := Metric.ball u (u / 2)
  have ht_open : IsOpen t := Metric.isOpen_ball
  have ht_conn : IsPreconnected t := (convex_ball u (u / 2)).isPreconnected
  have hu_mem : u ∈ t := Metric.mem_ball_self (by positivity)
  let g : ℕ → ℝ → ℂ := fun n v => (v : ℂ)⁻¹ ^ j * H ((n + 1 : ℝ) / v)
  let g' : ℕ → ℝ → ℂ := fun n v => (v : ℂ)⁻¹ ^ (j + 1) * emStep j H ((n + 1 : ℝ) / v)
  have hK : ExpDecaySmooth (emStep j H) := hH.emStep_smooth j
  obtain ⟨CK, cK, hCK, hcK, hbdK⟩ := hK.2 0
  let qK : ℝ := Real.exp (-cK / (3 * u / 2))
  have hqK_lt : qK < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) (by positivity))
  let w : ℕ → ℝ := fun n => ((u / 2)⁻¹ ^ (j + 1) * CK * qK) * qK ^ n
  have hw_summ : Summable w := (summable_geometric_of_lt_one (Real.exp_pos _).le hqK_lt).mul_left _
  have hg_deriv : ∀ (n : ℕ) (y : ℝ), y ∈ t → HasDerivAt (g n) (g' n y) y := fun n y hy => by
    have hy_dist : |y - u| < u / 2 := by simpa [t, Metric.mem_ball, Real.dist_eq] using hy
    have hy_pos : 0 < y := by linarith [(abs_lt.mp hy_dist).1]
    have h1 : HasDerivAt (fun v : ℝ => (v : ℂ)⁻¹ ^ j) (-(j : ℂ) * (y : ℂ)⁻¹ ^ (j + 1)) y :=
      hasDerivAt_inv_pow_complex hy_pos.ne'
    have h2 : HasDerivAt (fun v : ℝ => H ((n + 1 : ℝ) / v))
        (deriv H ((n + 1 : ℝ) / y) * (-((((n + 1 : ℝ) / y ^ 2 : ℝ) : ℂ)))) y := by
      have harg : HasDerivAt (fun v : ℝ => (n + 1 : ℝ) / v) (-((n + 1 : ℝ) / y ^ 2)) y := by
        have hinv := (hasDerivAt_inv hy_pos.ne').const_mul (n + 1 : ℝ)
        refine hinv.congr_deriv ?_
        ring
      have hH' := (hH.differentiable ((n + 1 : ℝ) / y)).hasDerivAt.scomp y harg
      refine hH'.congr_deriv ?_
      rw [Complex.real_smul]
      push_cast; ring
    have hprod := h1.mul h2
    refine hprod.congr_deriv ?_
    dsimp only [g', emStep]
    have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy_pos.ne'
    rw [pow_succ]
    push_cast
    field_simp [hyc]
    ring
  have hg_bound : ∀ (n : ℕ) (y : ℝ), y ∈ t → ‖g' n y‖ ≤ w n := fun n y hy => by
    have hy_dist : |y - u| < u / 2 := by simpa [t, Metric.mem_ball, Real.dist_eq] using hy
    have hy_lo : u / 2 < y := by linarith [(abs_lt.mp hy_dist).1]
    have hy_hi : y < 3 * u / 2 := by linarith [(abs_lt.mp hy_dist).2]
    have hy_pos : 0 < y := by linarith
    dsimp only [g', w]
    rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy_pos]
    have hinv_le : y⁻¹ ^ (j + 1) ≤ (u / 2)⁻¹ ^ (j + 1) :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) hy_lo.le) _
    have hK_bd := hbdK ((n + 1 : ℝ) / y) (by positivity)
    simp only [iteratedDeriv_zero] at hK_bd
    have hexp_le : Real.exp (-cK * ((n + 1 : ℝ) / y)) ≤ qK * qK ^ n := by
      have hdiv : (n + 1 : ℝ) / (3 * u / 2) ≤ (n + 1 : ℝ) / y :=
        div_le_div_of_nonneg_left (by positivity) hy_pos hy_hi.le
      have hexp1 : Real.exp (-cK * ((n + 1 : ℝ) / y)) ≤ Real.exp (-cK * ((n + 1 : ℝ) / (3 * u / 2))) :=
        Real.exp_le_exp.mpr (by nlinarith)
      refine hexp1.trans_eq ?_
      dsimp only [qK]
      calc Real.exp (-cK * ((n + 1 : ℝ) / (3 * u / 2)))
          = Real.exp (-cK / (3 * u / 2)) * Real.exp ((n : ℝ) * (-cK / (3 * u / 2))) := by
              rw [← Real.exp_add]; congr 1; ring
        _ = _ := by rw [Real.exp_nat_mul]
    calc y⁻¹ ^ (j + 1) * ‖emStep j H ((n + 1 : ℝ) / y)‖
        ≤ (u / 2)⁻¹ ^ (j + 1) * (CK * Real.exp (-cK * ((n + 1 : ℝ) / y))) :=
          mul_le_mul hinv_le hK_bd (norm_nonneg _) (by positivity)
      _ ≤ (u / 2)⁻¹ ^ (j + 1) * (CK * (qK * qK ^ n)) := by gcongr
      _ = ((u / 2)⁻¹ ^ (j + 1) * CK * qK) * qK ^ n := by ring
  have hg0 : Summable (fun n : ℕ => g n u) :=
    (summable_sumScale hH hu).mul_left ((u : ℂ)⁻¹ ^ j)
  have htsum := hasDerivAt_tsum_of_isPreconnected hw_summ ht_open ht_conn hg_deriv hg_bound hu_mem hg0 hu_mem
  have heq_fn : (fun v : ℝ => ∑' n : ℕ, g n v) = fun v : ℝ => (v : ℂ)⁻¹ ^ j * sumScale H v := by
    funext v
    dsimp only [g, sumScale]
    exact tsum_mul_left
  have heq_deriv : ∑' n : ℕ, g' n u = (u : ℂ)⁻¹ ^ (j + 1) * sumScale (emStep j H) u := by
    dsimp only [g', sumScale]
    exact tsum_mul_left
  rw [heq_fn, heq_deriv] at htsum
  exact htsum

private lemma sumScale_iteratedDeriv {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (j : ℕ) :
    ∀ u : ℝ, 0 < u → iteratedDeriv j (sumScale h) u = (u : ℂ)⁻¹ ^ j * sumScale (emIter j h) u := by
  induction j with
  | zero => intro u _; simp [emIter]
  | succ j ih =>
    intro u hu
    have heq : iteratedDeriv j (sumScale h) =ᶠ[𝓝 u]
        fun v : ℝ => (v : ℂ)⁻¹ ^ j * sumScale (emIter j h) v := by
      filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
      exact ih v hv
    rw [iteratedDeriv_succ, heq.deriv_eq]
    exact (sumScale_hasDerivAt (hh.emIter_smooth j) j hu).deriv

private lemma integral_Ioi_emIter_one {h : ℝ → ℂ} (hh : ExpDecaySmooth h) :
    ∫ y in Ioi (0 : ℝ), emIter 1 h y = ∫ y in Ioi (0 : ℝ), h y := by
  have heq : emIter 1 h = fun y : ℝ => -((y : ℂ) * deriv h y) := by
    funext y; simp [emIter, emStep]
  rw [heq, integral_neg]
  have hint_uv' : IntegrableOn (fun y : ℝ => (y : ℂ) * deriv h y) (Ioi (0 : ℝ)) := by
    simpa [iteratedDeriv_zero] using integrableOn_of_expDecaySmooth (hh.deriv.mul_ofReal) 0
  have hint_u'v : IntegrableOn (fun y : ℝ => (1 : ℂ) * h y) (Ioi (0 : ℝ)) := by
    simpa [iteratedDeriv_zero] using integrableOn_of_expDecaySmooth hh 0
  have hzero : Tendsto (fun y : ℝ => (y : ℂ) * h y) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : ContinuousAt (fun y : ℝ => (y : ℂ) * h y) 0 :=
      (Complex.continuous_ofReal.mul hh.continuous).continuousAt
    simpa using hcont.continuousWithinAt.tendsto
  have htop : Tendsto (fun y : ℝ => (y : ℂ) * h y) atTop (𝓝 0) := by
    simpa [iteratedDeriv_zero] using tendsto_expDecaySmooth_atTop hh.mul_ofReal 0
  have hibp := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => (y : ℂ)) (v := h) (u' := fun _ => (1 : ℂ)) (v' := deriv h)
    (fun x _ => (hasDerivAt_id x).ofReal_comp)
    (fun x _ => (hh.differentiable x).hasDerivAt)
    hint_uv' hint_u'v hzero htop
  simpa using congrArg Neg.neg hibp

theorem sumScale_iteratedDeriv_hasAsympExp {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun u : ℝ => sumScale h u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), h y)))
      (d_u^[j] (emSeries h)) := by
  let I0 : ℂ := ∫ y in Ioi (0 : ℝ), h y
  let f0 : ℝ → ℂ := fun u => sumScale h u - (u : ℂ) * I0
  let G : ℕ → ℝ → ℂ := fun k => match k with
    | 0 => fun u => sumScale h u - (u : ℂ) * I0
    | 1 => fun u => (u : ℂ)⁻¹ * sumScale (emIter 1 h) u - I0
    | k + 2 => fun u => (u : ℂ)⁻¹ ^ (k + 2) * sumScale (emIter (k + 2) h) u
  have hG_deriv : ∀ (k : ℕ) (u : ℝ), 0 < u → HasDerivAt (G k) (G (k + 1) u) u := by
    intro k u hu
    match k with
    | 0 =>
      have h1 := sumScale_hasDerivAt hh 0 hu
      have h2 := ((hasDerivAt_id u).ofReal_comp).mul_const I0
      have hsub : HasDerivAt (fun v : ℝ => sumScale h v - (v : ℂ) * I0)
          ((u : ℂ)⁻¹ * sumScale (emStep 0 h) u - I0) u := by
        convert h1.sub h2 using 1
        · funext v; simp
        · simp
      simpa [G, emIter] using hsub
    | 1 =>
      have h1 := sumScale_hasDerivAt (hh.emIter_smooth 1) 1 hu
      simpa [G, emIter] using h1.sub_const I0
    | k + 2 =>
      exact sumScale_hasDerivAt (hh.emIter_smooth (k + 2)) (k + 2) hu
  have hiter_eq : ∀ (k : ℕ) (u : ℝ), 0 < u → iteratedDeriv k f0 u = G k u := by
    intro k
    induction k with
    | zero => intro u _; rfl
    | succ k ih =>
      intro u hu
      have hev : iteratedDeriv k f0 =ᶠ[𝓝 u] G k := by
        filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
        exact ih v hv
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hG_deriv k u hu).deriv
  have hG_asymp : ∀ k : ℕ, ∃ T : PowerSeries ℂ, HasAsympExp (G k) T := by
    intro k
    match k with
    | 0 => exact ⟨emSeries h, sumScale_hasAsympExp hh⟩
    | 1 =>
      have hexp1 := (hasAsympExp_inv_pow 1).mul (sumScale_hasAsympExp (hh.emIter_smooth 1))
      refine ⟨PowerSeries.X ^ 1 * emSeries (emIter 1 h), fun M => ?_⟩
      obtain ⟨C, hC⟩ := hexp1 M
      refine ⟨C, ?_⟩
      filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
      have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
      have heq_u : G 1 u = (u : ℂ)⁻¹ ^ 1 * (sumScale (emIter 1 h) u -
          (u : ℂ) * (∫ y in Ioi (0 : ℝ), emIter 1 h y)) := by
        dsimp only [G, I0]
        rw [integral_Ioi_emIter_one hh, pow_one, mul_sub]
        congr 1
        field_simp [huc]
      simpa only [heq_u] using hu_bd
    | k + 2 =>
      let I_k : ℂ := ∫ y in Ioi (0 : ℝ), emIter (k + 2) h y
      let Tk : PowerSeries ℂ :=
        PowerSeries.X ^ (k + 2) * emSeries (emIter (k + 2) h) +
          PowerSeries.X ^ (k + 1) * PowerSeries.C I_k
      have hexp := ((hasAsympExp_inv_pow (k + 2)).mul
        (sumScale_hasAsympExp (hh.emIter_smooth (k + 2)))).add
        ((hasAsympExp_inv_pow (k + 1)).mul (HasAsympExp.const I_k))
      refine ⟨Tk, fun M => ?_⟩
      obtain ⟨C, hC⟩ := hexp M
      refine ⟨C, ?_⟩
      filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
      have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
      have heq_u : G (k + 2) u =
          (u : ℂ)⁻¹ ^ (k + 2) * (sumScale (emIter (k + 2) h) u - (u : ℂ) * I_k) +
            (u : ℂ)⁻¹ ^ (k + 1) * I_k := by
        dsimp only [G]
        rw [mul_sub, pow_succ]
        field_simp [huc]
        ring
      simpa only [heq_u] using hu_bd
  have hiter_asymp : ∀ k : ℕ, ∃ T : PowerSeries ℂ, HasAsympExp (iteratedDeriv k f0) T := fun k => by
    obtain ⟨T, hT⟩ := hG_asymp k
    refine ⟨T, fun M => ?_⟩
    obtain ⟨C, hC⟩ := hT M
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
    simpa only [hiter_eq k u hu_pos] using hu_bd
  induction j with
  | zero => simpa using sumScale_hasAsympExp hh
  | succ j ih =>
    obtain ⟨T, hT⟩ := hiter_asymp (j + 1)
    have hT_deriv : HasAsympExp (deriv (iteratedDeriv j f0)) T := by
      simpa only [← iteratedDeriv_succ] using hT
    have hsmooth : ∀ᶠ u : ℝ in atTop,
        DifferentiableAt ℝ (iteratedDeriv j f0) u ∧ ContinuousAt (deriv (iteratedDeriv j f0)) u := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu_pos
      have hev_j : iteratedDeriv j f0 =ᶠ[𝓝 u] G j := by
        filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with v hv
        exact hiter_eq j v hv
      have hdiff_j : DifferentiableAt ℝ (iteratedDeriv j f0) u :=
        (hG_deriv j u hu_pos).differentiableAt.congr_of_eventuallyEq hev_j
      have hev_j1 : deriv (iteratedDeriv j f0) =ᶠ[𝓝 u] G (j + 1) := by
        filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with v hv
        rw [← iteratedDeriv_succ, hiter_eq (j + 1) v hv]
      have hcont_j1 : ContinuousAt (deriv (iteratedDeriv j f0)) u :=
        (hG_deriv (j + 1) u hu_pos).continuousAt.congr hev_j1.symm
      exact ⟨hdiff_j, hcont_j1⟩
    have hEq : T = d_u (d_u^[j] (emSeries h)) :=
      HasAsympExp.deriv_of_hasAsympExp ih hT_deriv hsmooth
    rw [Function.iterate_succ_apply', ← hEq, iteratedDeriv_succ]
    exact hT_deriv

/-! ### 5A. Divisor Zeta Bounds, Kernel Integrals & Termwise Differentiation -/

private lemma summable_sigmaNat_div_pow (a b : ℕ) (hb : 2 ≤ b) :
    Summable (fun n : ℕ => (sigmaNat a (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (a + b)) := by
  let w : ℕ → ℕ → ℝ := fun d n => (d : ℝ) ^ a / (n : ℝ) ^ (a + b)
  have hw : ∀ d n : ℕ, 0 ≤ w d n := fun d n => by dsimp [w]; positivity
  have hs_b : Summable (fun d : ℕ => ((d + 1 : ℕ) : ℝ) ^ (-(b : ℝ))) := by
    have hlt : -(b : ℝ) < -1 := by
      have hbR : (2 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      linarith
    exact (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr hlt)
  have hs_ab : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (-((a + b : ℕ) : ℝ))) := by
    have hlt : -((a + b : ℕ) : ℝ) < -1 := by
      have habR : (2 : ℝ) ≤ ((a + b : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ a + b)
      linarith
    exact (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.mpr hlt)
  have hfactor : ∀ d j : ℕ, w (d + 1) ((d + 1) * (j + 1)) =
      ((d + 1 : ℕ) : ℝ) ^ (-(b : ℝ)) * ((j + 1 : ℕ) : ℝ) ^ (-((a + b : ℕ) : ℝ)) := fun d j => by
    dsimp [w]
    have hd : (0 : ℝ) < (d + 1 : ℕ) := by positivity
    have hj : (0 : ℝ) < (j + 1 : ℕ) := by positivity
    rw [Nat.cast_mul, mul_pow, pow_add, Real.rpow_neg hd.le, Real.rpow_neg hj.le,
      Real.rpow_natCast, Real.rpow_natCast]
    field_simp [hd.ne', hj.ne']
  have hrow : ∀ d : ℕ, Summable (fun j : ℕ => w (d + 1) ((d + 1) * (j + 1))) := fun d =>
    (hs_ab.mul_left (((d + 1 : ℕ) : ℝ) ^ (-(b : ℝ)))).congr fun j => (hfactor d j).symm
  have hcol : Summable (fun d : ℕ => ∑' j : ℕ, w (d + 1) ((d + 1) * (j + 1))) := by
    refine (hs_b.mul_right (∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ (-((a + b : ℕ) : ℝ)))).congr fun d => ?_
    simp_rw [hfactor]
    rw [tsum_mul_left]
  let g : ℕ × ℕ → ℝ := fun p => w (p.1 + 1) ((p.1 + 1) * (p.2 + 1))
  have hg_summ : Summable g :=
    (summable_prod_of_nonneg (fun p => hw _ _)).mpr ⟨hrow, hcol⟩
  have hg_sigma : Summable (fun s : Σ n : ℕ, Nat.divisors (n + 1) => g (divisorPairEquiv.symm s)) :=
    (divisorPairEquiv.symm.summable_iff).mpr hg_summ
  refine hg_sigma.sigma.congr fun n => ?_
  rw [tsum_fintype]
  have hterm : (∑ d : Nat.divisors (n + 1), g (divisorPairEquiv.symm ⟨n, d⟩)) =
      ∑ d : Nat.divisors (n + 1), w d.1 (n + 1) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    have hd_pos : 0 < d.1 := Nat.pos_of_mem_divisors d.2
    have hd_dvd : d.1 ∣ n + 1 := Nat.dvd_of_mem_divisors d.2
    have hq_pos : 0 < (n + 1) / d.1 :=
      Nat.div_pos (Nat.le_of_dvd (Nat.succ_pos n) hd_dvd) hd_pos
    change w (d.1 - 1 + 1) ((d.1 - 1 + 1) * ((n + 1) / d.1 - 1 + 1)) = w d.1 (n + 1)
    rw [Nat.sub_add_cancel hd_pos, Nat.sub_add_cancel hq_pos, Nat.mul_div_cancel' hd_dvd]
  rw [hterm, Finset.sum_coe_sort (Nat.divisors (n + 1)) (fun d => w d (n + 1))]
  dsimp [w, sigmaNat]
  rw [← Finset.sum_div]
  simp

private lemma integral_Ioi_gFun : ∫ y in Ioi (0 : ℝ), gFun y = -1 := by
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt qFun (gFun x) x := fun x _ =>
    (qFun_expDecaySmooth.differentiable x).hasDerivAt
  have hint : IntegrableOn gFun (Ioi (0 : ℝ)) := by
    simpa [iteratedDeriv_zero] using integrableOn_of_expDecaySmooth gFun_expDecaySmooth 0
  have htop : Tendsto qFun atTop (𝓝 0) := by
    simpa [iteratedDeriv_zero] using tendsto_expDecaySmooth_atTop qFun_expDecaySmooth 0
  have hI := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hd hint htop
  have hq0 : qFun 0 = 1 := by simp [qFun, qComplex, expAux_zero]
  rw [hq0, zero_sub] at hI
  exact hI

private lemma iteratedDeriv_sub_inv (A : ℂ) (k : ℕ) {z : ℂ} (hz : z ≠ A) :
    iteratedDeriv k (fun ζ : ℂ => (A - ζ)⁻¹) z = (k.factorial : ℂ) / (A - z) ^ (k + 1) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have hne : ∀ᶠ ζ in 𝓝 z, ζ ≠ A := (isOpen_ne (x := A)).mem_nhds hz
    have hev : iteratedDeriv k (fun ζ : ℂ => (A - ζ)⁻¹) =ᶠ[𝓝 z]
        fun ζ : ℂ => (k.factorial : ℂ) / (A - ζ) ^ (k + 1) := by
      filter_upwards [hne] with ζ hζ
      exact ih hζ
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hAz : A - z ≠ 0 := sub_ne_zero.mpr hz.symm
    have h_sub : HasDerivAt (fun ζ : ℂ => A - ζ) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub A
    have h_pow : HasDerivAt (fun ζ : ℂ => (A - ζ) ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * (A - z) ^ k * (-1)) z :=
      h_sub.pow (k + 1)
    have h_div : HasDerivAt (fun ζ : ℂ => (k.factorial : ℂ) / (A - ζ) ^ (k + 1))
        (-((k.factorial : ℂ) * (((k + 1 : ℕ) : ℂ) * (A - z) ^ k * (-1))) /
          ((A - z) ^ (k + 1)) ^ 2) z := by
      have hd := (hasDerivAt_const z (k.factorial : ℂ)).div h_pow (pow_ne_zero _ hAz)
      refine hd.congr_deriv ?_
      simp [zero_mul]
    refine h_div.deriv.trans ?_
    rw [Nat.factorial_succ]
    push_cast
    field_simp [hAz]
    ring

private lemma iteratedDeriv_add_inv (A : ℂ) (k : ℕ) {z : ℂ} (hz : A + z ≠ 0) :
    iteratedDeriv k (fun ζ : ℂ => (A + ζ)⁻¹) z =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) / (A + z) ^ (k + 1) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    have hne : ∀ᶠ ζ in 𝓝 z, A + ζ ≠ 0 :=
      ((continuous_const.add continuous_id).continuousAt.eventually_ne hz)
    have hev : iteratedDeriv k (fun ζ : ℂ => (A + ζ)⁻¹) =ᶠ[𝓝 z]
        fun ζ : ℂ => (-1 : ℂ) ^ k * (k.factorial : ℂ) / (A + ζ) ^ (k + 1) := by
      filter_upwards [hne] with ζ hζ
      exact ih hζ
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have h_add : HasDerivAt (fun ζ : ℂ => A + ζ) 1 z := by
      simpa using (hasDerivAt_id z).const_add A
    have h_pow : HasDerivAt (fun ζ : ℂ => (A + ζ) ^ (k + 1))
        (((k + 1 : ℕ) : ℂ) * (A + z) ^ k * 1) z :=
      h_add.pow (k + 1)
    have h_div : HasDerivAt
        (fun ζ : ℂ => (-1 : ℂ) ^ k * (k.factorial : ℂ) / (A + ζ) ^ (k + 1))
        (-((-1 : ℂ) ^ k * (k.factorial : ℂ) * (((k + 1 : ℕ) : ℂ) * (A + z) ^ k * 1)) /
          ((A + z) ^ (k + 1)) ^ 2) z := by
      have hd := (hasDerivAt_const z ((-1 : ℂ) ^ k * (k.factorial : ℂ))).div h_pow
        (pow_ne_zero _ hz)
      refine hd.congr_deriv ?_
      simp [zero_mul]
    refine h_div.deriv.trans ?_
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp [hz]
    ring

private lemma iteratedDeriv_sub_inv_cube_add (A : ℂ) (k : ℕ) {z : ℂ}
    (hz1 : z ≠ A) (hz2 : A + z ≠ 0) :
    iteratedDeriv k (fun ζ : ℂ => (A - ζ)⁻¹ ^ 3 + (A + ζ)⁻¹ ^ 3) z =
      (1 / 2 : ℂ) * (((k + 2).factorial : ℂ) / (A - z) ^ (k + 3) +
        (-1 : ℂ) ^ k * ((k + 2).factorial : ℂ) / (A + z) ^ (k + 3)) := by
  let U : Set ℂ := {ζ : ℂ | ζ ≠ A ∧ A + ζ ≠ 0}
  have hU_open : IsOpen U :=
    (isOpen_ne (x := A)).inter
      ((continuous_const.add continuous_id).isOpen_preimage _ isOpen_ne)
  have hzU : z ∈ U := ⟨hz1, hz2⟩
  have hid : (fun ζ : ℂ => (A - ζ)⁻¹ ^ 3 + (A + ζ)⁻¹ ^ 3) =ᶠ[𝓝 z]
      fun ζ : ℂ => (1 / 2 : ℂ) * (iteratedDeriv 2 (fun w => (A - w)⁻¹) ζ +
        iteratedDeriv 2 (fun w => (A + w)⁻¹) ζ) := by
    filter_upwards [hU_open.mem_nhds hzU] with ζ ⟨hζ1, hζ2⟩
    rw [iteratedDeriv_sub_inv A 2 hζ1, iteratedDeriv_add_inv A 2 hζ2]
    norm_num
    field_simp [sub_ne_zero.mpr hζ1.symm, hζ2]
  rw [hid.iteratedDeriv_eq]
  have h1_an : AnalyticAt ℂ (fun ζ => iteratedDeriv 2 (fun w => (A - w)⁻¹) ζ) z := by
    have hev : (fun ζ : ℂ => iteratedDeriv 2 (fun w => (A - w)⁻¹) ζ) =ᶠ[𝓝 z]
        fun ζ => (2 : ℂ) / (A - ζ) ^ 3 := by
      filter_upwards [(isOpen_ne (x := A)).mem_nhds hz1] with ζ hζ
      rw [iteratedDeriv_sub_inv A 2 hζ]; norm_num
    exact (AnalyticAt.div analyticAt_const ((analyticAt_const.sub analyticAt_id).pow 3)
      (pow_ne_zero 3 (sub_ne_zero.mpr hz1.symm))).congr hev.symm
  have h2_an : AnalyticAt ℂ (fun ζ => iteratedDeriv 2 (fun w => (A + w)⁻¹) ζ) z := by
    have hev : (fun ζ : ℂ => iteratedDeriv 2 (fun w => (A + w)⁻¹) ζ) =ᶠ[𝓝 z]
        fun ζ => (2 : ℂ) / (A + ζ) ^ 3 := by
      filter_upwards [((continuous_const.add continuous_id).continuousAt.eventually_ne hz2)] with ζ hζ
      have hζ' : A + ζ ≠ 0 := hζ
      rw [iteratedDeriv_add_inv A 2 hζ']; norm_num
    exact (AnalyticAt.div analyticAt_const ((analyticAt_const.add analyticAt_id).pow 3)
      (pow_ne_zero 3 hz2)).congr hev.symm
  rw [iteratedDeriv_const_mul_field (1 / 2 : ℂ)
    (fun ζ => iteratedDeriv 2 (fun w => (A - w)⁻¹) ζ + iteratedDeriv 2 (fun w => (A + w)⁻¹) ζ)]
  rw [iteratedDeriv_fun_add (h1_an.contDiffAt.of_le le_top) (h2_an.contDiffAt.of_le le_top)]
  have hm1 : iteratedDeriv k (fun ζ => iteratedDeriv 2 (fun w => (A - w)⁻¹) ζ) z =
      iteratedDeriv (k + 2) (fun w => (A - w)⁻¹) z := by
    change iteratedDeriv k (iteratedDeriv 2 (fun w => (A - w)⁻¹)) z = _
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, ← Function.iterate_add_apply,
      ← iteratedDeriv_eq_iterate]
  have hm2 : iteratedDeriv k (fun ζ => iteratedDeriv 2 (fun w => (A + w)⁻¹) ζ) z =
      iteratedDeriv (k + 2) (fun w => (A + w)⁻¹) z := by
    change iteratedDeriv k (iteratedDeriv 2 (fun w => (A + w)⁻¹)) z = _
    rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, ← Function.iterate_add_apply,
      ← iteratedDeriv_eq_iterate]
  rw [hm1, hm2, iteratedDeriv_sub_inv A (k + 2) hz1, iteratedDeriv_add_inv A (k + 2) hz2]
  have hsign : (-1 : ℂ) ^ (k + 2) = (-1 : ℂ) ^ k := by rw [pow_add]; norm_num
  rw [hsign]

private lemma iteratedDeriv_sq_sub_inv (A : ℂ) (k : ℕ) {z : ℂ}
    (hA0 : A ≠ 0) (hz1 : z ≠ A) (hz2 : A + z ≠ 0) :
    iteratedDeriv k (fun ζ : ℂ => (A ^ 2 - ζ ^ 2)⁻¹) z =
      (2 * A)⁻¹ * ((k.factorial : ℂ) / (A - z) ^ (k + 1) +
        (-1 : ℂ) ^ k * (k.factorial : ℂ) / (A + z) ^ (k + 1)) := by
  let U : Set ℂ := {ζ : ℂ | ζ ≠ A ∧ A + ζ ≠ 0}
  have hU_open : IsOpen U :=
    (isOpen_ne (x := A)).inter
      ((continuous_const.add continuous_id).isOpen_preimage _ isOpen_ne)
  have hid : (fun ζ : ℂ => (A ^ 2 - ζ ^ 2)⁻¹) =ᶠ[𝓝 z]
      fun ζ : ℂ => (2 * A)⁻¹ * ((A - ζ)⁻¹ + (A + ζ)⁻¹) := by
    filter_upwards [hU_open.mem_nhds ⟨hz1, hz2⟩] with ζ ⟨hζ1, hζ2⟩
    have hζ1' : A - ζ ≠ 0 := sub_ne_zero.mpr hζ1.symm
    have hsq : A ^ 2 - ζ ^ 2 = (A - ζ) * (A + ζ) := by ring
    rw [hsq]
    field_simp [hA0, hζ1', hζ2]
    ring
  rw [hid.iteratedDeriv_eq]
  have h1_an : AnalyticAt ℂ (fun ζ => (A - ζ)⁻¹) z :=
    (analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr hz1.symm)
  have h2_an : AnalyticAt ℂ (fun ζ => (A + ζ)⁻¹) z :=
    (analyticAt_const.add analyticAt_id).inv hz2
  rw [iteratedDeriv_const_mul_field (2 * A)⁻¹ (fun ζ => (A - ζ)⁻¹ + (A + ζ)⁻¹),
    iteratedDeriv_fun_add (h1_an.contDiffAt.of_le le_top) (h2_an.contDiffAt.of_le le_top),
    iteratedDeriv_sub_inv A k hz1, iteratedDeriv_add_inv A k hz2]

private lemma iteratedDeriv_tsum_ball {R : ℝ} (hR : 0 < R) (f : ℕ → ℂ → ℂ)
    (hf_an : ∀ n : ℕ, AnalyticOnNhd ℂ (f n) (Metric.ball 0 R))
    (hf_bd : ∀ k : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ (n : ℕ) (z : ℂ), z ∈ Metric.ball 0 R → ‖iteratedDeriv k (f n) z‖ ≤ u n)
    (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => ∑' n : ℕ, f n z) 0 = ∑' n : ℕ, iteratedDeriv m (f n) 0 := by
  let s : Set ℂ := Metric.ball (0 : ℂ) R
  have hs_open : IsOpen s := Metric.isOpen_ball
  have h0_mem : (0 : ℂ) ∈ s := Metric.mem_ball_self hR
  have h_sum : ∀ z ∈ s, Summable (fun n : ℕ => f n z) := by
    intro z hz
    obtain ⟨u, hu_sum, hu_bd⟩ := hf_bd 0
    refine hu_sum.of_norm_bounded fun n => ?_
    simpa [iteratedDeriv_zero] using hu_bd n z hz
  have h_unif : ∀ (k : ℕ), 1 ≤ k → k ≤ m →
      SummableLocallyUniformlyOn (fun n => iteratedDerivWithin k (f n) s) s := by
    intro k _ _
    obtain ⟨u, hu_sum, hu_bd⟩ := hf_bd k
    refine SummableLocallyUniformlyOn_of_locally_bounded hs_open fun K hK _ => ⟨u, hu_sum, fun n z hzK => ?_⟩
    have hzs : z ∈ s := hK hzK
    rw [iteratedDerivWithin_of_isOpen hs_open hzs]
    exact hu_bd n z hzs
  have h_diff : ∀ (n k : ℕ) (z : ℂ), k ≤ m → z ∈ s →
      DifferentiableAt ℂ (iteratedDerivWithin k (f n) s) z := by
    intro n k z _ hzs
    have hcd : ContDiffOn ℂ (⊤ : ℕ∞) (f n) s := (hf_an n).contDiffOn hs_open.uniqueDiffOn
    have hd_on : DifferentiableOn ℂ (iteratedDerivWithin k (f n) s) s :=
      hcd.differentiableOn_iteratedDerivWithin (WithTop.coe_lt_coe.mpr (WithTop.coe_lt_top k))
        hs_open.uniqueDiffOn
    exact hd_on.differentiableAt (hs_open.mem_nhds hzs)
  have h_res := iteratedDerivWithin_tsum m hs_open h0_mem h_sum h_unif h_diff
  rw [iteratedDerivWithin_of_isOpen hs_open h0_mem] at h_res
  refine h_res.trans (tsum_congr fun n => ?_)
  exact iteratedDerivWithin_of_isOpen hs_open h0_mem

private lemma norm_sub_exp_mul_real_ge (σ : ℝ) (A : ℝ) (v : ℝ) :
    |A * Real.sin σ| ≤ ‖(A : ℂ) - Complex.exp (I * (σ : ℂ)) * (v : ℂ)‖ := by
  let w : ℂ := (A : ℂ) - Complex.exp (I * (σ : ℂ)) * (v : ℂ)
  have hexp_σ : Complex.exp (I * (σ : ℂ)) = Complex.exp ((σ : ℂ) * I) := by congr 1; ring
  have hw_re : w.re = A - Real.cos σ * v := by
    dsimp only [w]
    rw [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, hexp_σ,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hw_im : w.im = -(Real.sin σ * v) := by
    dsimp only [w]
    rw [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, hexp_σ,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, zero_sub]
  have h_nsq : (A * Real.sin σ) ^ 2 ≤ Complex.normSq w := by
    rw [Complex.normSq_apply, hw_re, hw_im]
    have hid := Real.sin_sq_add_cos_sq σ
    have hid' : (A - Real.cos σ * v) * (A - Real.cos σ * v) +
        (-(Real.sin σ * v)) * (-(Real.sin σ * v)) =
        (v - A * Real.cos σ) ^ 2 + (A * Real.sin σ) ^ 2 +
          (v ^ 2 - A ^ 2) * (Real.sin σ ^ 2 + Real.cos σ ^ 2 - 1) := by ring
    rw [hid', hid, sub_self, mul_zero, add_zero]
    linarith [sq_nonneg (v - A * Real.cos σ)]
  change |A * Real.sin σ| ≤ ‖w‖
  rw [Complex.norm_def]
  refine Real.le_sqrt_of_sq_le ?_
  rw [sq_abs]
  exact h_nsq

private lemma norm_add_exp_mul_real_ge (σ : ℝ) (hcos : 0 ≤ Real.cos σ) {A : ℝ} (_hA : 0 ≤ A)
    {v : ℝ} (hv : 0 ≤ v) :
    A ≤ ‖(A : ℂ) + Complex.exp (I * (σ : ℂ)) * (v : ℂ)‖ := by
  have hexp_σ : Complex.exp (I * (σ : ℂ)) = Complex.exp ((σ : ℂ) * I) := by congr 1; ring
  have hre : ((A : ℂ) + Complex.exp (I * (σ : ℂ)) * (v : ℂ)).re = A + Real.cos σ * v := by
    rw [Complex.add_re, Complex.ofReal_re, Complex.mul_re, hexp_σ,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hle : A ≤ ((A : ℂ) + Complex.exp (I * (σ : ℂ)) * (v : ℂ)).re := by
    rw [hre]
    nlinarith
  exact hle.trans (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))

/-! ### 5B. Borel Witnesses & Formal Series Matching (`m = 0` and `m ≥ 1`) -/

/-- Frequency sequence `A_n = 4π²(n + 1)` on `(0, ∞)`. -/
@[expose] def A_freq (n : ℕ) : ℝ := 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)

private lemma A_freq_pos (n : ℕ) : 0 < A_freq n := by
  unfold A_freq; positivity

private lemma A_freq_ge_four_pi_sq (n : ℕ) : 4 * Real.pi ^ 2 ≤ A_freq n := by
  unfold A_freq
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  nlinarith [sq_nonneg Real.pi]

private lemma A_freq_strictMono : StrictMono A_freq := by
  intro a b hab
  unfold A_freq
  have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
  gcongr

private lemma A_freq_ball_lower {n : ℕ} {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) (2 * Real.pi ^ 2)) :
    2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ≤ ‖(A_freq n : ℂ) - z‖ ∧
    2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ≤ ‖(A_freq n : ℂ) + z‖ := by
  have hz_norm : ‖z‖ < 2 * Real.pi ^ 2 := by simpa [Metric.mem_ball] using hz
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have h2pi : 2 * Real.pi ^ 2 ≤ 2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) :=
    le_mul_of_one_le_right (by positivity) h1
  have hsub : 2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ≤ ‖(A_freq n : ℂ) - z‖ := by
    have htri := norm_add_le ((A_freq n : ℂ) - z) z
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (A_freq_pos n)] at htri
    have hA_eq : A_freq n = 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) := rfl
    linarith
  have hadd : 2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) ≤ ‖(A_freq n : ℂ) + z‖ := by
    have htri := norm_add_le ((A_freq n : ℂ) + z) (-z)
    rw [add_neg_cancel_right, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (A_freq_pos n)] at htri
    have hA_eq : A_freq n = 4 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) := rfl
    linarith
  exact ⟨hsub, hadd⟩

private lemma A_freq_tail_diff_norm_ge (w₀ : ℂ) (R : ℝ) :
    ∃ N : ℕ, ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w₀ R →
      A_freq (k + N) / 2 ≤ ‖(A_freq (k + N) : ℂ) - z‖ ∧
      A_freq (k + N) / 2 ≤ ‖(A_freq (k + N) : ℂ) + z‖ := by
  let N : ℕ := Nat.ceil ((‖w₀‖ + R) / (2 * Real.pi ^ 2))
  refine ⟨N, fun k z hz => ?_⟩
  have hN : (‖w₀‖ + R) / (2 * Real.pi ^ 2) ≤ (N : ℝ) := Nat.le_ceil _
  have hpi : 0 < 2 * Real.pi ^ 2 := by positivity
  have hM1 : ‖w₀‖ + R ≤ 2 * Real.pi ^ 2 * (N : ℝ) := ((div_le_iff₀ hpi).mp hN).trans_eq (by ring)
  have hM2 : 2 * (‖w₀‖ + R) ≤ A_freq (k + N) := by
    dsimp only [A_freq]
    have hle : (N : ℝ) ≤ ((k + N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : N ≤ k + N + 1)
    nlinarith [sq_nonneg Real.pi]
  have hz_norm : ‖z‖ ≤ ‖w₀‖ + R := by
    have hball : ‖z - w₀‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    calc ‖z‖ = ‖(z - w₀) + w₀‖ := by ring_nf
      _ ≤ ‖z - w₀‖ + ‖w₀‖ := norm_add_le _ _
      _ ≤ R + ‖w₀‖ := by linarith
      _ = ‖w₀‖ + R := by ring
  have hsub : A_freq (k + N) / 2 ≤ ‖(A_freq (k + N) : ℂ) - z‖ := by
    have htri := norm_add_le ((A_freq (k + N) : ℂ) - z) z
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (A_freq_pos (k + N))] at htri
    linarith
  have hadd : A_freq (k + N) / 2 ≤ ‖(A_freq (k + N) : ℂ) + z‖ := by
    have htri := norm_add_le ((A_freq (k + N) : ℂ) + z) (-z)
    rw [add_neg_cancel_right, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (A_freq_pos (k + N))] at htri
    linarith
  exact ⟨hsub, hadd⟩

private lemma A_freq_add_ne_zero_of_wedge {w : ℂ}
    (hw : w ∈ borelWedge (Real.pi / 4) (2 * Real.pi ^ 2)) (n : ℕ) :
    (A_freq n : ℂ) + w ≠ 0 := by
  intro h0
  rcases hw with hw_ball | ⟨hw_re, _⟩
  · have hlt : ‖w‖ < 2 * Real.pi ^ 2 := by simpa [Metric.mem_ball] using hw_ball
    have heq : w = -(A_freq n : ℂ) := eq_neg_of_add_eq_zero_right h0
    rw [heq, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (A_freq_pos n)] at hlt
    linarith [A_freq_ge_four_pi_sq n, sq_pos_of_pos Real.pi_pos]
  · have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
    linarith [A_freq_pos n]

/-- Triple-pole Borel transform for `f₀(u) = (d/dt)(t L₀(e^{-t}))|_{t=1/u} + u - 1/4`:
`G₀(ξ) = -4 ∑_{n ≥ 1} d(n) (4π² n) ((4π² n - ξ)^{-3} + (4π² n + ξ)^{-3})`. -/
@[expose] def G₀ (ξ : ℂ) : ℂ :=
  -4 * ∑' n : ℕ, (sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
    (((A_freq n : ℂ) - ξ)⁻¹ ^ 3 + ((A_freq n : ℂ) + ξ)⁻¹ ^ 3)

private def G₀_borelData :
    HigherOrderBorelData G₀ 0 A_freq (fun _ => 3)
      (fun m s => if s = 3 then 4 * (sigmaNat 0 (m + 1) : ℂ) * (A_freq m : ℂ) else 0) where
  α₀ := Real.pi / 4
  θ := Real.pi / 6
  ε := 2 * Real.pi ^ 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by positivity
  ω_pos := A_freq_pos 0
  ω_mono := A_freq_strictMono
  ord_pos := fun _ => by omega
  pp_lead_ne_zero := fun m => by
    simp only [↓reduceIte]
    have hsig : ((sigmaNat 0 (m + 1) : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (sigmaNat_pos (Nat.succ_pos m)))
    exact mul_ne_zero (mul_ne_zero (by norm_num) hsig)
      (Complex.ofReal_ne_zero.mpr (A_freq_pos m).ne')
  analyticOn := fun w hw => by
    simp only [rotatedPuncturedWedge, puncturedWedge, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_mul, Set.mem_sdiff] at hw
    obtain ⟨N, hN⟩ := A_freq_tail_diff_norm_ge w 1
    let term : ℕ → ℂ → ℂ := fun n z =>
      (sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
        (((A_freq n : ℂ) - z)⁻¹ ^ 3 + ((A_freq n : ℂ) + z)⁻¹ ^ 3)
    let head : ℂ → ℂ := fun z => ∑ n ∈ Finset.range N, term n z
    let tail : ℂ → ℂ := fun z => ∑' k : ℕ, term (k + N) z
    have hsumm02 := summable_sigmaNat_div_pow 0 2 le_rfl
    let cbd : ℝ := 16 / (4 * Real.pi ^ 2) ^ 2
    have htail_bd : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w 1 →
        ‖term (k + N) z‖ ≤ cbd * ((sigmaNat 0 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 2) := by
      intro k z hz
      obtain ⟨hsub, hadd⟩ := hN k z hz
      have hA_pos : 0 < A_freq (k + N) := A_freq_pos (k + N)
      dsimp only [term]
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hA_pos]
      have hinv1 : ‖((A_freq (k + N) : ℂ) - z)⁻¹ ^ 3‖ ≤ (2 / A_freq (k + N)) ^ 3 := by
        rw [norm_pow, norm_inv]
        have hle : ‖(A_freq (k + N) : ℂ) - z‖⁻¹ ≤ 2 / A_freq (k + N) := by
          rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hA_pos]
          linarith
        exact pow_le_pow_left₀ (by positivity) hle 3
      have hinv2 : ‖((A_freq (k + N) : ℂ) + z)⁻¹ ^ 3‖ ≤ (2 / A_freq (k + N)) ^ 3 := by
        rw [norm_pow, norm_inv]
        have hle : ‖(A_freq (k + N) : ℂ) + z‖⁻¹ ≤ 2 / A_freq (k + N) := by
          rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hA_pos]
          linarith
        exact pow_le_pow_left₀ (by positivity) hle 3
      have hsum_bd : ‖((A_freq (k + N) : ℂ) - z)⁻¹ ^ 3 + ((A_freq (k + N) : ℂ) + z)⁻¹ ^ 3‖ ≤
          16 / A_freq (k + N) ^ 3 := by
        calc ‖_‖ ≤ ‖((A_freq (k + N) : ℂ) - z)⁻¹ ^ 3‖ + ‖((A_freq (k + N) : ℂ) + z)⁻¹ ^ 3‖ :=
              norm_add_le _ _
          _ ≤ (2 / A_freq (k + N)) ^ 3 + (2 / A_freq (k + N)) ^ 3 := add_le_add hinv1 hinv2
          _ = 16 / A_freq (k + N) ^ 3 := by ring
      calc (sigmaNat 0 (k + N + 1) : ℝ) * A_freq (k + N) * ‖_‖
          ≤ (sigmaNat 0 (k + N + 1) : ℝ) * A_freq (k + N) * (16 / A_freq (k + N) ^ 3) := by
            gcongr
        _ = 16 * ((sigmaNat 0 (k + N + 1) : ℝ) / A_freq (k + N) ^ 2) := by
            have hA_ne : A_freq (k + N) ≠ 0 := hA_pos.ne'
            field_simp [hA_ne]
        _ = cbd * ((sigmaNat 0 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 2) := by
            dsimp only [cbd, A_freq]
            rw [mul_pow]
            ring
    have htail_diff : DifferentiableOn ℂ tail (Metric.ball w 1) := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun k : ℕ => cbd * ((sigmaNat 0 (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ 2))
        (((summable_nat_add_iff N).2 hsumm02).mul_left cbd) (fun k => ?_) Metric.isOpen_ball
        htail_bd
      refine DifferentiableOn.const_mul ?_ _
      refine DifferentiableOn.add ?_ ?_
      · refine (DifferentiableOn.inv ((differentiableOn_const _).sub differentiableOn_id)
          fun z hz => ?_).pow 3
        change (A_freq (k + N) : ℂ) - z ≠ 0
        intro h0
        have h1 := (hN k z hz).1
        rw [h0, norm_zero] at h1
        linarith [A_freq_pos (k + N)]
      · refine (DifferentiableOn.inv ((differentiableOn_const _).add differentiableOn_id)
          fun z hz => ?_).pow 3
        change (A_freq (k + N) : ℂ) + z ≠ 0
        intro h0
        have h1 := (hN k z hz).2
        rw [h0, norm_zero] at h1
        linarith [A_freq_pos (k + N)]
    have htail_ana : AnalyticAt ℂ tail w :=
      (htail_diff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self zero_lt_one)
    have hhead_ana : AnalyticAt ℂ head w := by
      refine Finset.analyticAt_fun_sum (Finset.range N) fun n _ => ?_
      refine AnalyticAt.mul analyticAt_const (AnalyticAt.add ?_ ?_)
      · refine ((analyticAt_const.sub analyticAt_id).inv ?_).pow 3
        change (A_freq n : ℂ) - w ≠ 0
        intro h0
        apply hw.2
        exact ⟨n, by simpa using sub_eq_zero.mp h0⟩
      · refine ((analyticAt_const.add analyticAt_id).inv ?_).pow 3
        change (A_freq n : ℂ) + w ≠ 0
        exact A_freq_add_ne_zero_of_wedge hw.1 n
    have heq_ball : ∀ z ∈ Metric.ball w 1, G₀ z = -4 * (head z + tail z) := by
      intro z hz
      have hts : Summable (fun k : ℕ => term (k + N) z) := by
        refine (((summable_nat_add_iff N).2 hsumm02).mul_left cbd).of_norm_bounded fun k => ?_
        exact htail_bd k z hz
      have hsum_all := (summable_nat_add_iff (f := fun n => term n z) N).1 hts
      simpa only [G₀, head, tail, term] using congrArg (-4 * ·) (hsum_all.sum_add_tsum_nat_add N).symm
    have hev : G₀ =ᶠ[𝓝 w] fun z => -4 * (head z + tail z) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
        heq_ball
    exact (AnalyticAt.mul analyticAt_const (hhead_ana.add htail_ana)).congr hev.symm
  pole_principalPart := fun m => by
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
    let w : ℂ := (A_freq m : ℂ)
    let R : ℝ := 2 * Real.pi ^ 2
    have hR : 0 < R := by positivity
    obtain ⟨N₀, hN₀⟩ := A_freq_tail_diff_norm_ge w R
    let N₁ : ℕ := max N₀ (m + 1)
    have hN₁ : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w R →
        A_freq (k + N₁) / 2 ≤ ‖(A_freq (k + N₁) : ℂ) - z‖ ∧
        A_freq (k + N₁) / 2 ≤ ‖(A_freq (k + N₁) : ℂ) + z‖ := by
      intro k z hz
      have hk := hN₀ (k + (N₁ - N₀)) z hz
      have hidx : k + (N₁ - N₀) + N₀ = k + N₁ := by omega
      simpa only [hidx] using hk
    let term : ℕ → ℂ → ℂ := fun n z =>
      (sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
        (((A_freq n : ℂ) - z)⁻¹ ^ 3 + ((A_freq n : ℂ) + z)⁻¹ ^ 3)
    let mid : ℂ → ℂ := fun z => ∑ n ∈ (Finset.range N₁).erase m, term n z
    let tail : ℂ → ℂ := fun z => ∑' k : ℕ, term (k + N₁) z
    let extra : ℂ → ℂ := fun z =>
      (sigmaNat 0 (m + 1) : ℂ) * (A_freq m : ℂ) * ((A_freq m : ℂ) + z)⁻¹ ^ 3
    have hsumm02 := summable_sigmaNat_div_pow 0 2 le_rfl
    let cbd : ℝ := 16 / (4 * Real.pi ^ 2) ^ 2
    have htail_bd : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w R →
        ‖term (k + N₁) z‖ ≤ cbd * ((sigmaNat 0 (k + N₁ + 1) : ℝ) / ((k + N₁ + 1 : ℕ) : ℝ) ^ 2) := by
      intro k z hz
      obtain ⟨hsub, hadd⟩ := hN₁ k z hz
      have hA_pos : 0 < A_freq (k + N₁) := A_freq_pos (k + N₁)
      dsimp only [term]
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hA_pos]
      have hinv1 : ‖((A_freq (k + N₁) : ℂ) - z)⁻¹ ^ 3‖ ≤ (2 / A_freq (k + N₁)) ^ 3 := by
        rw [norm_pow, norm_inv]
        have hle : ‖(A_freq (k + N₁) : ℂ) - z‖⁻¹ ≤ 2 / A_freq (k + N₁) := by
          rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hA_pos]; linarith
        exact pow_le_pow_left₀ (by positivity) hle 3
      have hinv2 : ‖((A_freq (k + N₁) : ℂ) + z)⁻¹ ^ 3‖ ≤ (2 / A_freq (k + N₁)) ^ 3 := by
        rw [norm_pow, norm_inv]
        have hle : ‖(A_freq (k + N₁) : ℂ) + z‖⁻¹ ≤ 2 / A_freq (k + N₁) := by
          rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) hA_pos]; linarith
        exact pow_le_pow_left₀ (by positivity) hle 3
      have hsum_bd : ‖((A_freq (k + N₁) : ℂ) - z)⁻¹ ^ 3 + ((A_freq (k + N₁) : ℂ) + z)⁻¹ ^ 3‖ ≤
          16 / A_freq (k + N₁) ^ 3 := by
        calc ‖_‖ ≤ ‖((A_freq (k + N₁) : ℂ) - z)⁻¹ ^ 3‖ + ‖((A_freq (k + N₁) : ℂ) + z)⁻¹ ^ 3‖ :=
              norm_add_le _ _
          _ ≤ (2 / A_freq (k + N₁)) ^ 3 + (2 / A_freq (k + N₁)) ^ 3 := add_le_add hinv1 hinv2
          _ = 16 / A_freq (k + N₁) ^ 3 := by ring
      calc (sigmaNat 0 (k + N₁ + 1) : ℝ) * A_freq (k + N₁) * ‖_‖
          ≤ (sigmaNat 0 (k + N₁ + 1) : ℝ) * A_freq (k + N₁) * (16 / A_freq (k + N₁) ^ 3) := by
            gcongr
        _ = 16 * ((sigmaNat 0 (k + N₁ + 1) : ℝ) / A_freq (k + N₁) ^ 2) := by
            have hA_ne : A_freq (k + N₁) ≠ 0 := hA_pos.ne'
            field_simp [hA_ne]
        _ = cbd * ((sigmaNat 0 (k + N₁ + 1) : ℝ) / ((k + N₁ + 1 : ℕ) : ℝ) ^ 2) := by
            dsimp only [cbd, A_freq]
            rw [mul_pow]
            ring
    have htail_diff : DifferentiableOn ℂ tail (Metric.ball w R) := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun k : ℕ => cbd * ((sigmaNat 0 (k + N₁ + 1) : ℝ) / ((k + N₁ + 1 : ℕ) : ℝ) ^ 2))
        (((summable_nat_add_iff N₁).2 hsumm02).mul_left cbd) (fun k => ?_) Metric.isOpen_ball
        htail_bd
      refine DifferentiableOn.const_mul (DifferentiableOn.add ?_ ?_) _
      · refine (DifferentiableOn.inv (DifferentiableOn.sub (differentiableOn_const _) differentiableOn_id)
          fun z hz => ?_).pow 3
        change (A_freq (k + N₁) : ℂ) - z ≠ 0
        intro h0; have h1 := (hN₁ k z hz).1; rw [h0, norm_zero] at h1; linarith [A_freq_pos (k + N₁)]
      · refine (DifferentiableOn.inv (DifferentiableOn.add (differentiableOn_const _) differentiableOn_id)
          fun z hz => ?_).pow 3
        change (A_freq (k + N₁) : ℂ) + z ≠ 0
        intro h0; have h1 := (hN₁ k z hz).2; rw [h0, norm_zero] at h1; linarith [A_freq_pos (k + N₁)]
    have htail_cont : ContinuousAt tail w :=
      (htail_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))).continuousAt
    have hmid_ana : AnalyticAt ℂ mid w := by
      refine Finset.analyticAt_fun_sum ((Finset.range N₁).erase m) fun n hn => ?_
      have hnm : n ≠ m := (Finset.mem_erase.mp hn).1
      refine AnalyticAt.mul analyticAt_const (AnalyticAt.add ?_ ?_)
      · refine ((analyticAt_const.sub analyticAt_id).inv ?_).pow 3
        change (A_freq n : ℂ) - w ≠ 0
        intro h0
        have hcast : ((n + 1 : ℕ) : ℂ) = ((m + 1 : ℕ) : ℂ) := by
          dsimp only [w] at h0
          have h1 : A_freq n = A_freq m := by exact_mod_cast (sub_eq_zero.mp h0)
          dsimp only [A_freq] at h1
          have hpi : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          have h2 : ((n + 1 : ℕ) : ℝ) = ((m + 1 : ℕ) : ℝ) := mul_left_cancel₀ hpi h1
          exact_mod_cast h2
        have : n + 1 = m + 1 := by exact_mod_cast hcast
        exact hnm (by omega)
      · refine ((analyticAt_const.add analyticAt_id).inv ?_).pow 3
        change (A_freq n : ℂ) + w ≠ 0
        intro h0
        have hre0 := congrArg Complex.re h0
        simp only [w, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre0
        linarith [A_freq_pos n, A_freq_pos m]
    have hextra_ana : AnalyticAt ℂ extra w := by
      refine AnalyticAt.mul analyticAt_const (((analyticAt_const.add analyticAt_id).inv ?_).pow 3)
      change (A_freq m : ℂ) + w ≠ 0
      intro h0
      have hre := congrArg Complex.re h0
      simp only [w, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
      linarith [A_freq_pos m]
    have hball : Metric.ball w R \ {w} ∈ 𝓝[≠] w := by
      rw [Set.sdiff_eq, Set.inter_comm]
      exact inter_mem_nhdsWithin _ (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
    have heq_within :
        (fun z : ℂ => G₀ z - ∑ s ∈ Finset.Icc 1 3,
          (if s = 3 then 4 * (sigmaNat 0 (m + 1) : ℂ) * (A_freq m : ℂ) else 0) / (z - w) ^ s) =ᶠ[𝓝[≠] w]
          fun z => -4 * (mid z + tail z + extra z) := by
      filter_upwards [hball] with z ⟨hz_ball, hz_ne⟩
      have hts : Summable (fun k : ℕ => term (k + N₁) z) := by
        refine (((summable_nat_add_iff N₁).2 hsumm02).mul_left cbd).of_norm_bounded fun k => ?_
        exact htail_bd k z hz_ball
      have hsum_all := (summable_nat_add_iff (f := fun n => term n z) N₁).1 hts
      have hm_mem : m ∈ Finset.range N₁ := Finset.mem_range.mpr (by omega)
      have hsplit : ∑' n : ℕ, term n z = term m z + mid z + tail z := by
        have h1 := (hsum_all.sum_add_tsum_nat_add N₁).symm
        have her := (Finset.add_sum_erase (Finset.range N₁) (fun n => term n z) hm_mem).symm
        rw [h1, her, add_assoc]
      have hpp_eq :
          (∑ s ∈ Finset.Icc 1 3,
            (if s = 3 then 4 * (sigmaNat 0 (m + 1) : ℂ) * (A_freq m : ℂ) else 0) / (z - w) ^ s) =
            -4 * (sigmaNat 0 (m + 1) : ℂ) * (A_freq m : ℂ) * ((A_freq m : ℂ) - z)⁻¹ ^ 3 := by
        have hIcc : ∑ s ∈ Finset.Icc 1 3,
              (if s = 3 then 4 * (sigmaNat 0 (m + 1) : ℂ) * (A_freq m : ℂ) else 0) / (z - w) ^ s =
            ∑ s ∈ Finset.Icc 1 3,
              if s = 3 then (4 * (sigmaNat 0 (m + 1) : ℂ) * (A_freq m : ℂ)) / (z - w) ^ 3 else 0 := by
          refine Finset.sum_congr rfl fun s _ => ?_
          split_ifs with hs
          · subst hs; rfl
          · simp
        rw [hIcc, Finset.sum_ite_eq']
        simp only [Finset.mem_Icc, Nat.one_le_ofNat, le_refl, and_self, ↓reduceIte]
        have hz_sub : z - w ≠ 0 := sub_ne_zero.mpr hz_ne
        have hw_sub : w - z = -(z - w) := by ring
        change _ = -4 * (sigmaNat 0 (m + 1) : ℂ) * w * (w - z)⁻¹ ^ 3
        rw [hw_sub]
        field_simp [hz_sub]
        ring
      rw [G₀, hsplit, hpp_eq]
      dsimp only [term, extra]
      ring
    refine ⟨-4 * (mid w + tail w + extra w), ?_⟩
    exact (((((hmid_ana.continuousAt.add htail_cont).add hextra_ana.continuousAt).const_mul (-4))).continuousWithinAt.tendsto).congr'
      heq_within.symm
  expType_plus := by
    let hsumm02 := summable_sigmaNat_div_pow 0 2 le_rfl
    let C : ℝ := 4 * (16 / (4 * Real.pi ^ 2) ^ 2) *
      ∑' n : ℕ, (sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2
    refine ⟨C, 0, by positivity, le_rfl, fun v hv => ?_⟩
    let μ : ℂ := Complex.exp (I * ((0 + Real.pi / 6 : ℝ) : ℂ))
    have hμ_norm : ‖μ‖ = 1 := by
      dsimp only [μ]
      rw [show I * ((0 + Real.pi / 6 : ℝ) : ℂ) = ((Real.pi / 6 : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hsub_ge : ∀ n : ℕ, A_freq n / 2 ≤ ‖(A_freq n : ℂ) - μ * (v : ℂ)‖ := fun n => by
      have h1 := norm_sub_exp_mul_real_ge (Real.pi / 6) (A_freq n) v
      have hsin : |A_freq n * Real.sin (Real.pi / 6)| = A_freq n / 2 := by
        have hAp := A_freq_pos n
        rw [Real.sin_pi_div_six, abs_of_pos (by positivity)]
        ring
      have hμ' : μ = Complex.exp (I * ((Real.pi / 6 : ℝ) : ℂ)) := by simp [μ]
      rw [hμ']
      exact hsin.symm.trans_le h1
    have hadd_ge : ∀ n : ℕ, A_freq n / 2 ≤ ‖(A_freq n : ℂ) + μ * (v : ℂ)‖ := fun n => by
      have hcos : 0 ≤ Real.cos (Real.pi / 6) := by rw [Real.cos_pi_div_six]; positivity
      have h1 := norm_add_exp_mul_real_ge (Real.pi / 6) hcos (A_freq_pos n).le hv
      have hμ' : μ = Complex.exp (I * ((Real.pi / 6 : ℝ) : ℂ)) := by simp [μ]
      rw [hμ']
      exact le_trans (by linarith [A_freq_pos n]) h1
    let cbd : ℝ := 16 / (4 * Real.pi ^ 2) ^ 2
    have hterm_bd : ∀ n : ℕ,
        ‖(sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
          (((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3)‖ ≤
        cbd * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := fun n => by
      have hA_pos := A_freq_pos n
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA_pos]
      have hinv1 : ‖((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3‖ ≤ (2 / A_freq n) ^ 3 := by
        rw [norm_pow, norm_inv]
        have hle : ‖(A_freq n : ℂ) - μ * (v : ℂ)‖⁻¹ ≤ 2 / A_freq n := by
          rw [inv_eq_one_div, div_le_div_iff₀ (by linarith [hsub_ge n]) hA_pos]; linarith [hsub_ge n]
        exact pow_le_pow_left₀ (by positivity) hle 3
      have hinv2 : ‖((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3‖ ≤ (2 / A_freq n) ^ 3 := by
        rw [norm_pow, norm_inv]
        have hle : ‖(A_freq n : ℂ) + μ * (v : ℂ)‖⁻¹ ≤ 2 / A_freq n := by
          rw [inv_eq_one_div, div_le_div_iff₀ (by linarith [hadd_ge n]) hA_pos]; linarith [hadd_ge n]
        exact pow_le_pow_left₀ (by positivity) hle 3
      have hsum_bd : ‖((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3‖ ≤
          16 / A_freq n ^ 3 := by
        calc ‖_‖ ≤ ‖((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3‖ + ‖((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3‖ :=
              norm_add_le _ _
          _ ≤ (2 / A_freq n) ^ 3 + (2 / A_freq n) ^ 3 := add_le_add hinv1 hinv2
          _ = 16 / A_freq n ^ 3 := by ring
      calc (sigmaNat 0 (n + 1) : ℝ) * A_freq n *
            ‖((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3‖
          ≤ (sigmaNat 0 (n + 1) : ℝ) * A_freq n * (16 / A_freq n ^ 3) := by gcongr
        _ = 16 * ((sigmaNat 0 (n + 1) : ℝ) / A_freq n ^ 2) := by
            have hA_ne : A_freq n ≠ 0 := hA_pos.ne'
            field_simp [hA_ne]
        _ = cbd * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
            dsimp only [cbd, A_freq]; rw [mul_pow]; ring
    have hdom : Summable (fun n : ℕ => cbd * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2)) :=
      hsumm02.mul_left cbd
    have hsn : Summable (fun n : ℕ => ‖(sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
        (((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3)‖) :=
      hdom.of_norm_bounded fun n => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hterm_bd n
    rw [Minor.pull, norm_mul, hμ_norm, one_mul, G₀, norm_mul, show ‖(-4 : ℂ)‖ = 4 by norm_num,
      zero_mul, Real.exp_zero, mul_one]
    change 4 * ‖∑' n : ℕ, (sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
        (((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3)‖ ≤ C
    calc 4 * ‖∑' n : ℕ, _‖
        ≤ 4 * ∑' n : ℕ, ‖(sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
            (((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3)‖ := by
          gcongr; exact norm_tsum_le_tsum_norm hsn
      _ ≤ 4 * ∑' n : ℕ, cbd * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hsn.tsum_le_tsum hterm_bd hdom) (by norm_num)
      _ = C := by dsimp only [C, cbd]; rw [tsum_mul_left]; ring
  expType_minus := by
    let hsumm02 := summable_sigmaNat_div_pow 0 2 le_rfl
    let C : ℝ := 4 * (16 / (4 * Real.pi ^ 2) ^ 2) *
      ∑' n : ℕ, (sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2
    refine ⟨C, 0, by positivity, le_rfl, fun v hv => ?_⟩
    let μ : ℂ := Complex.exp (I * ((0 - Real.pi / 6 : ℝ) : ℂ))
    have hμ_norm : ‖μ‖ = 1 := by
      dsimp only [μ]
      rw [show I * ((0 - Real.pi / 6 : ℝ) : ℂ) = ((-Real.pi / 6 : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hsub_ge : ∀ n : ℕ, A_freq n / 2 ≤ ‖(A_freq n : ℂ) - μ * (v : ℂ)‖ := fun n => by
      have h1 := norm_sub_exp_mul_real_ge (-Real.pi / 6) (A_freq n) v
      have hsin : |A_freq n * Real.sin (-Real.pi / 6)| = A_freq n / 2 := by
        have hAp := A_freq_pos n
        rw [show (-Real.pi / 6 : ℝ) = -(Real.pi / 6) by ring, Real.sin_neg, mul_neg, abs_neg,
          Real.sin_pi_div_six, abs_of_pos (by positivity)]
        ring
      have hμ' : μ = Complex.exp (I * ((-Real.pi / 6 : ℝ) : ℂ)) := by
        dsimp only [μ]; congr 2; push_cast; ring
      rw [hμ']
      exact hsin.symm.trans_le h1
    have hadd_ge : ∀ n : ℕ, A_freq n / 2 ≤ ‖(A_freq n : ℂ) + μ * (v : ℂ)‖ := fun n => by
      have hcos : 0 ≤ Real.cos (-Real.pi / 6) := by
        rw [show (-Real.pi / 6 : ℝ) = -(Real.pi / 6) by ring, Real.cos_neg, Real.cos_pi_div_six]
        positivity
      have h1 := norm_add_exp_mul_real_ge (-Real.pi / 6) hcos (A_freq_pos n).le hv
      have hμ' : μ = Complex.exp (I * ((-Real.pi / 6 : ℝ) : ℂ)) := by
        dsimp only [μ]; congr 2; push_cast; ring
      rw [hμ']
      exact le_trans (by linarith [A_freq_pos n]) h1
    let cbd : ℝ := 16 / (4 * Real.pi ^ 2) ^ 2
    have hterm_bd : ∀ n : ℕ,
        ‖(sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
          (((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3)‖ ≤
        cbd * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := fun n => by
      have hA_pos := A_freq_pos n
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA_pos]
      have hinv1 : ‖((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3‖ ≤ (2 / A_freq n) ^ 3 := by
        rw [norm_pow, norm_inv]
        have hle : ‖(A_freq n : ℂ) - μ * (v : ℂ)‖⁻¹ ≤ 2 / A_freq n := by
          rw [inv_eq_one_div, div_le_div_iff₀ (by linarith [hsub_ge n]) hA_pos]; linarith [hsub_ge n]
        exact pow_le_pow_left₀ (by positivity) hle 3
      have hinv2 : ‖((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3‖ ≤ (2 / A_freq n) ^ 3 := by
        rw [norm_pow, norm_inv]
        have hle : ‖(A_freq n : ℂ) + μ * (v : ℂ)‖⁻¹ ≤ 2 / A_freq n := by
          rw [inv_eq_one_div, div_le_div_iff₀ (by linarith [hadd_ge n]) hA_pos]; linarith [hadd_ge n]
        exact pow_le_pow_left₀ (by positivity) hle 3
      have hsum_bd : ‖((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3‖ ≤
          16 / A_freq n ^ 3 := by
        calc ‖_‖ ≤ ‖((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3‖ + ‖((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3‖ :=
              norm_add_le _ _
          _ ≤ (2 / A_freq n) ^ 3 + (2 / A_freq n) ^ 3 := add_le_add hinv1 hinv2
          _ = 16 / A_freq n ^ 3 := by ring
      calc (sigmaNat 0 (n + 1) : ℝ) * A_freq n *
            ‖((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3‖
          ≤ (sigmaNat 0 (n + 1) : ℝ) * A_freq n * (16 / A_freq n ^ 3) := by gcongr
        _ = 16 * ((sigmaNat 0 (n + 1) : ℝ) / A_freq n ^ 2) := by
            have hA_ne : A_freq n ≠ 0 := hA_pos.ne'
            field_simp [hA_ne]
        _ = cbd * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
            dsimp only [cbd, A_freq]; rw [mul_pow]; ring
    have hdom : Summable (fun n : ℕ => cbd * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2)) :=
      hsumm02.mul_left cbd
    have hsn : Summable (fun n : ℕ => ‖(sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
        (((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3)‖) :=
      hdom.of_norm_bounded fun n => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hterm_bd n
    rw [Minor.pull, norm_mul, hμ_norm, one_mul, G₀, norm_mul, show ‖(-4 : ℂ)‖ = 4 by norm_num,
      zero_mul, Real.exp_zero, mul_one]
    change 4 * ‖∑' n : ℕ, (sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
        (((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3)‖ ≤ C
    calc 4 * ‖∑' n : ℕ, _‖
        ≤ 4 * ∑' n : ℕ, ‖(sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
            (((A_freq n : ℂ) - μ * (v : ℂ))⁻¹ ^ 3 + ((A_freq n : ℂ) + μ * (v : ℂ))⁻¹ ^ 3)‖ := by
          gcongr; exact norm_tsum_le_tsum_norm hsn
      _ ≤ 4 * ∑' n : ℕ, cbd * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hsn.tsum_le_tsum hterm_bd hdom) (by norm_num)
      _ = C := by dsimp only [C, cbd]; rw [tsum_mul_left]; ring

private lemma formalSeries_G₀ :
    formalSeries G₀ = emSeries gFun - PowerSeries.C (1 / 4 : ℂ) := by
  let term : ℕ → ℂ → ℂ := fun n z =>
    (sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ) *
      (((A_freq n : ℂ) - z)⁻¹ ^ 3 + ((A_freq n : ℂ) + z)⁻¹ ^ 3)
  let R : ℝ := 2 * Real.pi ^ 2
  have hR : 0 < R := by positivity
  have h_an : ∀ n : ℕ, AnalyticOnNhd ℂ (term n) (Metric.ball 0 R) := fun n z hz => by
    obtain ⟨hsub, hadd⟩ := A_freq_ball_lower hz
    have hpos : 0 < 2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) := by positivity
    refine AnalyticAt.mul analyticAt_const (AnalyticAt.add ?_ ?_)
    · refine ((analyticAt_const.sub analyticAt_id).inv ?_).pow 3
      change (A_freq n : ℂ) - z ≠ 0
      intro h0; rw [h0, norm_zero] at hsub; linarith
    · refine ((analyticAt_const.add analyticAt_id).inv ?_).pow 3
      change (A_freq n : ℂ) + z ≠ 0
      intro h0; rw [h0, norm_zero] at hadd; linarith
  have hsumm02 := summable_sigmaNat_div_pow 0 2 le_rfl
  have h_bd : ∀ k : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ (n : ℕ) (z : ℂ), z ∈ Metric.ball 0 R → ‖iteratedDeriv k (term n) z‖ ≤ u n := fun k => by
    let ck : ℝ := 4 * Real.pi ^ 2 * (((k + 2).factorial : ℝ) / (2 * Real.pi ^ 2) ^ (k + 3))
    refine ⟨fun n => ck * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2),
      hsumm02.mul_left ck, fun n z hz => ?_⟩
    obtain ⟨hsub, hadd⟩ := A_freq_ball_lower hz
    have hpos : 0 < 2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) := by positivity
    have hz1 : z ≠ (A_freq n : ℂ) := fun h0 => by
      have : (A_freq n : ℂ) - z = 0 := by rw [h0, sub_self]
      rw [this, norm_zero] at hsub; linarith
    have hz2 : (A_freq n : ℂ) + z ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at hadd; linarith
    dsimp only [term]
    rw [iteratedDeriv_const_mul_field ((sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ))
        (fun ζ => ((A_freq n : ℂ) - ζ)⁻¹ ^ 3 + ((A_freq n : ℂ) + ζ)⁻¹ ^ 3),
      norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (A_freq_pos n), iteratedDeriv_sub_inv_cube_add (A_freq n : ℂ) k hz1 hz2]
    have hinv1 : ‖((k + 2).factorial : ℂ) / ((A_freq n : ℂ) - z) ^ (k + 3)‖ ≤
        ((k + 2).factorial : ℝ) / (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)) ^ (k + 3) := by
      rw [norm_div, Complex.norm_natCast, norm_pow]
      gcongr
    have hinv2 : ‖(-1 : ℂ) ^ k * ((k + 2).factorial : ℂ) / ((A_freq n : ℂ) + z) ^ (k + 3)‖ ≤
        ((k + 2).factorial : ℝ) / (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)) ^ (k + 3) := by
      rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_natCast, norm_pow]
      gcongr
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    have hsum_bd : ‖(1 / 2 : ℂ) * (((k + 2).factorial : ℂ) / ((A_freq n : ℂ) - z) ^ (k + 3) +
        (-1 : ℂ) ^ k * ((k + 2).factorial : ℂ) / ((A_freq n : ℂ) + z) ^ (k + 3))‖ ≤
        ((k + 2).factorial : ℝ) / (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)) ^ (k + 3) := by
      rw [norm_mul, hhalf]
      calc (1 / 2 : ℝ) * ‖_‖
          ≤ (1 / 2 : ℝ) * (‖((k + 2).factorial : ℂ) / ((A_freq n : ℂ) - z) ^ (k + 3)‖ +
              ‖(-1 : ℂ) ^ k * ((k + 2).factorial : ℂ) / ((A_freq n : ℂ) + z) ^ (k + 3)‖) := by
            gcongr; exact norm_add_le _ _
        _ ≤ (1 / 2 : ℝ) * (((k + 2).factorial : ℝ) / (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)) ^ (k + 3) +
              ((k + 2).factorial : ℝ) / (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)) ^ (k + 3)) := by
            gcongr
        _ = _ := by ring
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hpow_le : ((n + 1 : ℕ) : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ (k + 2) :=
      pow_le_pow_right₀ hn1 (by omega)
    calc (sigmaNat 0 (n + 1) : ℝ) * A_freq n * ‖_‖
        ≤ (sigmaNat 0 (n + 1) : ℝ) * A_freq n *
            (((k + 2).factorial : ℝ) / (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)) ^ (k + 3)) :=
          mul_le_mul_of_nonneg_left hsum_bd (mul_nonneg (Nat.cast_nonneg _) (A_freq_pos n).le)
      _ = ck * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (k + 2)) := by
          dsimp only [ck, A_freq]
          rw [mul_pow, pow_succ ((n + 1 : ℕ) : ℝ) (k + 2)]
          have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          have hpi0 : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          field_simp [hn0, hpi0]
      _ ≤ ck * ((sigmaNat 0 (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ 2) := by
          gcongr
  have hG_deriv : ∀ k : ℕ, iteratedDeriv k G₀ 0 =
      -4 * ∑' n : ℕ, iteratedDeriv k (term n) 0 := fun k => by
    have hG_eq : G₀ = fun z : ℂ => -4 * ∑' n : ℕ, term n z := rfl
    rw [hG_eq, iteratedDeriv_const_mul_field (-4 : ℂ) (fun z : ℂ => ∑' n : ℕ, term n z),
      iteratedDeriv_tsum_ball hR term h_an h_bd k]
  ext n
  cases n with
  | zero =>
    simp only [formalSeries, PowerSeries.coeff_mk, map_sub, emSeries, emTerm, pow_zero, one_mul,
      Nat.zero_add, Nat.factorial_one, Nat.cast_one, div_one, iteratedDeriv_gFun_zero,
      bernoulli_one, PowerSeries.coeff_zero_C]
    norm_num
  | succ k =>
    simp only [formalSeries, PowerSeries.coeff_mk, map_sub, emSeries, emTerm,
      iteratedDeriv_gFun_zero, PowerSeries.coeff_C, Nat.succ_ne_zero, ↓reduceIte, sub_zero]
    rw [hG_deriv k]
    have hterm_zero : ∀ n : ℕ, iteratedDeriv k (term n) 0 =
        (1 / 2 : ℂ) * (sigmaNat 0 (n + 1) : ℂ) * ((k + 2).factorial : ℂ) /
          (A_freq n : ℂ) ^ (k + 2) * (1 + (-1 : ℂ) ^ k) := fun n => by
      have hA_ne : (A_freq n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (A_freq_pos n).ne'
      have hz1 : (0 : ℂ) ≠ (A_freq n : ℂ) := hA_ne.symm
      have hz2 : (A_freq n : ℂ) + 0 ≠ 0 := by simpa using hA_ne
      dsimp only [term]
      rw [iteratedDeriv_const_mul_field ((sigmaNat 0 (n + 1) : ℂ) * (A_freq n : ℂ))
          (fun ζ => ((A_freq n : ℂ) - ζ)⁻¹ ^ 3 + ((A_freq n : ℂ) + ζ)⁻¹ ^ 3),
        iteratedDeriv_sub_inv_cube_add (A_freq n : ℂ) k hz1 hz2]
      simp only [sub_zero, add_zero]
      field_simp [hA_ne]
      ring
    simp_rw [hterm_zero]
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hm_eq : m + m = 2 * m := by omega
      rw [hm_eq]
      have hneg1 : (-1 : ℂ) ^ (2 * m) = 1 := by rw [pow_mul]; norm_num
      have hneg1' : (-1 : ℂ) ^ (2 * m + 1) = -1 := by rw [pow_succ, hneg1]; ring
      rw [hneg1, hneg1']
      have htsum_eq : ∑' n : ℕ, (1 / 2 : ℂ) * (sigmaNat 0 (n + 1) : ℂ) *
            ((2 * m + 2).factorial : ℂ) / (A_freq n : ℂ) ^ (2 * m + 2) * (1 + 1) =
          (((2 * m + 2).factorial : ℂ) / (4 * (Real.pi : ℂ) ^ 2) ^ (2 * m + 2)) *
            ∑' n : ℕ, ((sigmaNat 0 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m + 2)) := by
        have hstep : ∀ n : ℕ, (1 / 2 : ℂ) * (sigmaNat 0 (n + 1) : ℂ) *
              ((2 * m + 2).factorial : ℂ) / (A_freq n : ℂ) ^ (2 * m + 2) * (1 + 1) =
            (((2 * m + 2).factorial : ℂ) / (4 * (Real.pi : ℂ) ^ 2) ^ (2 * m + 2)) *
              ((sigmaNat 0 (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m + 2)) := fun n => by
          have hAn : (A_freq n : ℂ) = (4 * (Real.pi : ℂ) ^ 2) * ((n + 1 : ℕ) : ℂ) := by
            dsimp only [A_freq]; push_cast; ring
          have hpi : (4 * (Real.pi : ℂ) ^ 2 : ℂ) ≠ 0 :=
            mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          have hn0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
          rw [hAn, mul_pow]
          field_simp [hpi, hn0]
          ring
        simp_rw [hstep, tsum_mul_left]
      rw [htsum_eq]
      have hzeta := tsum_sigmaNat_div_pow 0 (2 * m + 2) (by omega)
      simp only [zero_add] at hzeta
      rw [hzeta]
      have hz_val := riemannZeta_two_mul_nat (by omega : m + 1 ≠ 0)
      have h2m2_nat : 2 * m + 2 = 2 * (m + 1) := by omega
      have h2m2_c : ((2 * (m + 1) : ℕ) : ℂ) = 2 * ((m + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [h2m2_nat, h2m2_c, hz_val]
      have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hfac_ne : ((2 * (m + 1)).factorial : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hsign_sq : ((-1 : ℂ) ^ (m + 1 + 1)) ^ 2 = 1 := by
        rw [← pow_mul, mul_comm (m + 1 + 1) 2, pow_mul]; norm_num
      have h2pow : ((2 : ℂ) ^ (2 * (m + 1) - 1)) ^ 2 = (4 : ℂ) ^ (2 * (m + 1)) / 4 := by
        have h_exp : (2 * (m + 1) - 1) * 2 = 4 * m + 2 := by omega
        have h_exp2 : 2 * (2 * (m + 1)) = (4 * m + 2) + 2 := by omega
        rw [← pow_mul, h_exp, show (4 : ℂ) = (2 : ℂ) ^ 2 by norm_num, ← pow_mul, h_exp2, pow_add]
        norm_num
        ring
      field_simp [hpi_ne, hfac_ne]
      rw [hsign_sq, h2pow, ← pow_mul (Real.pi : ℂ) (2 * (m + 1)) 2,
        mul_comm (2 * (m + 1)) 2, pow_mul (Real.pi : ℂ) 2 (2 * (m + 1)), mul_pow]
      ring
    · have hneg1 : (-1 : ℂ) ^ (2 * m + 1) = -1 := by
        rw [pow_succ, show (-1 : ℂ) ^ (2 * m) = 1 from by rw [pow_mul]; norm_num]; ring
      rw [hneg1, add_neg_cancel]
      have hodd : bernoulli (2 * m + 1 + 1 + 1) = 0 :=
        bernoulli_eq_zero_of_odd ⟨m + 1, by omega⟩ (by omega)
      simp [hodd]

private lemma d_u_sub (A B : PowerSeries ℂ) : d_u (A - B) = d_u A - d_u B := by
  simp only [d_u, map_sub]
  ring

private lemma d_u_C (c : ℂ) : d_u (PowerSeries.C c) = 0 := by
  simp [d_u]

private lemma d_u_iter_sub_C (j : ℕ) (S : PowerSeries ℂ) (c : ℂ) :
    d_u^[j + 1] (S - PowerSeries.C c) = d_u^[j + 1] S := by
  rw [Function.iterate_succ_apply, Function.iterate_succ_apply, d_u_sub, d_u_C, sub_zero]

private lemma iteratedDeriv_succ_sub_const (j : ℕ) (g : ℝ → ℂ) (c : ℂ) :
    iteratedDeriv (j + 1) (fun u : ℝ => g u - c) = iteratedDeriv (j + 1) g := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ']
  have hderiv : deriv (fun u : ℝ => g u - c) = deriv g := by
    funext u; exact deriv_sub_const c
  rw [hderiv]

/-- Smooth Euler–Maclaurin remainder `f₀(u) = sumScale gFun u + u - 1/4` for `L₀`. -/
@[expose] def f₀ (u : ℝ) : ℂ :=
  sumScale gFun u + (u : ℂ) - 1 / 4

private lemma f₀_hasAsympExp (j : ℕ) :
    HasAsympExp (iteratedDeriv j f₀) (d_u^[j] (formalSeries G₀)) := by
  have heq_f : f₀ = fun u : ℝ =>
      (sumScale gFun u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), gFun y)) - (1 / 4 : ℂ) := by
    funext u
    rw [integral_Ioi_gFun]
    dsimp only [f₀]
    ring
  rw [heq_f, formalSeries_G₀]
  cases j with
  | zero =>
    simp only [iteratedDeriv_zero, Function.iterate_zero, id_eq]
    have h0 : HasAsympExp (fun u : ℝ => sumScale gFun u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), gFun y))
        (emSeries gFun) := by
      simpa only [iteratedDeriv_zero, Function.iterate_zero, id_eq] using
        sumScale_iteratedDeriv_hasAsympExp gFun_expDecaySmooth 0
    have hc : HasAsympExp (fun _ : ℝ => -(1 / 4 : ℂ)) (PowerSeries.C (-(1 / 4 : ℂ))) :=
      HasAsympExp.const _
    simpa only [sub_eq_add_neg, map_neg] using h0.add hc
  | succ j =>
    rw [iteratedDeriv_succ_sub_const, d_u_iter_sub_C]
    exact sumScale_iteratedDeriv_hasAsympExp gFun_expDecaySmooth (j + 1)

private lemma sumScale_pow_contDiffOn (n : ℕ) :
    ∀ {h : ℝ → ℂ} (_hh : ExpDecaySmooth h) (k : ℕ),
      ContDiffOn ℝ n (fun u : ℝ => (u : ℂ)⁻¹ ^ k * sumScale h u) (Ioi (0 : ℝ)) := by
  induction n with
  | zero =>
    intro h hh k
    rw [Nat.cast_zero, contDiffOn_zero]
    intro u hu
    exact ((sumScale_hasDerivAt hh k hu).continuousAt).continuousWithinAt
  | succ n ih =>
    intro h hh k
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun u hu => ((sumScale_hasDerivAt hh k hu).differentiableAt).differentiableWithinAt,
      by simp, ?_⟩
    have hderiv_eq : EqOn (deriv (fun u : ℝ => (u : ℂ)⁻¹ ^ k * sumScale h u))
        (fun u : ℝ => (u : ℂ)⁻¹ ^ (k + 1) * sumScale (emStep k h) u) (Ioi (0 : ℝ)) := fun u hu =>
      (sumScale_hasDerivAt hh k hu).deriv
    exact (ih (hh.emStep_smooth k) (k + 1)).congr hderiv_eq

private lemma sumScale_contDiffOn {h : ℝ → ℂ} (hh : ExpDecaySmooth h) (n : ℕ) :
    ContDiffOn ℝ n (sumScale h) (Ioi (0 : ℝ)) := by
  simpa using sumScale_pow_contDiffOn n hh 0

/-- Auxiliary series `S_{2m}(ξ) = ∑_{n ≥ 1} (σ_{2m}(n) / n^{2m}) / ((4π² n)² - ξ²)` for `m ≥ 1`. -/
@[expose] def S_even (m : ℕ) (ξ : ℂ) : ℂ :=
  ∑' n : ℕ, ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
    ((A_freq n : ℂ) ^ 2 - ξ ^ 2)⁻¹

/-- Meromorphic Borel transform `K_{2m}(ξ)` (`m ≥ 1`) with simple poles at `ω k = 4π²(k + 1)`. -/
@[expose] def K_even (m : ℕ) (ξ : ℂ) : ℂ :=
  (-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m) * ξ ^ (2 * m + 1) * S_even m ξ

private lemma S_even_term_norm_le {m n : ℕ} {z : ℂ} {L1 L2 : ℝ}
    (hL1 : L1 ≤ ‖(A_freq n : ℂ) - z‖) (hL2 : L2 ≤ ‖(A_freq n : ℂ) + z‖)
    (hL1p : 0 < L1) (hL2p : 0 < L2) :
    ‖((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
        ((A_freq n : ℂ) ^ 2 - z ^ 2)⁻¹‖ ≤
      ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m)) * (L1 * L2)⁻¹ := by
  have hsq : (A_freq n : ℂ) ^ 2 - z ^ 2 = ((A_freq n : ℂ) - z) * ((A_freq n : ℂ) + z) := by ring
  rw [norm_mul, norm_div, Complex.norm_natCast, norm_pow, Complex.norm_natCast, norm_inv, hsq,
    norm_mul]
  gcongr

private def K_even_borelData (m : ℕ) (_hm : 1 ≤ m) :
    HigherOrderBorelData (K_even m) 0 A_freq (fun _ => 1)
      (fun k s => if s = 1 then (-1 : ℂ) ^ m * 2 * (4 * (Real.pi : ℂ) ^ 2) ^ m *
        (sigmaNat (2 * m) (k + 1) : ℂ) else 0) where
  α₀ := Real.pi / 4
  θ := Real.pi / 6
  ε := 2 * Real.pi ^ 2
  hθ_pos := by positivity
  hθ_lt := by linarith [Real.pi_pos]
  hα₀_lt := by linarith [Real.pi_pos]
  hε_pos := by positivity
  ω_pos := A_freq_pos 0
  ω_mono := A_freq_strictMono
  ord_pos := fun _ => le_rfl
  pp_lead_ne_zero := fun k => by
    simp only [↓reduceIte]
    have hsig : ((sigmaNat (2 * m) (k + 1) : ℕ) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (sigmaNat_pos (Nat.succ_pos k)))
    have hpi : (4 * (Real.pi : ℂ) ^ 2 : ℂ) ≠ 0 :=
      mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero m (by norm_num)) (by norm_num))
      (pow_ne_zero m hpi)) hsig
  analyticOn := fun w hw => by
    simp only [rotatedPuncturedWedge, puncturedWedge, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_mul, Set.mem_sdiff] at hw
    obtain ⟨N, hN⟩ := A_freq_tail_diff_norm_ge w 1
    let term : ℕ → ℂ → ℂ := fun n z =>
      ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
        ((A_freq n : ℂ) ^ 2 - z ^ 2)⁻¹
    let head : ℂ → ℂ := fun z => ∑ n ∈ Finset.range N, term n z
    let tail : ℂ → ℂ := fun z => ∑' k : ℕ, term (k + N) z
    have hsumm := summable_sigmaNat_div_pow (2 * m) 2 le_rfl
    let cbd : ℝ := 4 / (4 * Real.pi ^ 2) ^ 2
    have htail_bd : ∀ (k : ℕ) (z : ℂ), z ∈ Metric.ball w 1 →
        ‖term (k + N) z‖ ≤
          cbd * ((sigmaNat (2 * m) (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ (2 * m + 2)) := by
      intro k z hz
      obtain ⟨hsub, hadd⟩ := hN k z hz
      have hA_pos : 0 < A_freq (k + N) := A_freq_pos (k + N)
      have h1 := S_even_term_norm_le (m := m) (n := k + N) hsub hadd (by positivity) (by positivity)
      refine h1.trans_eq ?_
      dsimp only [cbd, A_freq]
      have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
      have hn0 : ((k + N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [pow_add ((k + N + 1 : ℕ) : ℝ) (2 * m) 2]
      field_simp [hpi0, hn0]
      ring
    have htail_diff : DifferentiableOn ℂ tail (Metric.ball w 1) := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun k : ℕ => cbd * ((sigmaNat (2 * m) (k + N + 1) : ℝ) / ((k + N + 1 : ℕ) : ℝ) ^ (2 * m + 2)))
        (((summable_nat_add_iff N).2 hsumm).mul_left cbd) (fun k => ?_) Metric.isOpen_ball
        htail_bd
      refine DifferentiableOn.const_mul ?_ _
      refine DifferentiableOn.inv ((differentiableOn_const _).sub (differentiableOn_id.pow 2))
        fun z hz h0 => ?_
      have hsq : (A_freq (k + N) : ℂ) ^ 2 - z ^ 2 =
          ((A_freq (k + N) : ℂ) - z) * ((A_freq (k + N) : ℂ) + z) := by ring
      rw [hsq, mul_eq_zero] at h0
      rcases h0 with h0 | h0
      · have h1 := (hN k z hz).1; rw [h0, norm_zero] at h1; linarith [A_freq_pos (k + N)]
      · have h1 := (hN k z hz).2; rw [h0, norm_zero] at h1; linarith [A_freq_pos (k + N)]
    have htail_ana : AnalyticAt ℂ tail w :=
      (htail_diff.analyticOnNhd Metric.isOpen_ball) w (Metric.mem_ball_self zero_lt_one)
    have hhead_ana : AnalyticAt ℂ head w := by
      refine Finset.analyticAt_fun_sum (Finset.range N) fun n _ => ?_
      refine AnalyticAt.mul analyticAt_const ?_
      refine (analyticAt_const.sub (analyticAt_id.pow 2)).inv ?_
      have hsq : (A_freq n : ℂ) ^ 2 - w ^ 2 =
          ((A_freq n : ℂ) - w) * ((A_freq n : ℂ) + w) := by ring
      change (A_freq n : ℂ) ^ 2 - w ^ 2 ≠ 0
      rw [hsq]
      refine mul_ne_zero ?_ (A_freq_add_ne_zero_of_wedge hw.1 n)
      intro h0
      apply hw.2
      exact ⟨n, by simpa using sub_eq_zero.mp h0⟩
    have heq_ball : ∀ z ∈ Metric.ball w 1,
        K_even m z =
          (-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m) * z ^ (2 * m + 1) *
            (head z + tail z) := by
      intro z hz
      have hts : Summable (fun k : ℕ => term (k + N) z) := by
        refine (((summable_nat_add_iff N).2 hsumm).mul_left cbd).of_norm_bounded fun k => ?_
        exact htail_bd k z hz
      have hsum_all := (summable_nat_add_iff (f := fun n => term n z) N).1 hts
      have hs_eq : S_even m z = head z + tail z := (hsum_all.sum_add_tsum_nat_add N).symm
      rw [K_even, hs_eq]
    have hev : K_even m =ᶠ[𝓝 w] fun z =>
        (-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m) * z ^ (2 * m + 1) *
          (head z + tail z) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self zero_lt_one))
        heq_ball
    have h_ana_prod : AnalyticAt ℂ (fun z =>
        (-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m) * z ^ (2 * m + 1) *
          (head z + tail z)) w :=
      ((analyticAt_const.mul (analyticAt_id.pow (2 * m + 1))).mul (hhead_ana.add htail_ana))
    exact h_ana_prod.congr hev.symm
  pole_principalPart := fun k => by
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul, Finset.Icc_self,
      Finset.sum_singleton, ↓reduceIte, pow_one]
    let w : ℂ := (A_freq k : ℂ)
    let R : ℝ := 2 * Real.pi ^ 2
    have hR : 0 < R := by positivity
    obtain ⟨N₀, hN₀⟩ := A_freq_tail_diff_norm_ge w R
    let N₁ : ℕ := max N₀ (k + 1)
    have hN₁ : ∀ (j : ℕ) (z : ℂ), z ∈ Metric.ball w R →
        A_freq (j + N₁) / 2 ≤ ‖(A_freq (j + N₁) : ℂ) - z‖ ∧
        A_freq (j + N₁) / 2 ≤ ‖(A_freq (j + N₁) : ℂ) + z‖ := by
      intro j z hz
      have hj := hN₀ (j + (N₁ - N₀)) z hz
      have hidx : j + (N₁ - N₀) + N₀ = j + N₁ := by omega
      simpa only [hidx] using hj
    let term : ℕ → ℂ → ℂ := fun n z =>
      ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
        ((A_freq n : ℂ) ^ 2 - z ^ 2)⁻¹
    let mid : ℂ → ℂ := fun z => ∑ n ∈ (Finset.range N₁).erase k, term n z
    let tail : ℂ → ℂ := fun z => ∑' j : ℕ, term (j + N₁) z
    have hsumm := summable_sigmaNat_div_pow (2 * m) 2 le_rfl
    let cbd : ℝ := 4 / (4 * Real.pi ^ 2) ^ 2
    have htail_bd : ∀ (j : ℕ) (z : ℂ), z ∈ Metric.ball w R →
        ‖term (j + N₁) z‖ ≤
          cbd * ((sigmaNat (2 * m) (j + N₁ + 1) : ℝ) / ((j + N₁ + 1 : ℕ) : ℝ) ^ (2 * m + 2)) := by
      intro j z hz
      obtain ⟨hsub, hadd⟩ := hN₁ j z hz
      have hAp : 0 < A_freq (j + N₁) := A_freq_pos (j + N₁)
      have h1 := S_even_term_norm_le (m := m) (n := j + N₁) hsub hadd (by positivity) (by positivity)
      refine h1.trans_eq ?_
      dsimp only [cbd, A_freq]
      have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
      have hn0 : ((j + N₁ + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [pow_add ((j + N₁ + 1 : ℕ) : ℝ) (2 * m) 2]
      field_simp [hpi0, hn0]
      ring
    have htail_diff : DifferentiableOn ℂ tail (Metric.ball w R) := by
      refine Complex.differentiableOn_tsum_of_summable_norm
        (u := fun j : ℕ => cbd * ((sigmaNat (2 * m) (j + N₁ + 1) : ℝ) / ((j + N₁ + 1 : ℕ) : ℝ) ^ (2 * m + 2)))
        (((summable_nat_add_iff N₁).2 hsumm).mul_left cbd) (fun j => ?_) Metric.isOpen_ball
        htail_bd
      refine DifferentiableOn.const_mul ?_ _
      refine DifferentiableOn.inv ((differentiableOn_const _).sub (differentiableOn_id.pow 2))
        fun z hz h0 => ?_
      have hsq : (A_freq (j + N₁) : ℂ) ^ 2 - z ^ 2 =
          ((A_freq (j + N₁) : ℂ) - z) * ((A_freq (j + N₁) : ℂ) + z) := by ring
      rw [hsq, mul_eq_zero] at h0
      rcases h0 with h0 | h0
      · have h1 := (hN₁ j z hz).1; rw [h0, norm_zero] at h1; linarith [A_freq_pos (j + N₁)]
      · have h1 := (hN₁ j z hz).2; rw [h0, norm_zero] at h1; linarith [A_freq_pos (j + N₁)]
    have htail_cont : ContinuousAt tail w :=
      (htail_diff.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))).continuousAt
    have hmid_ana : AnalyticAt ℂ mid w := by
      refine Finset.analyticAt_fun_sum ((Finset.range N₁).erase k) fun n hn => ?_
      have hnk : n ≠ k := (Finset.mem_erase.mp hn).1
      refine AnalyticAt.mul analyticAt_const ?_
      refine (analyticAt_const.sub (analyticAt_id.pow 2)).inv ?_
      have hsq : (A_freq n : ℂ) ^ 2 - w ^ 2 =
          ((A_freq n : ℂ) - w) * ((A_freq n : ℂ) + w) := by ring
      change (A_freq n : ℂ) ^ 2 - w ^ 2 ≠ 0
      rw [hsq]
      refine mul_ne_zero ?_ ?_
      · intro h0
        have hcast : ((n + 1 : ℕ) : ℂ) = ((k + 1 : ℕ) : ℂ) := by
          dsimp only [w] at h0
          have h1 : A_freq n = A_freq k := by exact_mod_cast (sub_eq_zero.mp h0)
          dsimp only [A_freq] at h1
          have hpi : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          exact_mod_cast (mul_left_cancel₀ hpi h1)
        have : n + 1 = k + 1 := by exact_mod_cast hcast
        exact hnk (by omega)
      · intro h0
        have hre := congrArg Complex.re h0
        simp only [w, Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hre
        linarith [A_freq_pos n, A_freq_pos k]
    let Cm : ℂ := (-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m)
    let Rk : ℂ := (-1 : ℂ) ^ m * 2 * (4 * (Real.pi : ℂ) ^ 2) ^ m * (sigmaNat (2 * m) (k + 1) : ℂ)
    let Pk : ℂ → ℂ := fun z =>
      -(Cm * ((sigmaNat (2 * m) (k + 1) : ℂ) / ((k + 1 : ℕ) : ℂ) ^ (2 * m)) *
        z ^ (2 * m + 1) / (w + z))
    have hPk_an : AnalyticAt ℂ Pk w := by
      refine (AnalyticAt.div (analyticAt_const.mul (analyticAt_id.pow (2 * m + 1)))
        (analyticAt_const.add analyticAt_id) ?_).neg
      intro h0
      have hre := congrArg Complex.re h0
      simp only [w, Complex.zero_re] at hre
      have hre' : A_freq k + A_freq k = 0 := hre
      linarith [A_freq_pos k]
    have hPk_val : Pk w = Rk := by
      dsimp only [Pk, Rk, Cm, w, A_freq]
      have hpi : (4 * (Real.pi : ℂ) ^ 2 : ℂ) ≠ 0 :=
        mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)
      have hweq : ((4 * Real.pi ^ 2 * ((k + 1 : ℕ) : ℝ) : ℝ) : ℂ) =
          (4 * (Real.pi : ℂ) ^ 2) * ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      have h2w : (4 * (Real.pi : ℂ) ^ 2 * ((k + 1 : ℕ) : ℂ)) +
          4 * (Real.pi : ℂ) ^ 2 * ((k + 1 : ℕ) : ℂ) ≠ 0 := by
        rw [← two_mul]
        exact mul_ne_zero (by norm_num) (mul_ne_zero hpi hk1)
      have hpow_split : (4 * (Real.pi : ℂ) ^ 2 * ((k + 1 : ℕ) : ℂ)) ^ (2 * m + 1) =
          (4 * (Real.pi : ℂ) ^ 2) ^ (2 * m + 1) * ((k + 1 : ℕ) : ℂ) ^ (2 * m) *
            ((k + 1 : ℕ) : ℂ) := by
        rw [mul_pow, pow_succ ((k + 1 : ℕ) : ℂ) (2 * m)]
        ring
      have hpi_split : (4 * (Real.pi : ℂ) ^ 2) ^ (2 * m + 1) =
          (4 * (Real.pi : ℂ) ^ 2) ^ m * (4 * (Real.pi : ℂ) ^ 2) ^ m *
            (4 * (Real.pi : ℂ) ^ 2) := by
        rw [show 2 * m + 1 = m + m + 1 by omega, pow_add, pow_add, pow_one]
      rw [hweq, hpow_split, hpi_split, pow_succ (-1 : ℂ) m]
      field_simp [hpi, hk1, h2w]
      ring
    have hslope : Tendsto (fun z : ℂ => (Pk z - Rk) / (z - w)) (𝓝[≠] w) (𝓝 (deriv Pk w)) := by
      have ht := (hasDerivAt_iff_tendsto_slope).mp hPk_an.differentiableAt.hasDerivAt
      refine ht.congr' (eventually_nhdsWithin_of_forall fun z _ => ?_)
      rw [slope_def_field, hPk_val]
    have hball : Metric.ball w R \ {w} ∈ 𝓝[≠] w := by
      rw [Set.sdiff_eq, Set.inter_comm]
      exact inter_mem_nhdsWithin _ (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
    have heq_within :
        (fun z : ℂ => K_even m z - Rk / (z - w)) =ᶠ[𝓝[≠] w]
          fun z => Cm * z ^ (2 * m + 1) * (mid z + tail z) + (Pk z - Rk) / (z - w) := by
      filter_upwards [hball] with z ⟨hz_ball, hz_ne⟩
      have hts : Summable (fun j : ℕ => term (j + N₁) z) := by
        refine (((summable_nat_add_iff N₁).2 hsumm).mul_left cbd).of_norm_bounded fun j => ?_
        exact htail_bd j z hz_ball
      have hsum_all := (summable_nat_add_iff (f := fun n => term n z) N₁).1 hts
      have hk_mem : k ∈ Finset.range N₁ := Finset.mem_range.mpr (by omega)
      have hsplit : S_even m z = term k z + mid z + tail z := by
        have h1 := (hsum_all.sum_add_tsum_nat_add N₁).symm
        have her := (Finset.add_sum_erase (Finset.range N₁) (fun n => term n z) hk_mem).symm
        rw [S_even]
        exact h1.trans (by rw [her, add_assoc])
      have hterm_k : Cm * z ^ (2 * m + 1) * term k z = Pk z / (z - w) := by
        have hzw : z - w ≠ 0 := sub_ne_zero.mpr hz_ne
        have haddz : w + z ≠ 0 := by
          intro h0
          have hball_lt : ‖z - w‖ < R := by simpa [Metric.mem_ball, dist_eq_norm] using hz_ball
          have hw_norm : ‖w‖ = A_freq k := by
            dsimp only [w]; rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (A_freq_pos k)]
          have hz_eq_neg_w : z = -w := eq_neg_of_add_eq_zero_right h0
          rw [hz_eq_neg_w] at hball_lt
          have h2w_lt : ‖-2 * w‖ < R := by convert hball_lt using 1; congr 1; ring
          rw [norm_mul, show ‖(-2 : ℂ)‖ = 2 by norm_num, hw_norm] at h2w_lt
          dsimp only [R] at h2w_lt
          linarith [A_freq_ge_four_pi_sq k]
        have hsq : (A_freq k : ℂ) ^ 2 - z ^ 2 = -(z - w) * (w + z) := by dsimp only [w]; ring
        dsimp only [term, Pk]
        rw [hsq]
        field_simp [hzw, haddz]
      change Cm * z ^ (2 * m + 1) * S_even m z - Rk / (z - w) = _
      rw [hsplit, mul_add, mul_add, hterm_k]
      ring
    have hfront : Tendsto (fun z : ℂ => Cm * z ^ (2 * m + 1) * (mid z + tail z)) (𝓝[≠] w)
        (𝓝 (Cm * w ^ (2 * m + 1) * (mid w + tail w))) := by
      have hc : ContinuousAt (fun z : ℂ => Cm * z ^ (2 * m + 1) * (mid z + tail z)) w :=
        (continuousAt_const.mul (continuousAt_id.pow (2 * m + 1))).mul
          (hmid_ana.continuousAt.add htail_cont)
      exact hc.continuousWithinAt.tendsto
    refine ⟨Cm * w ^ (2 * m + 1) * (mid w + tail w) + deriv Pk w, ?_⟩
    exact (hfront.add hslope).congr' heq_within.symm
  expType_plus := by
    let hsumm := summable_sigmaNat_div_pow (2 * m) 2 le_rfl
    let C_sum : ℝ := (4 / (4 * Real.pi ^ 2) ^ 2) *
      ∑' n : ℕ, (sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2)
    let C : ℝ := ‖(-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m)‖ *
      ((2 * m + 1).factorial : ℝ) * C_sum
    refine ⟨C, 1, by positivity, zero_le_one, fun v hv => ?_⟩
    let μ : ℂ := Complex.exp (I * ((0 + Real.pi / 6 : ℝ) : ℂ))
    have hμ_norm : ‖μ‖ = 1 := by
      dsimp only [μ]
      rw [show I * ((0 + Real.pi / 6 : ℝ) : ℂ) = ((Real.pi / 6 : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hsub_ge : ∀ n : ℕ, A_freq n / 2 ≤ ‖(A_freq n : ℂ) - μ * (v : ℂ)‖ := fun n => by
      have h1 := norm_sub_exp_mul_real_ge (Real.pi / 6) (A_freq n) v
      have hsin : |A_freq n * Real.sin (Real.pi / 6)| = A_freq n / 2 := by
        have hAp := A_freq_pos n
        rw [Real.sin_pi_div_six, abs_of_pos (by positivity)]
        ring
      have hμ' : μ = Complex.exp (I * ((Real.pi / 6 : ℝ) : ℂ)) := by simp [μ]
      rw [hμ']
      exact hsin.symm.trans_le h1
    have hadd_ge : ∀ n : ℕ, A_freq n / 2 ≤ ‖(A_freq n : ℂ) + μ * (v : ℂ)‖ := fun n => by
      have hcos : 0 ≤ Real.cos (Real.pi / 6) := by rw [Real.cos_pi_div_six]; positivity
      have h1 := norm_add_exp_mul_real_ge (Real.pi / 6) hcos (A_freq_pos n).le hv
      have hμ' : μ = Complex.exp (I * ((Real.pi / 6 : ℝ) : ℂ)) := by simp [μ]
      rw [hμ']
      exact le_trans (by linarith [A_freq_pos n]) h1
    let cbd : ℝ := 4 / (4 * Real.pi ^ 2) ^ 2
    have hterm_bd : ∀ n : ℕ,
        ‖((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
            ((A_freq n : ℂ) ^ 2 - (μ * (v : ℂ)) ^ 2)⁻¹‖ ≤
          cbd * ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2)) := fun n => by
      have hAp := A_freq_pos n
      have h1 := S_even_term_norm_le (m := m) (n := n) (hsub_ge n) (hadd_ge n)
        (by positivity) (by positivity)
      refine h1.trans_eq ?_
      dsimp only [cbd, A_freq]
      have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
      have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [pow_add ((n + 1 : ℕ) : ℝ) (2 * m) 2]
      field_simp [hpi0, hn0]
      ring
    have hdom : Summable (fun n : ℕ => cbd * ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2))) :=
      hsumm.mul_left cbd
    have hsn : Summable (fun n : ℕ => ‖((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
        ((A_freq n : ℂ) ^ 2 - (μ * (v : ℂ)) ^ 2)⁻¹‖) :=
      hdom.of_norm_bounded fun n => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hterm_bd n
    have hS_bd : ‖S_even m (μ * (v : ℂ))‖ ≤ C_sum := by
      dsimp only [S_even, C_sum]
      calc ‖∑' n : ℕ, _‖ ≤ ∑' n : ℕ, ‖_‖ := norm_tsum_le_tsum_norm hsn
        _ ≤ ∑' n : ℕ, cbd * ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2)) :=
            hsn.tsum_le_tsum hterm_bd hdom
        _ = cbd * ∑' n : ℕ, (sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2) :=
            tsum_mul_left
    have hv_pow : v ^ (2 * m + 1) ≤ ((2 * m + 1).factorial : ℝ) * Real.exp v := by
      have h1 := Real.pow_div_factorial_le_exp v hv (2 * m + 1)
      have hfac : (0 : ℝ) < ((2 * m + 1).factorial : ℝ) := by positivity
      exact (div_le_iff₀ hfac).mp h1 |>.trans_eq (by ring)
    change ‖μ * K_even m (μ * (v : ℂ))‖ ≤ C * Real.exp (1 * v)
    rw [norm_mul, hμ_norm, one_mul, K_even, norm_mul, norm_mul, norm_mul, norm_pow (-1 : ℂ),
      norm_pow (μ * (v : ℂ)), norm_mul, hμ_norm, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hv, ← norm_pow (-1 : ℂ)]
    calc ‖(-1 : ℂ) ^ (m + 1)‖ * ‖4 / (4 * (Real.pi : ℂ) ^ 2) ^ m‖ * v ^ (2 * m + 1) *
            ‖S_even m (μ * (v : ℂ))‖
        = ‖(-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m)‖ * v ^ (2 * m + 1) *
            ‖S_even m (μ * (v : ℂ))‖ := by rw [← norm_mul]
      _ ≤ ‖(-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m)‖ *
            (((2 * m + 1).factorial : ℝ) * Real.exp v) * C_sum := by gcongr
      _ = C * Real.exp (1 * v) := by dsimp only [C]; rw [one_mul]; ring
  expType_minus := by
    let hsumm := summable_sigmaNat_div_pow (2 * m) 2 le_rfl
    let C_sum : ℝ := (4 / (4 * Real.pi ^ 2) ^ 2) *
      ∑' n : ℕ, (sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2)
    let C : ℝ := ‖(-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m)‖ *
      ((2 * m + 1).factorial : ℝ) * C_sum
    refine ⟨C, 1, by positivity, zero_le_one, fun v hv => ?_⟩
    let μ : ℂ := Complex.exp (I * ((0 - Real.pi / 6 : ℝ) : ℂ))
    have hμ_norm : ‖μ‖ = 1 := by
      dsimp only [μ]
      rw [show I * ((0 - Real.pi / 6 : ℝ) : ℂ) = ((-Real.pi / 6 : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have hsub_ge : ∀ n : ℕ, A_freq n / 2 ≤ ‖(A_freq n : ℂ) - μ * (v : ℂ)‖ := fun n => by
      have h1 := norm_sub_exp_mul_real_ge (-Real.pi / 6) (A_freq n) v
      have hsin : |A_freq n * Real.sin (-Real.pi / 6)| = A_freq n / 2 := by
        have hAp := A_freq_pos n
        rw [show (-Real.pi / 6 : ℝ) = -(Real.pi / 6) by ring, Real.sin_neg, mul_neg, abs_neg,
          Real.sin_pi_div_six, abs_of_pos (by positivity)]
        ring
      have hμ' : μ = Complex.exp (I * ((-Real.pi / 6 : ℝ) : ℂ)) := by
        dsimp only [μ]; congr 2; push_cast; ring
      rw [hμ']
      exact hsin.symm.trans_le h1
    have hadd_ge : ∀ n : ℕ, A_freq n / 2 ≤ ‖(A_freq n : ℂ) + μ * (v : ℂ)‖ := fun n => by
      have hcos : 0 ≤ Real.cos (-Real.pi / 6) := by
        rw [show (-Real.pi / 6 : ℝ) = -(Real.pi / 6) by ring, Real.cos_neg, Real.cos_pi_div_six]
        positivity
      have h1 := norm_add_exp_mul_real_ge (-Real.pi / 6) hcos (A_freq_pos n).le hv
      have hμ' : μ = Complex.exp (I * ((-Real.pi / 6 : ℝ) : ℂ)) := by
        dsimp only [μ]; congr 2; push_cast; ring
      rw [hμ']
      exact le_trans (by linarith [A_freq_pos n]) h1
    let cbd : ℝ := 4 / (4 * Real.pi ^ 2) ^ 2
    have hterm_bd : ∀ n : ℕ,
        ‖((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
            ((A_freq n : ℂ) ^ 2 - (μ * (v : ℂ)) ^ 2)⁻¹‖ ≤
          cbd * ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2)) := fun n => by
      have hAp := A_freq_pos n
      have h1 := S_even_term_norm_le (m := m) (n := n) (hsub_ge n) (hadd_ge n)
        (by positivity) (by positivity)
      refine h1.trans_eq ?_
      dsimp only [cbd, A_freq]
      have hpi0 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
      have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      rw [pow_add ((n + 1 : ℕ) : ℝ) (2 * m) 2]
      field_simp [hpi0, hn0]
      ring
    have hdom : Summable (fun n : ℕ => cbd * ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2))) :=
      hsumm.mul_left cbd
    have hsn : Summable (fun n : ℕ => ‖((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
        ((A_freq n : ℂ) ^ 2 - (μ * (v : ℂ)) ^ 2)⁻¹‖) :=
      hdom.of_norm_bounded fun n => by rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hterm_bd n
    have hS_bd : ‖S_even m (μ * (v : ℂ))‖ ≤ C_sum := by
      dsimp only [S_even, C_sum]
      calc ‖∑' n : ℕ, _‖ ≤ ∑' n : ℕ, ‖_‖ := norm_tsum_le_tsum_norm hsn
        _ ≤ ∑' n : ℕ, cbd * ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2)) :=
            hsn.tsum_le_tsum hterm_bd hdom
        _ = cbd * ∑' n : ℕ, (sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2) :=
            tsum_mul_left
    have hv_pow : v ^ (2 * m + 1) ≤ ((2 * m + 1).factorial : ℝ) * Real.exp v := by
      have h1 := Real.pow_div_factorial_le_exp v hv (2 * m + 1)
      have hfac : (0 : ℝ) < ((2 * m + 1).factorial : ℝ) := by positivity
      exact (div_le_iff₀ hfac).mp h1 |>.trans_eq (by ring)
    change ‖μ * K_even m (μ * (v : ℂ))‖ ≤ C * Real.exp (1 * v)
    rw [norm_mul, hμ_norm, one_mul, K_even, norm_mul, norm_mul, norm_mul, norm_pow (-1 : ℂ),
      norm_pow (μ * (v : ℂ)), norm_mul, hμ_norm, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hv, ← norm_pow (-1 : ℂ)]
    calc ‖(-1 : ℂ) ^ (m + 1)‖ * ‖4 / (4 * (Real.pi : ℂ) ^ 2) ^ m‖ * v ^ (2 * m + 1) *
            ‖S_even m (μ * (v : ℂ))‖
        = ‖(-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m)‖ * v ^ (2 * m + 1) *
            ‖S_even m (μ * (v : ℂ))‖ := by rw [← norm_mul]
      _ ≤ ‖(-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m)‖ *
            (((2 * m + 1).factorial : ℝ) * Real.exp v) * C_sum := by gcongr
      _ = C * Real.exp (1 * v) := by dsimp only [C]; rw [one_mul]; ring

private lemma formalSeries_K_even (m : ℕ) (hm : 1 ≤ m) :
    formalSeries (K_even m) =
      PowerSeries.X * (emSeries (hFun m) +
        PowerSeries.C ((bernoulli (2 * m) : ℂ) / ((2 * m : ℕ) : ℂ)) *
          PowerSeries.X ^ (2 * m - 1)) := by
  let term : ℕ → ℂ → ℂ := fun n z =>
    ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
      ((A_freq n : ℂ) ^ 2 - z ^ 2)⁻¹
  let R : ℝ := 2 * Real.pi ^ 2
  have hR : 0 < R := by positivity
  have h_an : ∀ n : ℕ, AnalyticOnNhd ℂ (term n) (Metric.ball 0 R) := fun n z hz => by
    obtain ⟨hsub, hadd⟩ := A_freq_ball_lower hz
    have hpos : 0 < 2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) := by positivity
    refine AnalyticAt.mul analyticAt_const ((analyticAt_const.sub (analyticAt_id.pow 2)).inv ?_)
    have hsq : (A_freq n : ℂ) ^ 2 - z ^ 2 =
        ((A_freq n : ℂ) - z) * ((A_freq n : ℂ) + z) := by ring
    change (A_freq n : ℂ) ^ 2 - z ^ 2 ≠ 0
    rw [hsq]
    exact mul_ne_zero (fun h0 => by rw [h0, norm_zero] at hsub; linarith)
      (fun h0 => by rw [h0, norm_zero] at hadd; linarith)
  have hsumm := summable_sigmaNat_div_pow (2 * m) 2 le_rfl
  have h_bd : ∀ k : ℕ, ∃ u : ℕ → ℝ, Summable u ∧
      ∀ (n : ℕ) (z : ℂ), z ∈ Metric.ball 0 R → ‖iteratedDeriv k (term n) z‖ ≤ u n := fun k => by
    let ck : ℝ := (k.factorial : ℝ) / ((4 * Real.pi ^ 2) * (2 * Real.pi ^ 2) ^ (k + 1))
    refine ⟨fun n => ck * ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2)),
      hsumm.mul_left ck, fun n z hz => ?_⟩
    obtain ⟨hsub, hadd⟩ := A_freq_ball_lower hz
    have hpos : 0 < 2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ) := by positivity
    have hA_ne : (A_freq n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (A_freq_pos n).ne'
    have hz1 : z ≠ (A_freq n : ℂ) := fun h0 => by
      have : (A_freq n : ℂ) - z = 0 := by rw [h0, sub_self]
      rw [this, norm_zero] at hsub; linarith
    have hz2 : (A_freq n : ℂ) + z ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at hadd; linarith
    dsimp only [term]
    rw [iteratedDeriv_const_mul_field
      ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m))
      (fun ζ : ℂ => ((A_freq n : ℂ) ^ 2 - ζ ^ 2)⁻¹),
      norm_mul, norm_div, Complex.norm_natCast, norm_pow, Complex.norm_natCast,
      iteratedDeriv_sq_sub_inv (A_freq n : ℂ) k hA_ne hz1 hz2,
      norm_mul, norm_inv, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (A_freq_pos n)]
    have hinv1 : ‖(k.factorial : ℂ) / ((A_freq n : ℂ) - z) ^ (k + 1)‖ ≤
        (k.factorial : ℝ) / (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)) ^ (k + 1) := by
      rw [norm_div, Complex.norm_natCast, norm_pow]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hpos _)
        (pow_le_pow_left₀ hpos.le hsub _)
    have hinv2 : ‖(-1 : ℂ) ^ k * (k.factorial : ℂ) / ((A_freq n : ℂ) + z) ^ (k + 1)‖ ≤
        (k.factorial : ℝ) / (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)) ^ (k + 1) := by
      rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
        Complex.norm_natCast, norm_pow]
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (pow_pos hpos _)
        (pow_le_pow_left₀ hpos.le hadd _)
    have hadd_bd : ‖(k.factorial : ℂ) / ((A_freq n : ℂ) - z) ^ (k + 1) +
        (-1 : ℂ) ^ k * (k.factorial : ℂ) / ((A_freq n : ℂ) + z) ^ (k + 1)‖ ≤
        2 * ((k.factorial : ℝ) / (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)) ^ (k + 1)) := by
      calc ‖_‖ ≤ ‖(k.factorial : ℂ) / ((A_freq n : ℂ) - z) ^ (k + 1)‖ +
            ‖(-1 : ℂ) ^ k * (k.factorial : ℂ) / ((A_freq n : ℂ) + z) ^ (k + 1)‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hn1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hpow_le : ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2) ≤ ((n + 1 : ℕ) : ℝ) ^ (2 * m + k + 2) :=
      pow_le_pow_right₀ hn1 (by omega)
    calc ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m)) *
          ((2 * A_freq n)⁻¹ * ‖_‖)
        ≤ ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m)) *
            ((2 * A_freq n)⁻¹ * (2 * ((k.factorial : ℝ) / (2 * Real.pi ^ 2 * ((n + 1 : ℕ) : ℝ)) ^ (k + 1)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (by linarith)
              (inv_nonneg.mpr (mul_nonneg zero_le_two (A_freq_pos n).le)))
            (by positivity)
      _ = ck * ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + k + 2)) := by
          dsimp only [ck, A_freq]
          have hpow_den : ((n + 1 : ℕ) : ℝ) ^ (2 * m + k + 2) =
              ((n + 1 : ℕ) : ℝ) ^ (2 * m) * ((n + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) ^ (k + 1) := by
            rw [show 2 * m + k + 2 = (2 * m + 1) + (k + 1) by omega, pow_add, pow_succ]
          rw [mul_pow, hpow_den]
          have hpi1 : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          have hpi2 : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
          have hn0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
          field_simp [hpi1, hpi2, hn0]
      _ ≤ ck * ((sigmaNat (2 * m) (n + 1) : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (2 * m + 2)) := by
          gcongr
  have hS_an : AnalyticOnNhd ℂ (S_even m) (Metric.ball 0 R) := by
    have hdiff : DifferentiableOn ℂ (S_even m) (Metric.ball 0 R) := by
      obtain ⟨u, hu_sum, hu_bd⟩ := h_bd 0
      refine Complex.differentiableOn_tsum_of_summable_norm hu_sum
        (fun n => (h_an n).differentiableOn) Metric.isOpen_ball fun n z hz => by
        have h0 := hu_bd n z hz
        simp only [iteratedDeriv_zero] at h0
        exact h0
    exact hdiff.analyticOnNhd Metric.isOpen_ball
  have hS_deriv : ∀ s : ℕ, iteratedDeriv s (S_even m) 0 =
      ∑' n : ℕ, ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
        ((2 * (A_freq n : ℂ))⁻¹ * ((s.factorial : ℂ) / (A_freq n : ℂ) ^ (s + 1) *
          (1 + (-1 : ℂ) ^ s))) := fun s => by
    have hts := iteratedDeriv_tsum_ball hR term h_an h_bd s
    change iteratedDeriv s (S_even m) 0 = _ at hts
    rw [hts]
    refine tsum_congr fun n => ?_
    have hA_ne : (A_freq n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (A_freq_pos n).ne'
    dsimp only [term]
    rw [iteratedDeriv_const_mul_field
      ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m))
      (fun ζ : ℂ => ((A_freq n : ℂ) ^ 2 - ζ ^ 2)⁻¹),
      iteratedDeriv_sq_sub_inv (A_freq n : ℂ) s hA_ne hA_ne.symm (by simpa using hA_ne)]
    simp only [sub_zero, add_zero]
    field_simp [hA_ne]
  let Cm : ℂ := (-1 : ℂ) ^ (m + 1) * (4 / (4 * (Real.pi : ℂ) ^ 2) ^ m)
  have hK_deriv : ∀ r : ℕ, iteratedDeriv r (K_even m) 0 =
      if r < 2 * m + 1 then 0
      else Cm * ((r.factorial : ℂ) / ((r - (2 * m + 1)).factorial : ℂ)) *
        iteratedDeriv (r - (2 * m + 1)) (S_even m) 0 := fun r => by
    have hprod_eq : K_even m = fun z : ℂ => Cm * (z ^ (2 * m + 1) * S_even m z) := by
      funext z; dsimp only [K_even, Cm]; ring
    rw [hprod_eq, iteratedDeriv_const_mul_field Cm (fun z : ℂ => z ^ (2 * m + 1) * S_even m z)]
    have hpow_c : ContDiffAt ℂ r (fun z : ℂ => z ^ (2 * m + 1)) 0 :=
      (analyticAt_id.pow (2 * m + 1)).contDiffAt.of_le le_top
    have hS_c : ContDiffAt ℂ r (S_even m) 0 :=
      (hS_an 0 (Metric.mem_ball_self hR)).contDiffAt.of_le le_top
    rw [iteratedDeriv_fun_mul hpow_c hS_c]
    have hid : ∀ i : ℕ, iteratedDeriv i (fun z : ℂ => z ^ (2 * m + 1)) 0 =
        if i = 2 * m + 1 then ((2 * m + 1).factorial : ℂ) else 0 := fun i => by
      rw [iteratedDeriv_fun_pow_zero]
      split_ifs <;> simp
    split_ifs with hlt
    · have hz_sum : ∑ i ∈ Finset.range (r + 1),
          (r.choose i : ℂ) * iteratedDeriv i (fun z : ℂ => z ^ (2 * m + 1)) 0 *
            iteratedDeriv (r - i) (S_even m) 0 = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi_lt : i < 2 * m + 1 := (Finset.mem_range.mp hi).trans_le (by omega)
        simp [hid i, hi_lt.ne]
      rw [hz_sum, mul_zero]
    · have hle : 2 * m + 1 ≤ r := by omega
      rw [Finset.sum_eq_single (2 * m + 1)]
      · rw [hid (2 * m + 1)]
        simp only [↓reduceIte]
        have hch := congrArg (fun k : ℕ => (k : ℂ)) (Nat.choose_mul_factorial_mul_factorial hle)
        push_cast at hch
        have hfac1 : ((2 * m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        have hfac2 : ((r - (2 * m + 1)).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        field_simp [hfac1, hfac2]
        linear_combination Cm * (iteratedDeriv (r - (2 * m + 1)) (S_even m) 0) * hch
      · intro i _ hine; simp [hid i, hine]
      · intro hnot; exact absurd (Finset.mem_range.mpr (by omega)) hnot
  ext n
  cases n with
  | zero =>
    simp [formalSeries, PowerSeries.coeff_mul]
  | succ r =>
    have hL : PowerSeries.coeff (r + 1) (formalSeries (K_even m)) = iteratedDeriv r (K_even m) 0 := by
      simp [formalSeries]
    rw [hL, PowerSeries.coeff_succ_X_mul, map_add, emSeries, PowerSeries.coeff_mk,
      PowerSeries.coeff_C_mul_X_pow, hK_deriv r]
    by_cases hlt : r < 2 * m - 1
    · have hlt' : r < 2 * m + 1 := by omega
      have hne : r ≠ 2 * m - 1 := by omega
      simp [hlt', hne, emTerm, iteratedDeriv_hFun_zero, hlt]
    · by_cases h_eq : r = 2 * m - 1
      · subst h_eq
        have hlt' : 2 * m - 1 < 2 * m + 1 := by omega
        simp only [hlt', ↓reduceIte, emTerm, iteratedDeriv_hFun_zero, lt_self_iff_false,
          Nat.sub_self, bernoulli_zero, Rat.cast_one, mul_one]
        have hodd : (-1 : ℂ) ^ (2 * m - 1) = -1 := by
          have h2m1 : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
          rw [h2m1, pow_succ, show (-1 : ℂ) ^ (2 * (m - 1)) = 1 from by rw [pow_mul]; norm_num]
          ring
        have hfac : ((2 * m - 1 + 1).factorial : ℂ) =
            ((2 * m : ℕ) : ℂ) * ((2 * m - 1).factorial : ℂ) := by
          have hs : 2 * m - 1 + 1 = 2 * m := by omega
          rw [hs, show 2 * m = (2 * m - 1) + 1 by omega, Nat.factorial_succ]
          push_cast; ring
        have hfac1 : ((2 * m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
        have hm2 : ((2 * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : 2 * m ≠ 0)
        rw [hodd, hfac, show 2 * m - 1 + 1 = 2 * m by omega]
        field_simp [hfac1, hm2]
        ring
      · by_cases heven_r : Even r
        · obtain ⟨q, rfl⟩ := heven_r
          have hne_2m1 : q + q ≠ 2 * m - 1 := by omega
          have hodd_rp1 : Odd (q + q + 1) := ⟨q, by omega⟩
          have hbern0 : bernoulli (q + q + 1) = 0 :=
            bernoulli_eq_zero_of_odd hodd_rp1 (by omega)
          have hR_zero : emTerm (hFun m) (q + q) +
              (if q + q = 2 * m - 1 then (bernoulli (2 * m) : ℂ) / ((2 * m : ℕ) : ℂ) else 0) = 0 := by
            simp [hne_2m1, emTerm, hbern0]
          rw [hR_zero]
          split_ifs with hlt'
          · rfl
          · have hs_odd : Odd (q + q - (2 * m + 1)) := ⟨q - m - 1, by omega⟩
            have hS0 : iteratedDeriv (q + q - (2 * m + 1)) (S_even m) 0 = 0 := by
              have hneg : (-1 : ℂ) ^ (q + q - (2 * m + 1)) = -1 := by
                rcases hs_odd with ⟨t, ht⟩
                rw [ht, pow_succ, show (-1 : ℂ) ^ (2 * t) = 1 from by rw [pow_mul]; norm_num]
                ring
              rw [hS_deriv]
              have hz_n : ∀ n : ℕ,
                  ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
                    ((2 * (A_freq n : ℂ))⁻¹ * (((q + q - (2 * m + 1)).factorial : ℂ) /
                      (A_freq n : ℂ) ^ (q + q - (2 * m + 1) + 1) * (1 + (-1 : ℂ) ^ (q + q - (2 * m + 1))))) = 0 :=
                fun n => by rw [hneg]; ring
              simp_rw [hz_n]
              exact tsum_zero
            rw [hS0, mul_zero]
        · obtain ⟨k, rfl⟩ := Nat.not_even_iff_odd.mp heven_r
          have hk_ge : m ≤ k := by omega
          let p : ℕ := k + 1 - m
          have hp_pos : 1 ≤ p := by omega
          have hnot_lt' : ¬ (2 * k + 1 < 2 * m + 1) := by omega
          have hne_2m1 : 2 * k + 1 ≠ 2 * m - 1 := by omega
          have hnot_lt_sub : ¬ (2 * k + 1 < 2 * m - 1) := by omega
          simp only [hnot_lt', hne_2m1, ↓reduceIte, add_zero]
          have hs_eq : 2 * k + 1 - (2 * m + 1) = 2 * (p - 1) := by omega
          rw [hs_eq, hS_deriv (2 * (p - 1))]
          have hneg1 : (-1 : ℂ) ^ (2 * (p - 1)) = 1 := by rw [pow_mul]; norm_num
          simp_rw [hneg1]
          have hsum_eq : ∑' n : ℕ, ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
                ((2 * (A_freq n : ℂ))⁻¹ * (((2 * (p - 1)).factorial : ℂ) /
                  (A_freq n : ℂ) ^ (2 * (p - 1) + 1) * (1 + 1))) =
              (((2 * (p - 1)).factorial : ℂ) / (4 * (Real.pi : ℂ) ^ 2) ^ (2 * p)) *
                ∑' n : ℕ, ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m + 2 * p)) := by
            have hstep : ∀ n : ℕ,
                ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m)) *
                  ((2 * (A_freq n : ℂ))⁻¹ * (((2 * (p - 1)).factorial : ℂ) /
                    (A_freq n : ℂ) ^ (2 * (p - 1) + 1) * (1 + 1))) =
                (((2 * (p - 1)).factorial : ℂ) / (4 * (Real.pi : ℂ) ^ 2) ^ (2 * p)) *
                  ((sigmaNat (2 * m) (n + 1) : ℂ) / ((n + 1 : ℕ) : ℂ) ^ (2 * m + 2 * p)) := fun n => by
              have hAn : (A_freq n : ℂ) = (4 * (Real.pi : ℂ) ^ 2) * ((n + 1 : ℕ) : ℂ) := by
                dsimp only [A_freq]; push_cast; ring
              have hpi : (4 * (Real.pi : ℂ) ^ 2 : ℂ) ≠ 0 :=
                mul_ne_zero (by norm_num) (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
              have hn0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
              have hexp_p : 2 * (p - 1) + 1 + 1 = 2 * p := by omega
              rw [pow_add ((n + 1 : ℕ) : ℂ) (2 * m) (2 * p), hAn,
                mul_pow (4 * (Real.pi : ℂ) ^ 2) ((n + 1 : ℕ) : ℂ) (2 * (p - 1) + 1)]
              have h4_eq : (4 * (Real.pi : ℂ) ^ 2) ^ (2 * p) =
                  (4 * (Real.pi : ℂ) ^ 2) * (4 * (Real.pi : ℂ) ^ 2) ^ (2 * (p - 1) + 1) := by
                rw [← pow_succ', hexp_p]
              have hn_eq : ((n + 1 : ℕ) : ℂ) ^ (2 * p) =
                  ((n + 1 : ℕ) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ (2 * (p - 1) + 1) := by
                rw [← pow_succ', hexp_p]
              field_simp [hpi, hn0]
              rw [h4_eq, hn_eq]
              ring
            simp_rw [hstep, tsum_mul_left]
          rw [hsum_eq, tsum_sigmaNat_div_pow (2 * m) (2 * p) (by omega)]
          have hz_p := riemannZeta_two_mul_nat (by omega : p ≠ 0)
          have hz_mp := riemannZeta_two_mul_nat (by omega : m + p ≠ 0)
          have hp_eq : ((2 * p : ℕ) : ℂ) = 2 * (p : ℂ) := by push_cast; ring
          have hmp_eq2 : ((2 * m + 2 * p : ℕ) : ℂ) = 2 * ((m + p : ℕ) : ℂ) := by push_cast; ring
          rw [hp_eq, hz_p, hmp_eq2, hz_mp]
          simp only [emTerm, iteratedDeriv_hFun_zero, hnot_lt_sub, ↓reduceIte]
          have hsub_r : 2 * k + 1 - (2 * m - 1) = 2 * p := by omega
          have hrp1 : 2 * k + 1 + 1 = 2 * (m + p) := by omega
          rw [hsub_r, hrp1]
          have hneg_r : (-1 : ℂ) ^ (2 * k + 1) = -1 := by
            rw [pow_succ, show (-1 : ℂ) ^ (2 * k) = 1 from by rw [pow_mul]; norm_num]; ring
          rw [hneg_r]
          have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
          have hfac_p : ((2 * p).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          have hfac_p1 : ((2 * (p - 1)).factorial : ℂ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          have hfac_mp : ((2 * (m + p)).factorial : ℂ) ≠ 0 :=
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
          have h4m : (4 * (Real.pi : ℂ) ^ 2) ^ m ≠ 0 :=
            pow_ne_zero m (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi))
          have h4p : (4 * (Real.pi : ℂ) ^ 2) ^ (2 * p) ≠ 0 :=
            pow_ne_zero (2 * p) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi))
          have hsign_prod : (-1 : ℂ) ^ (m + 1) * (-1 : ℂ) ^ (p + 1) * (-1 : ℂ) ^ (m + p + 1) = -1 := by
            rw [← pow_add, ← pow_add, show m + 1 + (p + 1) + (m + p + 1) = 2 * (m + p + 1) + 1 by omega,
              pow_succ, show (-1 : ℂ) ^ (2 * (m + p + 1)) = 1 from by rw [pow_mul]; norm_num]
            ring
          have hpow2 : (2 : ℂ) ^ (2 * p - 1) * (2 : ℂ) ^ (2 * (m + p) - 1) * 4 =
              (4 : ℂ) ^ m * (4 : ℂ) ^ (2 * p) := by
            have he1 : (2 * p - 1) + (2 * (m + p) - 1) + 2 = 2 * m + 2 * (2 * p) := by omega
            calc (2 : ℂ) ^ (2 * p - 1) * (2 : ℂ) ^ (2 * (m + p) - 1) * 4
                = (2 : ℂ) ^ (2 * p - 1) * (2 : ℂ) ^ (2 * (m + p) - 1) * (2 : ℂ) ^ 2 := by norm_num
              _ = (2 : ℂ) ^ ((2 * p - 1) + (2 * (m + p) - 1) + 2) := by rw [← pow_add, ← pow_add]
              _ = (2 : ℂ) ^ (2 * m + 2 * (2 * p)) := by rw [he1]
              _ = ((2 : ℂ) ^ 2) ^ m * ((2 : ℂ) ^ 2) ^ (2 * p) := by
                  rw [pow_add, pow_mul, pow_mul]
              _ = (4 : ℂ) ^ m * (4 : ℂ) ^ (2 * p) := by norm_num
          have hpow_pi : (Real.pi : ℂ) ^ (2 * p) * (Real.pi : ℂ) ^ (2 * (m + p)) =
              ((Real.pi : ℂ) ^ 2) ^ m * ((Real.pi : ℂ) ^ 2) ^ (2 * p) := by
            rw [← pow_add, show 2 * p + 2 * (m + p) = 2 * m + 2 * (2 * p) by omega,
              pow_add, pow_mul, pow_mul]
          dsimp only [Cm]
          field_simp [hfac_p1, hfac_p, hfac_mp, h4m, h4p]
          rw [mul_pow (4 : ℂ) ((Real.pi : ℂ) ^ 2) m, mul_pow (4 : ℂ) ((Real.pi : ℂ) ^ 2) (2 * p)]
          calc (-1 : ℂ) ^ (m + 1) * 4 * ((2 * k + 1).factorial : ℂ) *
                (-1 : ℂ) ^ (p + 1) * (2 : ℂ) ^ (2 * p - 1) * (Real.pi : ℂ) ^ (2 * p) *
                  (bernoulli (2 * p) : ℂ) *
                (-1 : ℂ) ^ (m + p + 1) * (2 : ℂ) ^ (2 * (m + p) - 1) *
                  (Real.pi : ℂ) ^ (2 * (m + p)) * (bernoulli (2 * (m + p)) : ℂ)
              = (((-1 : ℂ) ^ (m + 1) * (-1 : ℂ) ^ (p + 1) * (-1 : ℂ) ^ (m + p + 1)) *
                  ((2 : ℂ) ^ (2 * p - 1) * (2 : ℂ) ^ (2 * (m + p) - 1) * 4) *
                  ((Real.pi : ℂ) ^ (2 * p) * (Real.pi : ℂ) ^ (2 * (m + p)))) *
                  ((2 * k + 1).factorial : ℂ) * (bernoulli (2 * p) : ℂ) *
                  (bernoulli (2 * (m + p)) : ℂ) := by ring
            _ = (-1 : ℂ) * ((4 : ℂ) ^ m * (4 : ℂ) ^ (2 * p)) *
                  (((Real.pi : ℂ) ^ 2) ^ m * ((Real.pi : ℂ) ^ 2) ^ (2 * p)) *
                  ((2 * k + 1).factorial : ℂ) * (bernoulli (2 * p) : ℂ) *
                  (bernoulli (2 * (m + p)) : ℂ) := by rw [hsign_prod, hpow2, hpow_pi]
            _ = _ := by ring

/-- Scaled Euler–Maclaurin remainder `f_{2m}(u)` (`m ≥ 1`) matching `formalSeries (K_even m)`. -/
@[expose] def f_even (m : ℕ) (u : ℝ) : ℂ :=
  (u : ℂ)⁻¹ * (sumScale (hFun m) u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), hFun m y)) +
    ((bernoulli (2 * m) : ℂ) / ((2 * m : ℕ) : ℂ)) * (u : ℂ)⁻¹ ^ (2 * m)

private lemma iteratedDeriv_inv_pow_real (a j : ℕ) {u : ℝ} (hu : u ≠ 0) :
    ∃ C : ℂ, (iteratedDeriv j (fun x : ℝ => (x : ℂ)⁻¹ ^ a)) =ᶠ[𝓝 u]
      fun v : ℝ => C * (v : ℂ)⁻¹ ^ (a + j) := by
  induction j generalizing a with
  | zero =>
    refine ⟨1, Filter.Eventually.of_forall fun v => by simp⟩
  | succ j ih =>
    obtain ⟨C, hC⟩ := ih a
    refine ⟨-(((a + j : ℕ) : ℂ) * C), ?_⟩
    have hne : ∀ᶠ v in 𝓝 u, v ≠ 0 := (isOpen_ne (x := (0 : ℝ))).mem_nhds hu
    filter_upwards [hC.eventuallyEq_nhds, hne] with v hv hv0
    rw [iteratedDeriv_succ, hv.deriv_eq]
    have h1 : HasDerivAt (fun x : ℝ => C * (x : ℂ)⁻¹ ^ (a + j))
        (-(((a + j : ℕ) : ℂ) * C) * (v : ℂ)⁻¹ ^ (a + (j + 1))) v := by
      have hd := (hasDerivAt_inv_pow_complex (j := a + j) hv0).const_mul C
      refine hd.congr_deriv ?_
      rw [show a + j + 1 = a + (j + 1) by omega]
      ring
    exact h1.deriv

private lemma f_even_hasAsympExp (m : ℕ) (hm : 1 ≤ m) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (f_even m)) (d_u^[j] (formalSeries (K_even m))) := by
  let c2m : ℂ := ∫ y in Ioi (0 : ℝ), hFun m y
  let g2m : ℝ → ℂ := fun u => sumScale (hFun m) u - (u : ℂ) * c2m
  let b2m : ℂ := (bernoulli (2 * m) : ℂ) / ((2 * m : ℕ) : ℂ)
  have hg2m_asymp : ∀ k : ℕ, HasAsympExp (iteratedDeriv k g2m) (d_u^[k] (emSeries (hFun m))) :=
    fun k => sumScale_iteratedDeriv_hasAsympExp (hFun_expDecaySmooth m) k
  have hg2m_contDiff : ∀ (k : ℕ) (u : ℝ), 0 < u → ContDiffAt ℝ k g2m u := fun k u hu => by
    have h1 : ContDiffOn ℝ k g2m (Ioi (0 : ℝ)) :=
      (sumScale_contDiffOn (hFun_expDecaySmooth m) k).sub
        ((Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).mul contDiffOn_const)
    exact h1.contDiffAt (isOpen_Ioi.mem_nhds hu)
  have hinv1_contDiff : ∀ (k : ℕ) (u : ℝ), 0 < u → ContDiffAt ℝ k (fun v : ℝ => (v : ℂ)⁻¹) u :=
    fun k u hu => (Complex.ofRealCLM.contDiff.contDiffAt.inv
      (Complex.ofReal_ne_zero.mpr hu.ne')).of_le (WithTop.coe_le_coe.mpr le_top)
  have hinv_contDiff : ∀ (a k : ℕ) (u : ℝ), 0 < u →
      ContDiffAt ℝ k (fun v : ℝ => (v : ℂ)⁻¹ ^ a) u := fun a k u hu =>
    ((hinv1_contDiff k u hu).pow a)
  have hf_asymp_any : ∀ k : ℕ, ∃ T : PowerSeries ℂ, HasAsympExp (iteratedDeriv k (f_even m)) T := by
    intro k
    let p1 : ℝ → ℂ := fun u => (u : ℂ)⁻¹ * g2m u
    let p2 : ℝ → ℂ := fun u => b2m * (u : ℂ)⁻¹ ^ (2 * m)
    have hp1_asymp : ∃ T1 : PowerSeries ℂ, HasAsympExp (iteratedDeriv k p1) T1 := by
      let coeffs : Fin (k + 1) → ℂ := fun i =>
        (k.choose i.1 : ℂ) * ((-1 : ℂ) ^ i.1 * (i.1.factorial : ℂ))
      let T1 : PowerSeries ℂ := ∑ i : Fin (k + 1),
        (PowerSeries.C (coeffs i) * PowerSeries.X ^ (i.1 + 1)) * d_u^[k - i.1] (emSeries (hFun m))
      refine ⟨T1, fun M => ?_⟩
      have hterm : ∀ i : Fin (k + 1), HasAsympExp
          (fun u : ℝ => coeffs i * (u : ℂ)⁻¹ ^ (i.1 + 1) * iteratedDeriv (k - i.1) g2m u)
          ((PowerSeries.C (coeffs i) * PowerSeries.X ^ (i.1 + 1)) * d_u^[k - i.1] (emSeries (hFun m))) :=
        fun i => ((HasAsympExp.const (coeffs i)).mul (hasAsympExp_inv_pow (i.1 + 1))).mul
          (hg2m_asymp (k - i.1))
      have hsum_asymp : HasAsympExp
          (fun u : ℝ => ∑ i : Fin (k + 1),
            coeffs i * (u : ℂ)⁻¹ ^ (i.1 + 1) * iteratedDeriv (k - i.1) g2m u) T1 := by
        dsimp only [T1]
        induction (Finset.univ : Finset (Fin (k + 1))) using Finset.induction_on with
        | empty => simpa using HasAsympExp.const 0
        | @insert a s ha ih =>
          have hadd_fn : (fun u : ℝ => ∑ i ∈ insert a s,
              coeffs i * (u : ℂ)⁻¹ ^ (i.1 + 1) * iteratedDeriv (k - i.1) g2m u) =
              fun u : ℝ => coeffs a * (u : ℂ)⁻¹ ^ (a.1 + 1) * iteratedDeriv (k - a.1) g2m u +
                ∑ i ∈ s, coeffs i * (u : ℂ)⁻¹ ^ (i.1 + 1) * iteratedDeriv (k - i.1) g2m u := by
            funext u; exact Finset.sum_insert ha
          rw [hadd_fn, Finset.sum_insert ha]
          exact (hterm a).add ih
      obtain ⟨C, hC⟩ := hsum_asymp M
      refine ⟨C, ?_⟩
      filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
      have heq_p1 : iteratedDeriv k p1 u =
          ∑ i : Fin (k + 1), coeffs i * (u : ℂ)⁻¹ ^ (i.1 + 1) * iteratedDeriv (k - i.1) g2m u := by
        have h1 : ContDiffAt ℝ k (fun v : ℝ => (v : ℂ)⁻¹) u := hinv1_contDiff k u hu_pos
        have h2 : ContDiffAt ℝ k g2m u := hg2m_contDiff k u hu_pos
        change iteratedDeriv k (fun v : ℝ => (v : ℂ)⁻¹ * g2m v) u = _
        rw [iteratedDeriv_fun_mul h1 h2, Finset.sum_fin_eq_sum_range]
        simp only [Nat.lt_succ_iff]
        refine Finset.sum_congr rfl fun i hi => ?_
        have hid_inv : ∀ r : ℕ, ∀ x : ℝ, x ≠ 0 →
            iteratedDeriv r (fun v : ℝ => (v : ℂ)⁻¹) x =
              (-1 : ℂ) ^ r * (r.factorial : ℂ) * (x : ℂ)⁻¹ ^ (r + 1) := by
          intro r x hx0
          induction r generalizing x with
          | zero => simp
          | succ r ih =>
            have hne : ∀ᶠ y in 𝓝 x, y ≠ 0 := (isOpen_ne (x := (0 : ℝ))).mem_nhds hx0
            have hev : iteratedDeriv r (fun v : ℝ => (v : ℂ)⁻¹) =ᶠ[𝓝 x]
                fun y : ℝ => (-1 : ℂ) ^ r * (r.factorial : ℂ) * (y : ℂ)⁻¹ ^ (r + 1) := by
              filter_upwards [hne] with y hy; exact ih y hy
            rw [iteratedDeriv_succ, hev.deriv_eq]
            have hd := (hasDerivAt_inv_pow_complex (j := r + 1) hx0).const_mul
              ((-1 : ℂ) ^ r * (r.factorial : ℂ))
            refine hd.deriv.trans ?_
            rw [Nat.factorial_succ, pow_succ]
            push_cast; ring
        have hi_le : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [dite_eq_left hi_le, hid_inv i u hu_pos.ne']
        dsimp only [coeffs]
        ring
      simpa only [heq_p1] using hu_bd
    have hp2_asymp : ∃ T2 : PowerSeries ℂ, HasAsympExp (iteratedDeriv k p2) T2 := by
      have hconst : ∀ r : ℕ, ∃ C2 : ℂ, ∀ x : ℝ, x ≠ 0 →
          iteratedDeriv r (fun v : ℝ => (v : ℂ)⁻¹ ^ (2 * m)) x = C2 * (x : ℂ)⁻¹ ^ (2 * m + r) := by
        intro r
        induction r with
        | zero => exact ⟨1, fun x _ => by simp⟩
        | succ r ih =>
          obtain ⟨C2, hC2⟩ := ih
          refine ⟨-(((2 * m + r : ℕ) : ℂ) * C2), fun x hx0 => ?_⟩
          have hne : ∀ᶠ y in 𝓝 x, y ≠ 0 := (isOpen_ne (x := (0 : ℝ))).mem_nhds hx0
          have hev : iteratedDeriv r (fun v : ℝ => (v : ℂ)⁻¹ ^ (2 * m)) =ᶠ[𝓝 x]
              fun y : ℝ => C2 * (y : ℂ)⁻¹ ^ (2 * m + r) := by
            filter_upwards [hne] with y hy; exact hC2 y hy
          rw [iteratedDeriv_succ, hev.deriv_eq]
          have hd := (hasDerivAt_inv_pow_complex (j := 2 * m + r) hx0).const_mul C2
          refine hd.deriv.trans ?_
          rw [show 2 * m + r + 1 = 2 * m + (r + 1) by omega]
          ring
      obtain ⟨C2, hC2⟩ := hconst k
      refine ⟨PowerSeries.C (b2m * C2) * PowerSeries.X ^ (2 * m + k), fun M => ?_⟩
      obtain ⟨C, hC⟩ := ((HasAsympExp.const (b2m * C2)).mul (hasAsympExp_inv_pow (2 * m + k))) M
      refine ⟨C, ?_⟩
      filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
      have heq_p2 : iteratedDeriv k p2 u = b2m * C2 * (u : ℂ)⁻¹ ^ (2 * m + k) := by
        dsimp only [p2]
        rw [iteratedDeriv_const_mul_field b2m (fun v : ℝ => (v : ℂ)⁻¹ ^ (2 * m)),
          hC2 u hu_pos.ne']
        ring
      simpa only [heq_p2] using hu_bd
    obtain ⟨T1, hT1⟩ := hp1_asymp
    obtain ⟨T2, hT2⟩ := hp2_asymp
    refine ⟨T1 + T2, fun M => ?_⟩
    obtain ⟨C, hC⟩ := (hT1.add hT2) M
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_gt_atTop (0 : ℝ)] with u hu_bd hu_pos
    have heq_sum : iteratedDeriv k (f_even m) u = iteratedDeriv k p1 u + iteratedDeriv k p2 u := by
      have hc1 : ContDiffAt ℝ k p1 u :=
        (hinv1_contDiff k u hu_pos).mul (hg2m_contDiff k u hu_pos)
      have hc2 : ContDiffAt ℝ k p2 u :=
        contDiffAt_const.mul (hinv_contDiff (2 * m) k u hu_pos)
      exact iteratedDeriv_add hc1 hc2
    simpa only [heq_sum] using hu_bd
  have hf_zero : HasAsympExp (f_even m) (formalSeries (K_even m)) := by
    rw [formalSeries_K_even m hm]
    have h_eq : (PowerSeries.X : PowerSeries ℂ) * (emSeries (hFun m) +
        PowerSeries.C b2m * PowerSeries.X ^ (2 * m - 1)) =
        PowerSeries.X ^ 1 * emSeries (hFun m) + PowerSeries.C b2m * PowerSeries.X ^ (2 * m) := by
      rw [mul_add, pow_one, ← mul_assoc, mul_comm (PowerSeries.X : PowerSeries ℂ) (PowerSeries.C b2m),
        mul_assoc, ← pow_succ']
      rw [show 2 * m - 1 + 1 = 2 * m by omega]
    rw [h_eq]
    have h0 : HasAsympExp (fun u : ℝ => sumScale (hFun m) u - (u : ℂ) * c2m) (emSeries (hFun m)) := by
      simpa only [iteratedDeriv_zero, Function.iterate_zero, id_eq] using
        (sumScale_iteratedDeriv_hasAsympExp (hFun_expDecaySmooth m) 0)
    have h1 : HasAsympExp (fun u : ℝ => (u : ℂ)⁻¹ * (sumScale (hFun m) u - (u : ℂ) * c2m))
        (PowerSeries.X ^ 1 * emSeries (hFun m)) := by
      simpa only [pow_one] using (hasAsympExp_inv_pow 1).mul h0
    exact h1.add ((HasAsympExp.const b2m).mul (hasAsympExp_inv_pow (2 * m)))
  have hf_contDiffOn : ∀ n : ℕ, ContDiffOn ℝ n (f_even m) (Ioi (0 : ℝ)) := fun n => by
    have hinv1_on : ContDiffOn ℝ n (fun v : ℝ => (v : ℂ)⁻¹) (Ioi (0 : ℝ)) :=
      (Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).inv fun v hv =>
        Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
    have hg_on : ContDiffOn ℝ n g2m (Ioi (0 : ℝ)) :=
      (sumScale_contDiffOn (hFun_expDecaySmooth m) n).sub
        ((Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).mul contDiffOn_const)
    have hp1_on : ContDiffOn ℝ n (fun u : ℝ => (u : ℂ)⁻¹ * g2m u) (Ioi (0 : ℝ)) :=
      hinv1_on.mul hg_on
    have hp2_on : ContDiffOn ℝ n (fun u : ℝ => b2m * (u : ℂ)⁻¹ ^ (2 * m)) (Ioi (0 : ℝ)) :=
      contDiffOn_const.mul (hinv1_on.pow (2 * m))
    exact hp1_on.add hp2_on
  induction j with
  | zero => simpa using hf_zero
  | succ j ih =>
    obtain ⟨T, hT⟩ := hf_asymp_any (j + 1)
    have hT_deriv : HasAsympExp (deriv (iteratedDeriv j (f_even m))) T := by
      simpa only [← iteratedDeriv_succ] using hT
    have hsmooth : ∀ᶠ u : ℝ in atTop,
        DifferentiableAt ℝ (iteratedDeriv j (f_even m)) u ∧
          ContinuousAt (deriv (iteratedDeriv j (f_even m))) u := by
      have hc : ContDiffOn ℝ ((j + 2 : ℕ) : ℕ∞) (f_even m) (Ioi (0 : ℝ)) := hf_contDiffOn (j + 2)
      have hd_on : DifferentiableOn ℝ (iteratedDerivWithin j (f_even m) (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) :=
        hc.differentiableOn_iteratedDerivWithin (by exact_mod_cast (by omega : j < j + 2))
          isOpen_Ioi.uniqueDiffOn
      have hcont_on : ContinuousOn (iteratedDerivWithin (j + 1) (f_even m) (Ioi (0 : ℝ)))
          (Ioi (0 : ℝ)) :=
        hc.continuousOn_iteratedDerivWithin (by exact_mod_cast (by omega : j + 1 ≤ j + 2))
          isOpen_Ioi.uniqueDiffOn
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu_pos
      have hev_j : iteratedDerivWithin j (f_even m) (Ioi (0 : ℝ)) =ᶠ[𝓝 u]
          iteratedDeriv j (f_even m) := by
        filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with v hv
        exact iteratedDerivWithin_of_isOpen isOpen_Ioi hv
      have hev_j1 : iteratedDerivWithin (j + 1) (f_even m) (Ioi (0 : ℝ)) =ᶠ[𝓝 u]
          deriv (iteratedDeriv j (f_even m)) := by
        filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with v hv
        rw [iteratedDerivWithin_of_isOpen isOpen_Ioi hv, iteratedDeriv_succ]
      exact ⟨(hd_on.differentiableAt (isOpen_Ioi.mem_nhds hu_pos)).congr_of_eventuallyEq hev_j.symm,
        ((hcont_on u hu_pos).continuousAt (isOpen_Ioi.mem_nhds hu_pos)).congr hev_j1⟩
    have hEq := HasAsympExp.deriv_of_hasAsympExp ih hT_deriv hsmooth
    rw [Function.iterate_succ_apply', ← hEq, iteratedDeriv_succ]
    exact hT_deriv

/-! ### 5C. Coordinate Transfers (`autonomous_ode_deriv`, `log u → u`, Homogenization, Affine) & Ray Identities -/

private def triangularInv {R : Type*} [Field R] {J : ℕ}
    (a b : Fin J → R) (c : Fin J → Fin J → R) : ℕ → MvPolynomial (Fin J) R
  | n =>
    if hn : n < J then
      let k : Fin J := ⟨n, hn⟩
      MvPolynomial.C (a k)⁻¹ *
        (MvPolynomial.X k - MvPolynomial.C (b k) -
          ∑ i ∈ (Finset.range n).attach,
            if hi : i.1 < J then MvPolynomial.C (c k ⟨i.1, hi⟩) * triangularInv a b c i.1 else 0)
    else 0
termination_by n => n
decreasing_by
  exact Finset.mem_range.mp i.2

private lemma triangular_aeval_injective {R : Type*} [Field R] {J : ℕ}
    (a b : Fin J → R) (c : Fin J → Fin J → R) (ha : ∀ k, a k ≠ 0)
    (Φ : Fin J → MvPolynomial (Fin J) R)
    (hΦ : ∀ k : Fin J, Φ k = MvPolynomial.C (a k) * MvPolynomial.X k + MvPolynomial.C (b k) +
      ∑ i ∈ Finset.range k.1,
        if hi : i < J then MvPolynomial.C (c k ⟨i, hi⟩) * MvPolynomial.X ⟨i, hi⟩ else 0) :
    Function.Injective (MvPolynomial.aeval Φ : MvPolynomial (Fin J) R →ₐ[R] MvPolynomial (Fin J) R) := by
  let ψ : Fin J → MvPolynomial (Fin J) R := fun k => triangularInv a b c k.1
  have hleft : ∀ k : Fin J, MvPolynomial.aeval ψ (Φ k) = MvPolynomial.X k := fun k => by
    rw [hΦ k, map_add, map_add, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      MvPolynomial.aeval_C, map_sum]
    have hsum : (∑ i ∈ Finset.range k.1, MvPolynomial.aeval ψ
        (if hi : i < J then MvPolynomial.C (c k ⟨i, hi⟩) * MvPolynomial.X ⟨i, hi⟩ else 0)) =
        ∑ i ∈ Finset.range k.1,
          if hi : i < J then MvPolynomial.C (c k ⟨i, hi⟩) * triangularInv a b c i else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · simp [ψ]
      · simp
    rw [hsum]
    change MvPolynomial.C (a k) * triangularInv a b c k.1 + MvPolynomial.C (b k) + _ = MvPolynomial.X k
    conv_lhs => arg 1; arg 1; arg 2; rw [triangularInv]
    rw [dite_eq_left k.isLt]
    dsimp only
    simp only [Fin.eta]
    rw [Finset.sum_attach (Finset.range k.1)
      (fun i => if hi : i < J then MvPolynomial.C (c k ⟨i, hi⟩) * triangularInv a b c i else 0)]
    have hinv : (MvPolynomial.C (a k) : MvPolynomial (Fin J) R) * MvPolynomial.C (a k)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (ha k), map_one]
    linear_combination (MvPolynomial.X k - MvPolynomial.C (b k) -
      ∑ i ∈ Finset.range k.1,
        if hi : i < J then MvPolynomial.C (c k ⟨i, hi⟩) * triangularInv a b c i else 0) * hinv
  intro P Q hPQ
  have hcomp : ∀ R' : MvPolynomial (Fin J) R,
      MvPolynomial.aeval ψ (MvPolynomial.aeval Φ R') = R' := fun R' => by
    rw [MvPolynomial.comp_aeval_apply, show (fun k => MvPolynomial.aeval ψ (Φ k)) = MvPolynomial.X from
      funext hleft, MvPolynomial.aeval_X_left_apply]
  calc P = MvPolynomial.aeval ψ (MvPolynomial.aeval Φ P) := (hcomp P).symm
    _ = MvPolynomial.aeval ψ (MvPolynomial.aeval Φ Q) := by rw [hPQ]
    _ = Q := hcomp Q

private lemma evalU_aeval {J K : ℕ}
    (Φ : Fin J → MvPolynomial (Fin K) (Polynomial ℂ))
    (P : MvPolynomial (Fin J) (Polynomial ℂ)) (u : ℂ) (z : Fin K → ℂ) :
    MvPolynomial.eval z (MvPolynomial.map (Polynomial.evalRingHom u) (MvPolynomial.aeval Φ P)) =
      MvPolynomial.eval
        (fun j => MvPolynomial.eval z (MvPolynomial.map (Polynomial.evalRingHom u) (Φ j)))
        (MvPolynomial.map (Polynomial.evalRingHom u) P) := by
  induction P using MvPolynomial.induction_on with
  | C q =>
    simp
  | add A B hA hB =>
    simp only [map_add] at hA hB ⊢
    rw [hA, hB]
  | mul_X A j hA =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.map_X, MvPolynomial.eval_X] at hA ⊢
    rw [hA]

private lemma map_aeval_poly_rat {J K : ℕ}
    (Φ : Fin J → MvPolynomial (Fin K) (Polynomial ℂ))
    (P : MvPolynomial (Fin J) (Polynomial ℂ)) :
    MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (MvPolynomial.aeval Φ P) =
      MvPolynomial.aeval
        (fun j => MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) (Φ j))
        (MvPolynomial.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) P) := by
  induction P using MvPolynomial.induction_on with
  | C q => simp
  | add A B hA hB => simp only [map_add, hA, hB]
  | mul_X A j hA => simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hA]

private lemma analytic_poly_jet_eq_zero {J : ℕ} {φ : ℝ → ℂ}
    (hφ : ∀ y : ℝ, AnalyticAt ℝ φ y) (P : MvPolynomial (Fin J) ℂ)
    {x : ℝ}
    (hx : ∀ᶠ y in 𝓝 x, MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P = 0) :
    ∀ y : ℝ, MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P = 0 := by
  have han_jet : ∀ (k : ℕ) (y : ℝ), AnalyticAt ℝ (iteratedDeriv k φ) y := fun k y => by
    induction k generalizing y with
    | zero => simpa using hφ y
    | succ k ih => rw [iteratedDeriv_succ]; exact (ih y).deriv
  have han_poly : AnalyticOnNhd ℝ
      (fun y : ℝ => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P) Set.univ := by
    clear hx
    intro y _
    induction P using MvPolynomial.induction_on with
    | C a => simpa using analyticAt_const
    | add A B hA hB =>
      rw [show (fun z : ℝ => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ z) (A + B)) =
          (fun z => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ z) A) +
            fun z => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ z) B from
        funext fun z => map_add _ A B]
      exact hA.add hB
    | mul_X A j hA =>
      rw [show (fun z : ℝ => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ z)
            (A * MvPolynomial.X j)) =
          (fun z => MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ z) A) *
            iteratedDeriv j.1 φ from
        (funext fun z => by rw [map_mul, MvPolynomial.eval_X]; rfl)]
      exact hA.mul (han_jet j.1 y)
  intro y
  exact han_poly.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    convex_univ.isPreconnected (Set.mem_univ x) hx (Set.mem_univ y)

private lemma analytic_poly_jet_eq_zero_of_atTop {J : ℕ} {φ : ℝ → ℂ}
    (hφ : ∀ y : ℝ, AnalyticAt ℝ φ y) (P : MvPolynomial (Fin J) ℂ)
    (htop : ∀ᶠ y : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P = 0) :
    ∀ y : ℝ, MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P = 0 := by
  obtain ⟨R, hR⟩ := eventually_atTop.mp htop
  have hnhds : ∀ᶠ y in 𝓝 (R + 1),
      MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P = 0 := by
    filter_upwards [isOpen_Ioi.mem_nhds (by linarith : R < R + 1)] with y hy
    exact hR y (le_of_lt hy)
  exact analytic_poly_jet_eq_zero hφ P hnhds

private lemma mvPolynomial_finZero_eq_C {R : Type*} [CommSemiring R]
    (P : MvPolynomial (Fin 0) R) : P = MvPolynomial.C (P.coeff 0) := by
  ext m
  have hm : m = 0 := Subsingleton.elim m 0
  subst hm
  simp

private lemma autonomous_ode_deriv {φ : ℝ → ℂ} (hφ : ∀ y : ℝ, AnalyticAt ℝ φ y)
    {J : ℕ} (P : MvPolynomial (Fin J) ℂ) (hP_ne : P ≠ 0)
    (hP_top : ∀ᶠ y : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 φ y) P = 0) :
    ∃ (J' : ℕ) (P' : MvPolynomial (Fin J') ℂ), P' ≠ 0 ∧
      ∀ᶠ y : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin J' => iteratedDeriv j.1 (deriv φ) y) P' = 0 := by
  classical
  cases J with
  | zero =>
    have hc := mvPolynomial_finZero_eq_C P
    obtain ⟨y, hy⟩ := hP_top.exists
    rw [hc, MvPolynomial.eval_C] at hy
    exact absurd (hc.trans (by rw [hy, map_zero])) hP_ne
  | succ r =>
    have hall : ∀ y : ℝ, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 φ y) P = 0 :=
      analytic_poly_jet_eq_zero_of_atTop hφ P hP_top
    let P_nat : MvPolynomial ℕ ℂ := MvPolynomial.rename Fin.val P
    have hPnat_ne : P_nat ≠ 0 := by
      intro h0
      exact hP_ne (MvPolynomial.rename_injective Fin.val Fin.val_injective (by simpa [P_nat] using h0))
    have hPnat_eq : ∀ y ∈ (Set.univ : Set ℝ),
        MvPolynomial.eval (fun i : ℕ => iteratedDeriv i φ y) P_nat = 0 := fun y _ => by
      dsimp only [P_nat]
      rw [MvPolynomial.eval_rename]
      exact hall y
    obtain ⟨n, Q, x, _, ordinary, ident⟩ :=
      ordinary_relation (Set.univ : Set ℝ) ⟨0, Set.mem_univ 0⟩
        (fun i y => iteratedDeriv i φ y) ⟨P_nat, hPnat_ne, hPnat_eq⟩
    have ident_all : ∀ z : ℝ,
        MvPolynomial.eval (fun i : Fin (n + 1) => iteratedDeriv i.1 φ z) Q = 0 :=
      fun z => ident z (Set.mem_univ z)
    let v : Fin (n + 1) → ℝ → ℂ := fun i z => iteratedDeriv i.1 φ z
    let g : Fin (n + 1) → ℝ → ℂ := fun i z =>
      MvPolynomial.eval (fun j => v j z) (MvPolynomial.pderiv i Q)
    have hd : ∀ (z : ℝ) (i : Fin (n + 1)), DifferentiableAt ℝ (v i) z := fun z i => by
      have han : ∀ (k : ℕ) (w : ℝ), AnalyticAt ℝ (iteratedDeriv k φ) w := fun k w => by
        induction k generalizing w with
        | zero => simpa using hφ w
        | succ k ih => rw [iteratedDeriv_succ]; exact (ih w).deriv
      exact (han i.1 z).differentiableAt
    have chain : ∀ (A : MvPolynomial (Fin (n + 1)) ℂ) (z : ℝ),
        HasDerivAt (fun p => MvPolynomial.eval (fun i => v i p) A)
          (∑ i, MvPolynomial.eval (fun j => v j z) (MvPolynomial.pderiv i A) * deriv (v i) z) z :=
      fun A z => polynomial_chain A v (fun i => deriv (v i)) z fun i => (hd z i).hasDerivAt
    have vanish : ∀ z : ℝ, ∑ i, g i z * deriv (v i) z = 0 := fun z => by
      have near : (fun w => MvPolynomial.eval (fun i => v i w) Q) =ᶠ[𝓝 z] (fun _ => 0) :=
        Filter.Eventually.of_forall ident_all
      exact (chain Q z).deriv.symm.trans (near.deriv_eq.trans (deriv_const _ _))
    cases n with
    | zero =>
      have hcont_g0 : ContinuousAt (g 0) x := (chain (MvPolynomial.pderiv 0 Q) x).continuousAt
      have hg0_nz : ∀ᶠ z in 𝓝 x, g 0 z ≠ 0 := hcont_g0.eventually_ne ordinary
      have hderiv0_nhds : ∀ᶠ z in 𝓝 x, deriv φ z = 0 := by
        filter_upwards [hg0_nz] with z hz
        have hvz := vanish z
        rw [Fin.sum_univ_one] at hvz
        have hdv : deriv (v 0) z = deriv φ z := by simp [v]
        rw [hdv] at hvz
        exact (mul_eq_zero.mp hvz).resolve_left hz
      have hderiv0_all : ∀ y : ℝ, deriv φ y = 0 := fun y => by
        simpa [iteratedDeriv_zero] using
          analytic_poly_jet_eq_zero (fun z => (hφ z).deriv)
            (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℂ)
            (by simpa [iteratedDeriv_zero] using hderiv0_nhds) y
      refine ⟨1, MvPolynomial.X 0, MvPolynomial.X_ne_zero 0, ?_⟩
      exact Eventually.of_forall fun y => by simpa [iteratedDeriv_zero] using hderiv0_all y
    | succ m =>
      let top : Fin (m + 2) := Fin.last (m + 1)
      let S : ℝ → ℂ := g top
      let invS : ℝ → ℂ := fun z => (S z)⁻¹
      let uState : Fin (m + 2) ⊕ Unit → ℝ → ℂ := Sum.elim v (fun _ => invS)
      let G := Generated uState x
      have gv : ∀ i : Fin (m + 2), G (v i) := fun i => Generated.coord (u := uState) (.inl i)
      have gw : G invS := Generated.coord (u := uState) (.inr ())
      have gc : ∀ c : ℂ, G (fun _ => c) := fun c => Generated.const _
      have gg : ∀ i : Fin (m + 2), G (g i) := fun i => Generated.evalPoly v gv _
      have Snz : ∀ᶠ z in 𝓝 x, S z ≠ 0 :=
        (chain (MvPolynomial.pderiv top Q) x).continuousAt.eventually_ne ordinary
      have low : ∀ i : Fin (m + 2), i ≠ top → G (deriv (v i)) := fun i hi => by
        obtain ⟨k, hk⟩ := i
        have hlt : k + 1 < m + 2 := by
          have hne : k ≠ m + 1 := fun eqn => hi (Fin.ext eqn)
          omega
        refine (gv ⟨k + 1, hlt⟩).congr (Eventually.of_forall fun z => ?_)
        change iteratedDeriv (k + 1) φ z = deriv (fun w => iteratedDeriv k φ w) z
        rw [iteratedDeriv_succ]
      let lowSum : ℝ → ℂ := ∑ i ∈ Finset.univ.erase top, g i * deriv (v i)
      have gl : G lowSum :=
        Generated.finsetSum _ _ fun i hi => (gg i).mul (low i (Finset.mem_erase.mp hi).1)
      have dv : ∀ i : Fin (m + 2), G (deriv (v i)) := fun i => by
        by_cases hi : i = top
        · subst hi
          apply (((gc (-1)).mul gl).mul gw).congr
          filter_upwards [Snz] with z nz
          have he := vanish z
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ top)] at he
          change (-1) * lowSum z * (S z)⁻¹ = deriv (v top) z
          have hh : S z * deriv (v top) z + lowSum z = 0 := by
            simpa [S, lowSum, Finset.sum_apply] using he
          field_simp [nz]
          linear_combination -hh
        · exact low i hi
      have dS : G (deriv S) := by
        let D : Fin (m + 2) → ℝ → ℂ := fun i z =>
          MvPolynomial.eval (fun k => v k z) (MvPolynomial.pderiv i (MvPolynomial.pderiv top Q))
        have gen : ∀ i, G (D i) := fun i => Generated.evalPoly v gv _
        apply (Generated.finsetSum Finset.univ _ fun i _ => (gen i).mul (dv i)).congr
        filter_upwards with z
        simpa [D, Finset.sum_apply] using (chain (MvPolynomial.pderiv top Q) z).deriv.symm
      have smooth : ∀ᶠ z in 𝓝 x, ∀ i, DifferentiableAt ℝ (uState i) z := by
        filter_upwards [Snz] with z nz i
        rcases i with i | ⟨⟩
        · exact hd z i
        · exact (chain (MvPolynomial.pderiv top Q) z).differentiableAt.inv nz
      have closed : ∀ i, G (deriv (uState i)) := fun i => by
        rcases i with i | ⟨⟩
        · exact dv i
        · apply (((gc (-1)).mul dS).mul (gw.pow 2)).congr
          filter_upwards [Snz] with z nz
          have hi := ((chain (MvPolynomial.pderiv top Q) z).differentiableAt.hasDerivAt.inv nz).deriv
          change (-1) * deriv S z * ((S z)⁻¹) ^ 2 = deriv invS z
          change deriv invS z = -deriv S z / (S z) ^ 2 at hi
          rw [hi]; simp [inv_pow, div_eq_mul_inv]
      have readout : G (deriv φ) :=
        (gv ⟨1, by omega⟩).congr (Eventually.of_forall fun z => by
          change iteratedDeriv 1 φ z = deriv φ z
          rw [iteratedDeriv_one])
      obtain ⟨R, hR_ne, hR_nhds⟩ := autonomous_readout uState x (deriv φ) readout smooth closed
      refine ⟨_, R, hR_ne, eventually_atTop.mpr ⟨0, fun y _ => ?_⟩⟩
      exact analytic_poly_jet_eq_zero (fun z => (hφ z).deriv) R hR_nhds y

/-- Stirling numbers of the second kind `S(k, j)` in `ℂ`. -/
private def stirling2C : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | k + 1, j + 1 => ((j + 1 : ℕ) : ℂ) * stirling2C k (j + 1) + stirling2C k j

private lemma stirling2C_eq_zero_of_lt {k j : ℕ} (hkj : k < j) : stirling2C k j = 0 := by
  induction k generalizing j with
  | zero =>
    cases j with
    | zero => omega
    | succ j => rfl
  | succ k ih =>
    cases j with
    | zero => omega
    | succ j =>
      simp only [stirling2C]
      rw [ih (by omega), ih (by omega)]
      ring

private lemma stirling2C_self (k : ℕ) : stirling2C k k = 1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [stirling2C, stirling2C_eq_zero_of_lt (Nat.lt_succ_self k), ih]
    ring

private lemma contDiffOn_Ioi_iteratedDeriv_differentiableAt {F : ℝ → ℂ}
    (hF : ∀ n : ℕ, ContDiffOn ℝ n F (Ioi (0 : ℝ))) (r : ℕ) {u : ℝ} (hu : 0 < u) :
    DifferentiableAt ℝ (iteratedDeriv r F) u := by
  have hcd : ContDiffOn ℝ ((r + 1 : ℕ) : ℕ∞) F (Ioi (0 : ℝ)) := hF (r + 1)
  have hd_on : DifferentiableOn ℝ (iteratedDerivWithin r F (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) :=
    hcd.differentiableOn_iteratedDerivWithin (by exact_mod_cast (by omega : r < r + 1))
      isOpen_Ioi.uniqueDiffOn
  have hev : iteratedDeriv r F =ᶠ[𝓝 u] iteratedDerivWithin r F (Ioi (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact (iteratedDerivWithin_of_isOpen isOpen_Ioi hv).symm
  exact (hd_on.differentiableAt (isOpen_Ioi.mem_nhds hu)).congr_of_eventuallyEq hev

private lemma iteratedDeriv_comp_exp {F : ℝ → ℂ}
    (hF : ∀ n : ℕ, ContDiffOn ℝ n F (Ioi (0 : ℝ))) :
    ∀ (k : ℕ) (y : ℝ),
      iteratedDeriv k (fun z : ℝ => F (Real.exp z)) y =
        ∑ j ∈ Finset.range (k + 1),
          stirling2C k j * (Real.exp y : ℂ) ^ j * iteratedDeriv j F (Real.exp y) := by
  intro k
  induction k with
  | zero => intro y; simp [stirling2C]
  | succ k ih =>
    intro y
    have heq_fn : iteratedDeriv k (fun z : ℝ => F (Real.exp z)) = fun z : ℝ =>
        ∑ j ∈ Finset.range (k + 1),
          stirling2C k j * (Real.exp z : ℂ) ^ j * iteratedDeriv j F (Real.exp z) :=
      funext ih
    rw [iteratedDeriv_succ, heq_fn]
    have hterm_deriv : ∀ j ∈ Finset.range (k + 1),
        HasDerivAt
          (fun z : ℝ => stirling2C k j * (Real.exp z : ℂ) ^ j * iteratedDeriv j F (Real.exp z))
          (stirling2C k j * (j : ℂ) * ((Real.exp y : ℂ) ^ j * iteratedDeriv j F (Real.exp y)) +
            stirling2C k j * ((Real.exp y : ℂ) ^ (j + 1) * iteratedDeriv (j + 1) F (Real.exp y)))
          y := fun j _ => by
      have hexp : HasDerivAt (fun z : ℝ => (Real.exp z : ℂ)) (Real.exp y : ℂ) y :=
        (Real.hasDerivAt_exp y).ofReal_comp
      have hpow : HasDerivAt (fun z : ℝ => (Real.exp z : ℂ) ^ j)
          ((j : ℂ) * (Real.exp y : ℂ) ^ j) y := by
        cases j with
        | zero => simpa using hasDerivAt_const y (1 : ℂ)
        | succ j' =>
          have hd := hexp.pow (j' + 1)
          refine hd.congr_deriv ?_
          rw [pow_succ ((Real.exp y : ℂ)) j']
          push_cast; ring
      have hF' : HasDerivAt (fun z : ℝ => iteratedDeriv j F (Real.exp z))
          (iteratedDeriv (j + 1) F (Real.exp y) * (Real.exp y : ℂ)) y := by
        have hdf := (contDiffOn_Ioi_iteratedDeriv_differentiableAt hF j (Real.exp_pos y)).hasDerivAt
        have hs := hdf.scomp y (Real.hasDerivAt_exp y)
        refine hs.congr_deriv ?_
        rw [Complex.real_smul, ← iteratedDeriv_succ]
        ring
      have hprod := (hpow.const_mul (stirling2C k j)).mul hF'
      refine hprod.congr_deriv ?_
      rw [pow_succ]
      ring
    have hsum_deriv : HasDerivAt
        (fun z : ℝ => ∑ j ∈ Finset.range (k + 1),
          stirling2C k j * (Real.exp z : ℂ) ^ j * iteratedDeriv j F (Real.exp z))
        (∑ j ∈ Finset.range (k + 1),
          (stirling2C k j * (j : ℂ) * ((Real.exp y : ℂ) ^ j * iteratedDeriv j F (Real.exp y)) +
            stirling2C k j * ((Real.exp y : ℂ) ^ (j + 1) * iteratedDeriv (j + 1) F (Real.exp y))))
        y := by
      refine (HasDerivAt.sum hterm_deriv).congr_of_eventuallyEq (Eventually.of_forall fun z => ?_)
      simp only [Finset.sum_apply]
    rw [hsum_deriv.deriv, Finset.sum_add_distrib]
    let T : ℕ → ℂ := fun j => (Real.exp y : ℂ) ^ j * iteratedDeriv j F (Real.exp y)
    have h1 : (∑ j ∈ Finset.range (k + 1), stirling2C k j * (j : ℂ) * T j) =
        ∑ j ∈ Finset.range (k + 2), stirling2C k j * (j : ℂ) * T j := by
      conv_rhs =>
        rw [Finset.sum_range_succ, stirling2C_eq_zero_of_lt (Nat.lt_succ_self k),
          zero_mul, zero_mul, add_zero]
    have h2 : (∑ j ∈ Finset.range (k + 1), stirling2C k j * T (j + 1)) =
        ∑ j ∈ Finset.range (k + 2), (if j = 0 then 0 else stirling2C k (j - 1)) * T j := by
      rw [Finset.sum_range_succ' (fun j => (if j = 0 then 0 else stirling2C k (j - 1)) * T j)]
      simp
    dsimp only [T] at h1 h2
    rw [h1, h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    cases j with
    | zero => simp [stirling2C]
    | succ j' =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, stirling2C]
      ring

private lemma autonomous_log_to_poly_ode {ψ : ℝ → ℂ} (hψ : ∀ y : ℝ, AnalyticAt ℝ ψ y)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) ℂ) (hP_ne : P ≠ 0)
    (hP_top : ∀ᶠ y : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 ψ y) P = 0) :
    ∃ Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ), Q ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 (fun v => ψ (Real.log v)) u)
          (evalU Q (u : ℂ)) = 0 := by
  have hall : ∀ y : ℝ, MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 ψ y) P = 0 :=
    analytic_poly_jet_eq_zero_of_atTop hψ P hP_top
  let F : ℝ → ℂ := fun u => ψ (Real.log u)
  have hF_cd : ∀ n : ℕ, ContDiffOn ℝ n F (Ioi (0 : ℝ)) := fun n => by
    have hψ_cd : ContDiff ℝ (⊤ : ℕ∞) ψ :=
      contDiff_iff_contDiffAt.mpr fun y => (hψ y).contDiffAt
    have hlog_cd : ContDiffOn ℝ (⊤ : ℕ∞) Real.log (Ioi (0 : ℝ)) :=
      Real.contDiffOn_log.mono fun x hx => ne_of_gt hx
    exact (hψ_cd.comp_contDiffOn hlog_cd).of_le (WithTop.coe_le_coe.mpr le_top)
  let Φ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := fun k =>
    ∑ j ∈ Finset.range (k.1 + 1),
      if hj : j < r + 1 then
        MvPolynomial.C (Polynomial.C (stirling2C k.1 j) * Polynomial.X ^ j) * MvPolynomial.X ⟨j, hj⟩
      else 0
  let Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    MvPolynomial.aeval Φ (MvPolynomial.map Polynomial.C P)
  refine ⟨Q, ?_, ?_⟩
  · let ι : Polynomial ℂ →+* RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ)
    have hι_inj : Function.Injective ι := RatFunc.algebraMap_injective ℂ
    have hx_rat_ne : (RatFunc.X : RatFunc ℂ) ≠ 0 := by
      rw [← RatFunc.algebraMap_X]
      exact (map_ne_zero_iff ι hι_inj).mpr Polynomial.X_ne_zero
    have ha_ne : ∀ k : Fin (r + 1), (RatFunc.X ^ k.1 : RatFunc ℂ) ≠ 0 := fun k =>
      pow_ne_zero k.1 hx_rat_ne
    let Φ_rat : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := fun k =>
      MvPolynomial.map ι (Φ k)
    have hΦ_rat : ∀ k : Fin (r + 1),
        Φ_rat k =
          MvPolynomial.C (RatFunc.X ^ k.1 : RatFunc ℂ) * MvPolynomial.X k +
            MvPolynomial.C (0 : RatFunc ℂ) +
            ∑ i ∈ Finset.range k.1,
              if hi : i < r + 1 then
                MvPolynomial.C (RatFunc.C (stirling2C k.1 i) * RatFunc.X ^ i) *
                  MvPolynomial.X ⟨i, hi⟩
              else 0 := fun k => by
      dsimp only [Φ_rat, Φ]
      rw [map_sum, Finset.sum_range_succ, dite_eq_left k.isLt, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X]
      have hhead : (∑ x ∈ Finset.range k.1, MvPolynomial.map ι
          (if hj : x < r + 1 then
            MvPolynomial.C (Polynomial.C (stirling2C k.1 x) * Polynomial.X ^ x) *
              MvPolynomial.X (⟨x, hj⟩ : Fin (r + 1))
          else 0)) =
          ∑ i ∈ Finset.range k.1,
            if hi : i < r + 1 then
              MvPolynomial.C (RatFunc.C (stirling2C k.1 i) * RatFunc.X ^ i) *
                MvPolynomial.X (⟨i, hi⟩ : Fin (r + 1))
            else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · simp [ι, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
        · simp
      have htop : ι (Polynomial.C (stirling2C k.1 k.1) * Polynomial.X ^ k.1) =
          (RatFunc.X ^ k.1 : RatFunc ℂ) := by
        rw [stirling2C_self, map_one, one_mul, map_pow, RatFunc.algebraMap_X]
      simp only [Fin.eta]
      rw [htop, hhead, map_zero, add_zero]
      exact add_comm _ _
    have hinj := triangular_aeval_injective (R := RatFunc ℂ)
      (fun k => RatFunc.X ^ k.1) (fun _ => 0)
      (fun k i => RatFunc.C (stirling2C k.1 i.1) * RatFunc.X ^ i.1) ha_ne Φ_rat hΦ_rat
    intro hQ0
    have hmap0 : MvPolynomial.map ι Q = 0 := by rw [hQ0, map_zero]
    dsimp only [Q] at hmap0
    rw [map_aeval_poly_rat, MvPolynomial.map_map] at hmap0
    have hP0_rat : MvPolynomial.map (ι.comp Polynomial.C) P = 0 :=
      hinj (hmap0.trans (map_zero _).symm)
    have hcomp_inj : Function.Injective (ι.comp Polynomial.C : ℂ →+* RatFunc ℂ) :=
      hι_inj.comp Polynomial.C_injective
    exact hP_ne ((MvPolynomial.map_injective (σ := Fin (r + 1)) _ hcomp_inj)
      (hP0_rat.trans (map_zero _).symm))
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    have hev_comp : (fun z : ℝ => F (Real.exp z)) = ψ := by
      funext z; simp [F, Real.log_exp]
    have hderiv_k : ∀ k : Fin (r + 1),
        iteratedDeriv k.1 ψ (Real.log u) =
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 F u)
            (evalU (Φ k) (u : ℂ)) := fun k => by
      have hid := iteratedDeriv_comp_exp hF_cd k.1 (Real.log u)
      rw [hev_comp, Real.exp_log hu] at hid
      rw [hid]
      dsimp only [Φ, evalU]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj_lt : j < r + 1 :=
        Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) k.isLt
      rw [dite_eq_left hj_lt, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
        Polynomial.coe_evalRingHom, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
      simp [Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
    have hev_Q : MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 F u)
        (evalU Q (u : ℂ)) =
        MvPolynomial.eval (fun k : Fin (r + 1) => iteratedDeriv k.1 ψ (Real.log u))
          (evalU (MvPolynomial.map Polynomial.C P) (u : ℂ)) := by
      dsimp only [Q, evalU]
      rw [evalU_aeval]
      refine congrArg (fun f => MvPolynomial.eval f _) (funext fun k => ?_)
      simpa [evalU] using (hderiv_k k).symm
    have heval_C : evalU (MvPolynomial.map Polynomial.C P) (u : ℂ) = P := by
      dsimp only [evalU]
      rw [MvPolynomial.map_map]
      have hid_hom : (Polynomial.evalRingHom (u : ℂ)).comp Polynomial.C = RingHom.id ℂ := by
        ext x; simp
      rw [hid_hom, MvPolynomial.map_id]
    rw [hev_Q, heval_C]
    exact hall (Real.log u)

private lemma iteratedDeriv_inv_real (r : ℕ) {u : ℝ} (hu : u ≠ 0) :
    iteratedDeriv r (fun v : ℝ => (v : ℂ)⁻¹) u =
      (-1 : ℂ) ^ r * (r.factorial : ℂ) * (u : ℂ)⁻¹ ^ (r + 1) := by
  induction r generalizing u with
  | zero => simp
  | succ r ih =>
    have hne : ∀ᶠ y in 𝓝 u, y ≠ 0 := (isOpen_ne (x := (0 : ℝ))).mem_nhds hu
    have hev : iteratedDeriv r (fun v : ℝ => (v : ℂ)⁻¹) =ᶠ[𝓝 u]
        fun y : ℝ => (-1 : ℂ) ^ r * (r.factorial : ℂ) * (y : ℂ)⁻¹ ^ (r + 1) := by
      filter_upwards [hne] with y hy; exact ih hy
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hd := (hasDerivAt_inv_pow_complex (j := r + 1) hu).const_mul
      ((-1 : ℂ) ^ r * (r.factorial : ℂ))
    refine hd.deriv.trans ?_
    rw [Nat.factorial_succ, pow_succ]
    push_cast; ring

private lemma homogenize_inv_mul_ode {G H : ℝ → ℂ}
    (hGH : ∀ u : ℝ, 0 < u → G u = H u * (u : ℂ)⁻¹)
    (hH_cd : ∀ n : ℕ, ContDiffOn ℝ n H (Ioi (0 : ℝ)))
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hQ_ne : Q ≠ 0)
    (hQ_top : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 G u) (evalU Q (u : ℂ)) = 0) :
    ∃ Q_hom : MvPolynomial (Fin (r + 1)) (Polynomial ℂ), Q_hom ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 H u) (evalU Q_hom (u : ℂ)) = 0 := by
  let M : ℕ := r + 1
  let d : ℕ := Q.totalDegree
  let c_inv : Fin (r + 1) → Fin (r + 1) → Polynomial ℂ := fun k i =>
    Polynomial.C ((k.1.choose i.1 : ℂ) * (-1 : ℂ) ^ (k.1 - i.1) * ((k.1 - i.1).factorial : ℂ)) *
      Polynomial.X ^ (M - (k.1 - i.1 + 1))
  let Φ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := fun k =>
    ∑ i ∈ Finset.range (k.1 + 1),
      if hi : i < r + 1 then MvPolynomial.C (c_inv k ⟨i, hi⟩) * MvPolynomial.X ⟨i, hi⟩ else 0
  let Q_hom : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) :=
    ∑ α ∈ Q.support,
      MvPolynomial.C (Q.coeff α * Polynomial.X ^ (M * (d - ∑ k : Fin (r + 1), α k))) *
        ∏ k : Fin (r + 1), (Φ k) ^ (α k)
  refine ⟨Q_hom, ?_, ?_⟩
  · let ι : Polynomial ℂ →+* RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ)
    have hι_inj : Function.Injective ι := RatFunc.algebraMap_injective ℂ
    have hx_ne : (RatFunc.X : RatFunc ℂ) ≠ 0 := by
      rw [← RatFunc.algebraMap_X]
      exact (map_ne_zero_iff ι hι_inj).mpr Polynomial.X_ne_zero
    let xM : RatFunc ℂ := RatFunc.X ^ M
    have hxM_ne : xM ≠ 0 := pow_ne_zero M hx_ne
    let ψ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := fun k =>
      MvPolynomial.C xM⁻¹ * MvPolynomial.map ι (Φ k)
    have hψ_tri : ∀ k : Fin (r + 1),
        ψ k =
          MvPolynomial.C (RatFunc.X⁻¹ : RatFunc ℂ) * MvPolynomial.X k +
            MvPolynomial.C (0 : RatFunc ℂ) +
            ∑ i ∈ Finset.range k.1,
              if hi : i < r + 1 then
                MvPolynomial.C (xM⁻¹ * ι (c_inv k ⟨i, hi⟩)) * MvPolynomial.X ⟨i, hi⟩
              else 0 := fun k => by
      dsimp only [ψ, Φ]
      rw [map_sum, Finset.sum_range_succ, mul_add, Finset.mul_sum]
      have hhead : (∑ i ∈ Finset.range k.1, MvPolynomial.C xM⁻¹ * MvPolynomial.map ι
          (if hi : i < r + 1 then
            MvPolynomial.C (c_inv k ⟨i, hi⟩) * MvPolynomial.X (⟨i, hi⟩ : Fin (r + 1)) else 0)) =
          ∑ i ∈ Finset.range k.1,
            if hi : i < r + 1 then
              MvPolynomial.C (xM⁻¹ * ι (c_inv k ⟨i, hi⟩)) * MvPolynomial.X (⟨i, hi⟩ : Fin (r + 1))
            else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · simp only [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
          rw [← mul_assoc, ← map_mul]
        · simp
      have htop : MvPolynomial.C xM⁻¹ * MvPolynomial.map ι
          (if hk : k.1 < r + 1 then
            MvPolynomial.C (c_inv k ⟨k.1, hk⟩) * MvPolynomial.X ⟨k.1, hk⟩ else 0) =
          MvPolynomial.C (RatFunc.X⁻¹ : RatFunc ℂ) * MvPolynomial.X k := by
        rw [dite_eq_left k.isLt, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
          ← mul_assoc, ← map_mul]
        have hcoeff : xM⁻¹ * ι (c_inv k ⟨k.1, k.isLt⟩) = (RatFunc.X⁻¹ : RatFunc ℂ) := by
          dsimp only [c_inv, xM]
          simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, pow_zero, Nat.factorial_zero,
            mul_one, zero_add, Polynomial.C_1, one_mul]
          rw [map_pow, RatFunc.algebraMap_X]
          have hM_sub : M - 1 = r := by omega
          rw [hM_sub, show M = r + 1 from rfl, pow_succ]
          field_simp [hx_ne]
        simp only [Fin.eta]
        rw [hcoeff]
      rw [htop, hhead, map_zero, add_zero]
      exact add_comm _ _
    have hinj := triangular_aeval_injective (R := RatFunc ℂ)
      (fun _ => (RatFunc.X⁻¹ : RatFunc ℂ)) (fun _ => 0)
      (fun k i => xM⁻¹ * ι (c_inv k i)) (fun _ => inv_ne_zero hx_ne) ψ hψ_tri
    have hmap_Qhom : MvPolynomial.map ι Q_hom =
        MvPolynomial.C (xM ^ d) * MvPolynomial.aeval ψ (MvPolynomial.map ι Q) := by
      have hQ_as_sum : MvPolynomial.map ι Q =
          ∑ α ∈ Q.support, MvPolynomial.C (ι (Q.coeff α)) * ∏ k : Fin (r + 1), MvPolynomial.X k ^ α k := by
        conv_lhs => rw [Q.as_sum, map_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [MvPolynomial.monomial_eq, Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _
          (fun _ _ => pow_zero _), map_mul, MvPolynomial.map_C, map_prod]
        refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
        rw [map_pow, MvPolynomial.map_X]
      dsimp only [Q_hom]
      rw [map_sum]
      conv_rhs => rw [hQ_as_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      have hα_le : ∑ k : Fin (r + 1), α k ≤ d := by
        have hs : (α.sum fun _ e => e) = ∑ k : Fin (r + 1), α k :=
          Finsupp.sum_fintype _ _ fun _ => rfl
        exact hs ▸ MvPolynomial.le_totalDegree hα
      have hΦ_split : ∀ k : Fin (r + 1), MvPolynomial.map ι (Φ k) = MvPolynomial.C xM * ψ k := fun k => by
        dsimp only [ψ]
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hxM_ne, map_one, one_mul]
      have hLHS1 : MvPolynomial.map ι
          (MvPolynomial.C (Q.coeff α * Polynomial.X ^ (M * (d - ∑ k : Fin (r + 1), α k)))) =
          (MvPolynomial.C (ι (Q.coeff α) * RatFunc.X ^ (M * (d - ∑ k : Fin (r + 1), α k))) :
            MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) := by
        rw [MvPolynomial.map_C, map_mul, map_pow, RatFunc.algebraMap_X]
      have hprod_C : (∏ k : Fin (r + 1), (MvPolynomial.C xM : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) ^ α k) =
          MvPolynomial.C (xM ^ ∑ k : Fin (r + 1), α k) := by
        simp_rw [← map_pow, ← map_prod, Finset.prod_pow_eq_pow_sum]
      have hLHS2 : MvPolynomial.map ι (∏ k : Fin (r + 1), Φ k ^ α k) =
          MvPolynomial.C (xM ^ ∑ k : Fin (r + 1), α k) * ∏ k : Fin (r + 1), ψ k ^ α k := by
        calc MvPolynomial.map ι (∏ k : Fin (r + 1), Φ k ^ α k)
            = ∏ k : Fin (r + 1), (MvPolynomial.C xM * ψ k) ^ α k := by
                rw [map_prod]
                refine Finset.prod_congr rfl fun k _ => ?_
                rw [map_pow, hΦ_split]
          _ = ∏ k : Fin (r + 1), ((MvPolynomial.C xM : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) ^ α k *
                ψ k ^ α k) := by
                refine Finset.prod_congr rfl fun k _ => mul_pow _ _ _
          _ = (∏ k : Fin (r + 1), (MvPolynomial.C xM : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)) ^ α k) *
                ∏ k : Fin (r + 1), ψ k ^ α k := Finset.prod_mul_distrib
          _ = MvPolynomial.C (xM ^ ∑ k : Fin (r + 1), α k) * ∏ k : Fin (r + 1), ψ k ^ α k := by
                rw [hprod_C]
      have hRHS2 : MvPolynomial.aeval ψ
            (MvPolynomial.C (ι (Q.coeff α)) * ∏ k : Fin (r + 1), MvPolynomial.X k ^ α k) =
          MvPolynomial.C (ι (Q.coeff α)) * ∏ k : Fin (r + 1), ψ k ^ α k := by
        rw [map_mul, MvPolynomial.aeval_C, map_prod]
        simp_rw [map_pow, MvPolynomial.aeval_X]
        rfl
      have hC_eq : ι (Q.coeff α) * RatFunc.X ^ (M * (d - ∑ k : Fin (r + 1), α k)) *
          xM ^ ∑ k : Fin (r + 1), α k = xM ^ d * ι (Q.coeff α) := by
        dsimp only [xM]
        rw [← pow_mul, ← pow_mul, mul_assoc (ι (Q.coeff α)), ← pow_add, ← mul_add,
          Nat.sub_add_cancel hα_le]
        ring
      rw [map_mul, hLHS1, hLHS2, hRHS2,
        ← mul_assoc (MvPolynomial.C (ι (Q.coeff α) * RatFunc.X ^ (M * (d - ∑ k : Fin (r + 1), α k)))),
        ← mul_assoc (MvPolynomial.C (xM ^ d)), ← map_mul, ← map_mul, hC_eq]
    intro hQhom0
    have hmap0 : MvPolynomial.map ι Q_hom = 0 := by rw [hQhom0, map_zero]
    rw [hmap_Qhom, mul_eq_zero] at hmap0
    rcases hmap0 with hxM0 | hae0
    · have : xM ^ d = 0 := by simpa using congrArg (MvPolynomial.eval 0) hxM0
      exact pow_ne_zero d hxM_ne this
    · have hQrat0 : MvPolynomial.map ι Q = 0 := hinj (hae0.trans (map_zero _).symm)
      exact hQ_ne ((MvPolynomial.map_injective (σ := Fin (r + 1)) ι hι_inj)
        (hQrat0.trans (map_zero _).symm))
  · filter_upwards [hQ_top, eventually_gt_atTop (0 : ℝ)] with u hu_Q hu_pos
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
    have hderiv_k : ∀ k : Fin (r + 1),
        (u : ℂ) ^ M * iteratedDeriv k.1 G u =
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 H u)
            (evalU (Φ k) (u : ℂ)) := fun k => by
      have hev_nhds : G =ᶠ[𝓝 u] fun v : ℝ => H v * (v : ℂ)⁻¹ := by
        filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with v hv
        exact hGH v hv
      have hcd_H : ContDiffAt ℝ k.1 H u := (hH_cd k.1).contDiffAt (isOpen_Ioi.mem_nhds hu_pos)
      have hcd_inv : ContDiffAt ℝ k.1 (fun v : ℝ => (v : ℂ)⁻¹) u :=
        (Complex.ofRealCLM.contDiff.contDiffAt.inv huc).of_le le_top
      rw [hev_nhds.iteratedDeriv_eq, iteratedDeriv_fun_mul hcd_H hcd_inv, Finset.mul_sum]
      dsimp only [Φ, evalU]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi_le : i ≤ k.1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hi_lt : i < r + 1 := Nat.lt_of_le_of_lt hi_le k.isLt
      rw [dite_eq_left hi_lt, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
        Polynomial.coe_evalRingHom, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        iteratedDeriv_inv_real (k.1 - i) hu_pos.ne']
      dsimp only [c_inv]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      have hexp_sum : M - (k.1 - i + 1) + (k.1 - i + 1) = M := by omega
      calc (u : ℂ) ^ M * ((k.1.choose i : ℂ) * iteratedDeriv i H u *
            ((-1 : ℂ) ^ (k.1 - i) * ((k.1 - i).factorial : ℂ) * (u : ℂ)⁻¹ ^ (k.1 - i + 1)))
          = ((k.1.choose i : ℂ) * (-1 : ℂ) ^ (k.1 - i) * ((k.1 - i).factorial : ℂ) *
              ((u : ℂ) ^ (M - (k.1 - i + 1)) * (u : ℂ) ^ (k.1 - i + 1) * (u : ℂ)⁻¹ ^ (k.1 - i + 1))) *
              iteratedDeriv i H u := by
            rw [← pow_add, hexp_sum]; ring
        _ = _ := by
            rw [mul_assoc ((u : ℂ) ^ (M - (k.1 - i + 1))), ← mul_pow, mul_inv_cancel₀ huc,
              one_pow, mul_one]
    have hsum_eval : MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 H u)
        (evalU Q_hom (u : ℂ)) =
        (u : ℂ) ^ (M * d) *
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 G u) (evalU Q (u : ℂ)) := by
      dsimp only [Q_hom, evalU]
      rw [map_sum, map_sum]
      have hQ_eval : MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 G u)
          (MvPolynomial.map (Polynomial.evalRingHom (u : ℂ)) Q) =
          ∑ α ∈ Q.support, (Q.coeff α).eval (u : ℂ) *
            ∏ k : Fin (r + 1), (iteratedDeriv k.1 G u) ^ (α k) := by
        conv_lhs => rw [Q.as_sum, map_sum, map_sum]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [MvPolynomial.monomial_eq, Finsupp.prod_of_support_subset _ (Finset.subset_univ _) _
          (fun _ _ => pow_zero _)]
        simp [Polynomial.coe_evalRingHom]
      rw [hQ_eval, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α hα => ?_
      have hα_le : ∑ k : Fin (r + 1), α k ≤ d := by
        have hs : (α.sum fun _ e => e) = ∑ k : Fin (r + 1), α k :=
          Finsupp.sum_fintype _ _ fun _ => rfl
        exact hs ▸ MvPolynomial.le_totalDegree hα
      simp only [map_mul, MvPolynomial.map_C, Polynomial.coe_evalRingHom, MvPolynomial.eval_C,
        map_prod, map_pow, Polynomial.eval_X]
      have hprod_eq : (∏ k : Fin (r + 1), (MvPolynomial.eval (fun j => iteratedDeriv j.1 H u)
          (MvPolynomial.map (Polynomial.evalRingHom (u : ℂ)) (Φ k))) ^ α k) =
          (u : ℂ) ^ (M * ∑ k : Fin (r + 1), α k) *
            ∏ k : Fin (r + 1), (iteratedDeriv k.1 G u) ^ α k := by
        calc _ = ∏ k : Fin (r + 1), ((u : ℂ) ^ M * iteratedDeriv k.1 G u) ^ α k := by
              refine Finset.prod_congr rfl fun k _ => ?_
              simpa [evalU] using congrArg (· ^ α k) (hderiv_k k).symm
          _ = ∏ k : Fin (r + 1), ((u : ℂ) ^ (M * α k) * (iteratedDeriv k.1 G u) ^ α k) := by
              refine Finset.prod_congr rfl fun k _ => ?_
              rw [mul_pow, ← pow_mul]
          _ = (∏ k : Fin (r + 1), (u : ℂ) ^ (M * α k)) *
                ∏ k : Fin (r + 1), (iteratedDeriv k.1 G u) ^ α k := Finset.prod_mul_distrib
          _ = (u : ℂ) ^ (∑ k : Fin (r + 1), M * α k) *
                ∏ k : Fin (r + 1), (iteratedDeriv k.1 G u) ^ α k := by
              rw [Finset.prod_pow_eq_pow_sum]
          _ = _ := by rw [← Finset.mul_sum]
      have hexp_u : (u : ℂ) ^ (M * (d - ∑ k : Fin (r + 1), α k)) *
          (u : ℂ) ^ (M * ∑ k : Fin (r + 1), α k) = (u : ℂ) ^ (M * d) := by
        rw [← pow_add, ← mul_add, Nat.sub_add_cancel hα_le]
      rw [hprod_eq]
      calc (Q.coeff α).eval (u : ℂ) * (u : ℂ) ^ (M * (d - ∑ k : Fin (r + 1), α k)) *
            ((u : ℂ) ^ (M * ∑ k : Fin (r + 1), α k) * ∏ k : Fin (r + 1), iteratedDeriv k.1 G u ^ α k)
          = ((u : ℂ) ^ (M * (d - ∑ k : Fin (r + 1), α k)) *
              (u : ℂ) ^ (M * ∑ k : Fin (r + 1), α k)) *
              ((Q.coeff α).eval (u : ℂ) * ∏ k : Fin (r + 1), iteratedDeriv k.1 G u ^ α k) := by ring
        _ = _ := by rw [hexp_u]
    rw [hsum_eval, hu_Q, mul_zero]

private def iteratedDerivPoly (n : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  (Polynomial.derivative (R := ℂ))^[n] p

private lemma iteratedDeriv_poly_ofReal (n : ℕ) (p : Polynomial ℂ) (x : ℝ) :
    iteratedDeriv n (fun v : ℝ => p.eval (v : ℂ)) x = (iteratedDerivPoly n p).eval (x : ℂ) := by
  induction n generalizing p with
  | zero => simp [iteratedDerivPoly]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hderiv : deriv (fun v : ℝ => p.eval (v : ℂ)) =
        fun v : ℝ => p.derivative.eval (v : ℂ) := by
      funext v
      have hd := (p.hasDerivAt (v : ℂ)).scomp v (hasDerivAt_id v).ofReal_comp
      simpa [Function.comp_def] using hd.deriv
    rw [hderiv, ih p.derivative]
    dsimp only [iteratedDerivPoly]
    exact congrArg (fun q : Polynomial ℂ => q.eval (x : ℂ))
      (Function.iterate_succ_apply (Polynomial.derivative (R := ℂ)) n p).symm

private lemma poly_ofReal_contDiffAt (p : Polynomial ℂ) (n : ℕ) (u : ℝ) :
    ContDiffAt ℝ n (fun v : ℝ => p.eval (v : ℂ)) u := by
  have heq : (fun v : ℝ => p.eval (v : ℂ)) =
      fun v : ℝ => ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * (v : ℂ) ^ i := by
    funext v
    rw [Polynomial.eval_eq_sum_range]
  rw [heq]
  exact ContDiffAt.sum fun i _ =>
    contDiffAt_const.mul ((Complex.ofRealCLM.contDiff.contDiffAt.of_le le_top).pow i)

private lemma poly_ode_of_mul_poly_add {G f : ℝ → ℂ} (a b : Polynomial ℂ) (ha : a ≠ 0)
    (hGf : ∀ u : ℝ, 0 < u → G u = a.eval (u : ℂ) * f u + b.eval (u : ℂ))
    (hf_cd : ∀ n : ℕ, ContDiffOn ℝ n f (Ioi (0 : ℝ)))
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hQ_ne : Q ≠ 0)
    (hQ_top : ∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 G u) (evalU Q (u : ℂ)) = 0) :
    ∃ Q' : MvPolynomial (Fin (r + 1)) (Polynomial ℂ), Q' ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 f u) (evalU Q' (u : ℂ)) = 0 := by
  let c_aff : Fin (r + 1) → Fin (r + 1) → Polynomial ℂ := fun k i =>
    Polynomial.C (k.1.choose i.1 : ℂ) * iteratedDerivPoly (k.1 - i.1) a
  let Φ : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := fun k =>
    MvPolynomial.C (iteratedDerivPoly k.1 b) +
      ∑ i ∈ Finset.range (k.1 + 1),
        if hi : i < r + 1 then MvPolynomial.C (c_aff k ⟨i, hi⟩) * MvPolynomial.X ⟨i, hi⟩ else 0
  let Q' : MvPolynomial (Fin (r + 1)) (Polynomial ℂ) := MvPolynomial.aeval Φ Q
  refine ⟨Q', ?_, ?_⟩
  · let ι : Polynomial ℂ →+* RatFunc ℂ := algebraMap (Polynomial ℂ) (RatFunc ℂ)
    have hι_inj : Function.Injective ι := RatFunc.algebraMap_injective ℂ
    have hι_a : ι a ≠ 0 := (map_ne_zero_iff ι hι_inj).mpr ha
    let Φ_rat : Fin (r + 1) → MvPolynomial (Fin (r + 1)) (RatFunc ℂ) := fun k =>
      MvPolynomial.map ι (Φ k)
    have hΦ_rat : ∀ k : Fin (r + 1),
        Φ_rat k =
          MvPolynomial.C (ι a) * MvPolynomial.X k +
            MvPolynomial.C (ι (iteratedDerivPoly k.1 b)) +
            ∑ i ∈ Finset.range k.1,
              if hi : i < r + 1 then
                MvPolynomial.C (ι (c_aff k ⟨i, hi⟩)) * MvPolynomial.X ⟨i, hi⟩
              else 0 := fun k => by
      dsimp only [Φ_rat, Φ]
      rw [map_add, MvPolynomial.map_C, map_sum, Finset.sum_range_succ,
        dite_eq_left k.isLt, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
      have htop : c_aff k ⟨k.1, k.isLt⟩ = a := by
        dsimp only [c_aff, iteratedDerivPoly]
        simp
      have hhead : (∑ x ∈ Finset.range k.1, MvPolynomial.map ι
          (if hi : x < r + 1 then
            MvPolynomial.C (c_aff k ⟨x, hi⟩) * MvPolynomial.X (⟨x, hi⟩ : Fin (r + 1))
          else 0)) =
          ∑ i ∈ Finset.range k.1,
            if hi : i < r + 1 then
              MvPolynomial.C (ι (c_aff k ⟨i, hi⟩)) * MvPolynomial.X (⟨i, hi⟩ : Fin (r + 1))
            else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · simp [map_mul]
        · simp
      simp only [Fin.eta]
      rw [htop, hhead]
      ring
    have hinj := triangular_aeval_injective (R := RatFunc ℂ)
      (fun _ => ι a) (fun k => ι (iteratedDerivPoly k.1 b)) (fun k i => ι (c_aff k i))
      (fun _ => hι_a) Φ_rat hΦ_rat
    intro hQ'0
    have hmap0 : MvPolynomial.map ι Q' = 0 := by rw [hQ'0, map_zero]
    dsimp only [Q'] at hmap0
    rw [map_aeval_poly_rat] at hmap0
    have hQ_rat0 : MvPolynomial.map ι Q = 0 := hinj (hmap0.trans (map_zero _).symm)
    exact hQ_ne ((MvPolynomial.map_injective (σ := Fin (r + 1)) ι hι_inj)
      (hQ_rat0.trans (map_zero _).symm))
  · filter_upwards [hQ_top, eventually_gt_atTop (0 : ℝ)] with u hu_Q hu_pos
    have hderiv_k : ∀ k : Fin (r + 1),
        iteratedDeriv k.1 G u =
          MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 f u)
            (evalU (Φ k) (u : ℂ)) := fun k => by
      have hev_nhds : G =ᶠ[𝓝 u] fun v : ℝ => f v * a.eval (v : ℂ) + b.eval (v : ℂ) := by
        filter_upwards [isOpen_Ioi.mem_nhds hu_pos] with v hv
        rw [hGf v hv, mul_comm]
      have hcd_f : ContDiffAt ℝ k.1 f u := (hf_cd k.1).contDiffAt (isOpen_Ioi.mem_nhds hu_pos)
      have hcd_a : ContDiffAt ℝ k.1 (fun v : ℝ => a.eval (v : ℂ)) u :=
        poly_ofReal_contDiffAt a k.1 u
      have hcd_b : ContDiffAt ℝ k.1 (fun v : ℝ => b.eval (v : ℂ)) u :=
        poly_ofReal_contDiffAt b k.1 u
      rw [hev_nhds.iteratedDeriv_eq, iteratedDeriv_fun_add (hcd_f.mul hcd_a) hcd_b,
        iteratedDeriv_fun_mul hcd_f hcd_a, iteratedDeriv_poly_ofReal k.1 b u]
      dsimp only [Φ, evalU]
      simp only [map_add, MvPolynomial.map_C, Polynomial.coe_evalRingHom, MvPolynomial.eval_C,
        map_sum, add_comm]
      refine congrArg (_ + ·) (Finset.sum_congr rfl fun i hi => ?_)
      have hi_lt : i < r + 1 :=
        Nat.lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) k.isLt
      simp only [dite_eq_left hi_lt, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
        Polynomial.coe_evalRingHom, MvPolynomial.eval_C, MvPolynomial.eval_X,
        iteratedDeriv_poly_ofReal (k.1 - i) a u]
      dsimp only [c_aff]
      simp only [Polynomial.eval_mul, Polynomial.eval_C]
      ring
    have hev_Q' : MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 f u)
        (evalU Q' (u : ℂ)) =
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.1 G u) (evalU Q (u : ℂ)) := by
      dsimp only [Q', evalU]
      rw [evalU_aeval]
      refine congrArg (fun f => MvPolynomial.eval f _) (funext fun k => ?_)
      simpa [evalU] using (hderiv_k k).symm
    rw [hev_Q', hu_Q]

private lemma scaledRay_sigmaSeries_even_eq (m : ℕ) (hm : 1 ≤ m) {u : ℝ} (hu : 0 < u) :
    scaledRay (sigmaSeries (2 * m)) (Real.log u) =
      (u : ℂ) ^ (2 * m) * f_even m u + (∫ y in Ioi (0 : ℝ), hFun m y) * (u : ℂ) ^ (2 * m) -
        (bernoulli (2 * m) : ℂ) / ((2 * m : ℕ) : ℂ) := by
  have ht_eq : tRay (Real.log u) = (u : ℂ)⁻¹ := by
    unfold tRay
    rw [Real.exp_neg, Real.exp_log hu]
    push_cast; rfl
  have hq_eq : qRay (Real.log u) = Complex.exp (-((u⁻¹ : ℝ) : ℂ)) := by
    unfold qRay
    rw [Real.exp_neg (Real.log u), Real.exp_log hu, Complex.ofReal_exp]
    push_cast; rfl
  have hval := value_sigmaSeries_exp_neg (2 * m) (inv_pos.mpr hu)
  have hterm : ∀ d : ℕ,
      (((d + 1 : ℕ) : ℂ) ^ (2 * m) /
          (Complex.exp (((d + 1 : ℕ) : ℂ) * ((u⁻¹ : ℝ) : ℂ)) - 1)) =
        (u : ℂ) ^ (2 * m) * hFun m ((d + 1 : ℝ) / u) := fun d => by
    have hdu : (d + 1 : ℝ) / u ≠ 0 := div_ne_zero (by positivity) hu.ne'
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    dsimp only [hFun]
    rw [qFun_eq_div_exp_sub_one hdu]
    push_cast
    rw [mul_div_assoc', ← pow_succ ((d + 1 : ℂ) / (u : ℂ)) (2 * m - 1),
      show 2 * m - 1 + 1 = 2 * m by omega, div_pow, mul_div_assoc',
      mul_div_cancel₀ ((d + 1 : ℂ) ^ (2 * m)) (pow_ne_zero (2 * m) huc),
      div_eq_mul_inv (d + 1 : ℂ) (u : ℂ)]
  have hval_sum : value (sigmaSeries (2 * m)) (qRay (Real.log u)) =
      (u : ℂ) ^ (2 * m) * sumScale (hFun m) u := by
    rw [hq_eq, hval]
    simp_rw [hterm]
    exact tsum_mul_left
  have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have hu_inv : (u : ℂ)⁻¹ * (u : ℂ) = 1 := inv_mul_cancel₀ huc
  have hpow : (u : ℂ) ^ (2 * m) * (u : ℂ)⁻¹ ^ (2 * m) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ huc, one_pow]
  dsimp only [scaledRay, f_even]
  rw [ht_eq, hval_sum]
  linear_combination (u : ℂ) ^ (2 * m) * (∫ y in Ioi (0 : ℝ), hFun m y) * hu_inv -
    ((bernoulli (2 * m) : ℂ) / ((2 * m : ℕ) : ℂ)) * hpow

private lemma scaledRay_sigmaSeries_zero_deriv_eq {u : ℝ} (hu : 0 < u) :
    -(u : ℂ) * deriv (scaledRay (sigmaSeries 0)) (Real.log u) = sumScale gFun u := by
  have heq_on : ∀ v : ℝ, 0 < v →
      scaledRay (sigmaSeries 0) (Real.log v) =
        ∑' n : ℕ, ((n + 1 : ℕ) : ℂ)⁻¹ * qFun ((n + 1 : ℝ) / v) := fun v hv => by
    have ht_eq : tRay (Real.log v) = (v : ℂ)⁻¹ := by
      unfold tRay; rw [Real.exp_neg, Real.exp_log hv]; push_cast; rfl
    have hq_eq : qRay (Real.log v) = Complex.exp (-((v⁻¹ : ℝ) : ℂ)) := by
      unfold qRay; rw [Real.exp_neg (Real.log v), Real.exp_log hv, Complex.ofReal_exp]; push_cast; rfl
    have hval := value_sigmaSeries_exp_neg 0 (inv_pos.mpr hv)
    simp only [pow_zero] at hval
    have hterm : ∀ d : ℕ,
        (v : ℂ)⁻¹ * ((1 : ℂ) / (Complex.exp (((d + 1 : ℕ) : ℂ) * ((v⁻¹ : ℝ) : ℂ)) - 1)) =
          ((d + 1 : ℕ) : ℂ)⁻¹ * qFun ((d + 1 : ℝ) / v) := fun d => by
      have hdv : (d + 1 : ℝ) / v ≠ 0 := div_ne_zero (by positivity) hv.ne'
      have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
      have hd0 : ((d + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
      rw [qFun_eq_div_exp_sub_one hdv]
      push_cast
      field_simp [hvc, hd0]
    dsimp only [scaledRay]
    rw [ht_eq, hq_eq, hval, ← tsum_mul_left]
    exact tsum_congr hterm
  let t : Set ℝ := Metric.ball u (u / 2)
  have ht_open : IsOpen t := Metric.isOpen_ball
  have ht_conn : IsPreconnected t := (convex_ball u (u / 2)).isPreconnected
  have hu_mem : u ∈ t := Metric.mem_ball_self (by positivity)
  let g : ℕ → ℝ → ℂ := fun n v => ((n + 1 : ℕ) : ℂ)⁻¹ * qFun ((n + 1 : ℝ) / v)
  let g' : ℕ → ℝ → ℂ := fun n v => -((v : ℂ)⁻¹ ^ 2) * gFun ((n + 1 : ℝ) / v)
  obtain ⟨CG, cG, hCG, hcG, hbdG⟩ := gFun_expDecaySmooth.2 0
  let qG : ℝ := Real.exp (-cG / (3 * u / 2))
  have hqG_lt : qG < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by linarith) (by positivity))
  let w : ℕ → ℝ := fun n => ((u / 2)⁻¹ ^ 2 * CG * qG) * qG ^ n
  have hw_summ : Summable w := (summable_geometric_of_lt_one (Real.exp_pos _).le hqG_lt).mul_left _
  have hg_deriv : ∀ (n : ℕ) (y : ℝ), y ∈ t → HasDerivAt (g n) (g' n y) y := fun n y hy => by
    have hy_dist : |y - u| < u / 2 := by simpa [t, Metric.mem_ball, Real.dist_eq] using hy
    have hy_pos : 0 < y := by linarith [(abs_lt.mp hy_dist).1]
    have harg : HasDerivAt (fun v : ℝ => (n + 1 : ℝ) / v) (-((n + 1 : ℝ) / y ^ 2)) y := by
      have hinv := (hasDerivAt_inv hy_pos.ne').const_mul (n + 1 : ℝ)
      refine hinv.congr_deriv ?_
      ring
    have hq' := (qFun_expDecaySmooth.differentiable ((n + 1 : ℝ) / y)).hasDerivAt.scomp y harg
    have hmul := hq'.const_mul (((n + 1 : ℕ) : ℂ)⁻¹)
    refine hmul.congr_deriv ?_
    dsimp only [g', gFun]
    have hyc : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy_pos.ne'
    have hd0 : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    rw [Complex.real_smul]
    push_cast
    field_simp [hyc, hd0]
  have hg_bound : ∀ (n : ℕ) (y : ℝ), y ∈ t → ‖g' n y‖ ≤ w n := fun n y hy => by
    have hy_dist : |y - u| < u / 2 := by simpa [t, Metric.mem_ball, Real.dist_eq] using hy
    have hy_lo : u / 2 < y := by linarith [(abs_lt.mp hy_dist).1]
    have hy_hi : y < 3 * u / 2 := by linarith [(abs_lt.mp hy_dist).2]
    have hy_pos : 0 < y := by linarith
    dsimp only [g', w]
    rw [norm_mul, norm_neg, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy_pos]
    have hinv_le : y⁻¹ ^ 2 ≤ (u / 2)⁻¹ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (inv_anti₀ (by positivity) hy_lo.le) _
    have hG_bd := hbdG ((n + 1 : ℝ) / y) (by positivity)
    simp only [iteratedDeriv_zero] at hG_bd
    have hexp_le : Real.exp (-cG * ((n + 1 : ℝ) / y)) ≤ qG * qG ^ n := by
      have hdiv : (n + 1 : ℝ) / (3 * u / 2) ≤ (n + 1 : ℝ) / y :=
        div_le_div_of_nonneg_left (by positivity) hy_pos hy_hi.le
      have hexp1 : Real.exp (-cG * ((n + 1 : ℝ) / y)) ≤
          Real.exp (-cG * ((n + 1 : ℝ) / (3 * u / 2))) :=
        Real.exp_le_exp.mpr (by nlinarith)
      refine hexp1.trans_eq ?_
      dsimp only [qG]
      calc Real.exp (-cG * ((n + 1 : ℝ) / (3 * u / 2)))
          = Real.exp (-cG / (3 * u / 2)) * Real.exp ((n : ℝ) * (-cG / (3 * u / 2))) := by
              rw [← Real.exp_add]; congr 1; ring
        _ = _ := by rw [Real.exp_nat_mul]
    calc y⁻¹ ^ 2 * ‖gFun ((n + 1 : ℝ) / y)‖
        ≤ (u / 2)⁻¹ ^ 2 * (CG * Real.exp (-cG * ((n + 1 : ℝ) / y))) :=
          mul_le_mul hinv_le hG_bd (norm_nonneg _) (by positivity)
      _ ≤ (u / 2)⁻¹ ^ 2 * (CG * (qG * qG ^ n)) := by gcongr
      _ = ((u / 2)⁻¹ ^ 2 * CG * qG) * qG ^ n := by ring
  have hg0 : Summable (fun n : ℕ => g n u) := by
    refine (summable_sumScale qFun_expDecaySmooth hu).norm.of_norm_bounded fun n => ?_
    dsimp only [g]
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hinv_le : (((n + 1 : ℕ) : ℝ)⁻¹) ≤ 1 := by
      refine inv_le_one_of_one_le₀ ?_
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    simpa using mul_le_mul_of_nonneg_right hinv_le (norm_nonneg (qFun ((n + 1 : ℝ) / u)))
  have htsum := hasDerivAt_tsum_of_isPreconnected hw_summ ht_open ht_conn hg_deriv hg_bound hu_mem hg0 hu_mem
  have heq_fn : (fun v : ℝ => ∑' n : ℕ, g n v) =ᶠ[𝓝 u]
      fun v : ℝ => scaledRay (sigmaSeries 0) (Real.log v) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact (heq_on v hv).symm
  have h_sum_deriv : HasDerivAt (fun v : ℝ => scaledRay (sigmaSeries 0) (Real.log v))
      (-((u : ℂ)⁻¹ ^ 2) * sumScale gFun u) u := by
    have htsum' := htsum.congr_of_eventuallyEq heq_fn.symm
    refine htsum'.congr_deriv ?_
    dsimp only [g', sumScale]
    exact tsum_mul_left
  have h_chain : HasDerivAt (fun v : ℝ => scaledRay (sigmaSeries 0) (Real.log v))
      (deriv (scaledRay (sigmaSeries 0)) (Real.log u) * (u : ℂ)⁻¹) u := by
    have hsr := (scaledRay_analytic (sigmaSeries_polyBound 0).to_diskCoeffBound (Real.log u)).differentiableAt.hasDerivAt
    have hs := hsr.scomp u (Real.hasDerivAt_log hu.ne')
    refine hs.congr_deriv ?_
    rw [Complex.real_smul, mul_comm]
    push_cast; rfl
  have huniq := h_chain.unique h_sum_deriv
  have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  calc -(u : ℂ) * deriv (scaledRay (sigmaSeries 0)) (Real.log u)
      = -((u : ℂ) ^ 2) * (deriv (scaledRay (sigmaSeries 0)) (Real.log u) * (u : ℂ)⁻¹) := by
          field_simp [huc]
    _ = -((u : ℂ) ^ 2) * (-((u : ℂ)⁻¹ ^ 2) * sumScale gFun u) := by rw [huniq]
    _ = sumScale gFun u := by field_simp [huc]

/-! ### 5D. Unconditional Tier-1 Theorems (`L₀`, `L_{2m}`, MacMahon `M`) -/

private lemma sigmaSeries_even_no_autonomous_ode (m : ℕ) {J : ℕ}
    (P : MvPolynomial (Fin J) ℂ) (hP_ne : P ≠ 0)
    (hP_zero : ∀ᶠ y : ℝ in atTop,
      MvPolynomial.eval (fun j : Fin J => iteratedDeriv j.1 (scaledRay (sigmaSeries (2 * m))) y) P = 0) :
    False := by
  have hσ_an : ∀ (k : ℕ) (y : ℝ), AnalyticAt ℝ (scaledRay (sigmaSeries k)) y := fun k y =>
    scaledRay_analytic (sigmaSeries_polyBound k).to_diskCoeffBound y
  cases m with
  | zero =>
    obtain ⟨J', P', hP'_ne, hP'_zero⟩ := autonomous_ode_deriv (hσ_an 0) P hP_ne hP_zero
    cases J' with
    | zero =>
      have hc := mvPolynomial_finZero_eq_C P'
      obtain ⟨y, hy⟩ := hP'_zero.exists
      rw [hc, MvPolynomial.eval_C] at hy
      exact hP'_ne (hc.trans (by rw [hy, map_zero]))
    | succ r =>
      obtain ⟨Q, hQ_ne, hQ_zero⟩ :=
        autonomous_log_to_poly_ode (fun y => (hσ_an 0 y).deriv) P' hP'_ne hP'_zero
      let G : ℝ → ℂ := fun u => deriv (scaledRay (sigmaSeries 0)) (Real.log u)
      let H : ℝ → ℂ := fun u => -f₀ u + (u : ℂ) - 1 / 4
      have hGH : ∀ u : ℝ, 0 < u → G u = H u * (u : ℂ)⁻¹ := fun u hu => by
        have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
        have hd := scaledRay_sigmaSeries_zero_deriv_eq hu
        have heqH : H u = -sumScale gFun u := by
          dsimp only [H, f₀]
          ring
        have hmul : -(-(u : ℂ) * deriv (scaledRay (sigmaSeries 0)) (Real.log u)) * (u : ℂ)⁻¹ =
            deriv (scaledRay (sigmaSeries 0)) (Real.log u) * ((u : ℂ) * (u : ℂ)⁻¹) := by ring
        dsimp only [G]
        rw [heqH, ← hd, hmul, mul_inv_cancel₀ huc, mul_one]
      have hf₀_cd : ∀ n : ℕ, ContDiffOn ℝ n f₀ (Ioi (0 : ℝ)) := fun n => by
        have h_u : ContDiffOn ℝ n (fun u : ℝ => (u : ℂ)) (Ioi (0 : ℝ)) :=
          Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top
        exact ((sumScale_contDiffOn gFun_expDecaySmooth n).add h_u).sub contDiffOn_const
      have hH_cd : ∀ n : ℕ, ContDiffOn ℝ n H (Ioi (0 : ℝ)) := fun n => by
        have h_u : ContDiffOn ℝ n (fun u : ℝ => (u : ℂ)) (Ioi (0 : ℝ)) :=
          Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top
        exact ((hf₀_cd n).neg.add h_u).sub contDiffOn_const
      obtain ⟨Q_hom, hQhom_ne, hQhom_zero⟩ :=
        homogenize_inv_mul_ode hGH hH_cd Q hQ_ne hQ_zero
      let a0 : Polynomial ℂ := -1
      let b0 : Polynomial ℂ := Polynomial.X - Polynomial.C (1 / 4 : ℂ)
      have ha0 : a0 ≠ 0 := by simp [a0]
      have hHf : ∀ u : ℝ, 0 < u → H u = a0.eval (u : ℂ) * f₀ u + b0.eval (u : ℂ) := fun u _ => by
        dsimp only [H, a0, b0]
        simp only [Polynomial.eval_neg, Polynomial.eval_one, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        ring
      obtain ⟨Q', hQ'_ne, hQ'_zero⟩ :=
        poly_ode_of_mul_poly_add a0 b0 ha0 hHf hf₀_cd Q_hom hQhom_ne hQhom_zero
      exact hQ'_ne (no_nonautonomous_ade_of_higher_order_borel G₀_borelData f₀_hasAsympExp Q' hQ'_zero)
  | succ m' =>
    have hm : 1 ≤ m' + 1 := by omega
    cases J with
    | zero =>
      have hc := mvPolynomial_finZero_eq_C P
      obtain ⟨y, hy⟩ := hP_zero.exists
      rw [hc, MvPolynomial.eval_C] at hy
      exact hP_ne (hc.trans (by rw [hy, map_zero]))
    | succ r =>
      obtain ⟨Q, hQ_ne, hQ_zero⟩ :=
        autonomous_log_to_poly_ode (hσ_an (2 * (m' + 1))) P hP_ne hP_zero
      let G : ℝ → ℂ := fun u => scaledRay (sigmaSeries (2 * (m' + 1))) (Real.log u)
      let a_m : Polynomial ℂ := Polynomial.X ^ (2 * (m' + 1))
      let b_m : Polynomial ℂ :=
        Polynomial.C (∫ y in Ioi (0 : ℝ), hFun (m' + 1) y) * Polynomial.X ^ (2 * (m' + 1)) -
          Polynomial.C ((bernoulli (2 * (m' + 1)) : ℂ) / ((2 * (m' + 1) : ℕ) : ℂ))
      have ha_m : a_m ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
      have hGf : ∀ u : ℝ, 0 < u →
          G u = a_m.eval (u : ℂ) * f_even (m' + 1) u + b_m.eval (u : ℂ) := fun u hu => by
        dsimp only [G, a_m, b_m]
        rw [scaledRay_sigmaSeries_even_eq (m' + 1) hm hu]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
          Polynomial.eval_X]
        ring
      have hfeven_cd : ∀ n : ℕ, ContDiffOn ℝ n (f_even (m' + 1)) (Ioi (0 : ℝ)) := fun n => by
        have hinv1_on : ContDiffOn ℝ n (fun v : ℝ => (v : ℂ)⁻¹) (Ioi (0 : ℝ)) :=
          (Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).inv fun v hv =>
            Complex.ofReal_ne_zero.mpr (ne_of_gt hv)
        have hg_on : ContDiffOn ℝ n
            (fun u => sumScale (hFun (m' + 1)) u - (u : ℂ) * (∫ y in Ioi (0 : ℝ), hFun (m' + 1) y))
            (Ioi (0 : ℝ)) :=
          (sumScale_contDiffOn (hFun_expDecaySmooth (m' + 1)) n).sub
            ((Complex.ofRealCLM.contDiff.contDiffOn.of_le le_top).mul contDiffOn_const)
        exact (hinv1_on.mul hg_on).add (contDiffOn_const.mul (hinv1_on.pow (2 * (m' + 1))))
      obtain ⟨Q', hQ'_ne, hQ'_zero⟩ :=
        poly_ode_of_mul_poly_add a_m b_m ha_m hGf hfeven_cd Q hQ_ne hQ_zero
      exact hQ'_ne (no_nonautonomous_ade_of_higher_order_borel (K_even_borelData (m' + 1) hm)
        (f_even_hasAsympExp (m' + 1) hm) Q' hQ'_zero)

/-- **Unconditional Chowla–Chowla (1984, Part I) Differential Transcendence**:
For every `m : ℕ`, the even-power divisor-sum generating series
`L_{2m}(q) = ∑_{n ≥ 1} σ_{2m}(n) q^n` is algebraically differentially transcendental over `ℂ(q)`. -/
theorem sigmaEvenSeries_algebraicIndependent (m : ℕ) :
    AlgebraicIndependent ℂ (seriesCoordinates (sigmaSeries (2 * m))) := by
  by_contra hdep
  obtain ⟨J, P, hP_ne, hP_zero⟩ :=
    autonomous_transfer_disk (sigmaSeries_polyBound (2 * m)).to_diskCoeffBound hdep
  exact sigmaSeries_even_no_autonomous_ode m P hP_ne hP_zero

/-- **Unconditional Differential Transcendence of the Classical Lambert Divisor Series**:
`L₀(q) = ∑_{n ≥ 1} d(n) q^n` (Chowla–Chowla 1984, `a = 0`) satisfies no nonzero algebraic
differential equation over `ℂ(q)`. -/
theorem divisorSeries_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates divisorSeries) := by
  rw [← sigmaSeries_zero]
  exact sigmaEvenSeries_algebraicIndependent 0

/-- **Unconditional Differential Transcendence of MacMahon's Plane Partition Generating Series**:
`M(q) = ∏_{n ≥ 1} (1 - q^n)^{-n}` satisfies no nonzero algebraic differential equation over `ℂ(q)`. -/
theorem macmahonSeries_algebraicIndependent :
    AlgebraicIndependent ℂ (seriesCoordinates macmahonSeries) := by
  by_contra hdep
  obtain ⟨J, R, hR_ne, hR_zero⟩ := autonomous_transfer_log_deriv
    macmahonSeries_diskBound (sigmaSeries_polyBound 2).to_diskCoeffBound
    macmahonSeries_ode macmahonSeries_qRay_ne_zero hdep
  exact sigmaSeries_even_no_autonomous_ode 1 R hR_ne hR_zero

end
end PakPrimes.DivisorAndMacMahon
