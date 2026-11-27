module

public import PakStokes.AllD.TrackedWaves
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Order.Prod.Lex.Basic
import all PakStokes.AllD.TrackedWaves
import all PakStokes.AllD.AllDFormalTransfer
import all PakStokes.AllD.ExtremeRayProjection
import all PakStokes.AllD.UniversalThimble
import all PakStokes.AllD.BesicovitchCore
import all PakStokes.RayAlgebra
import all PakStokes.WaveProducts
import all PakStokes.PhysicalPhases
import all PakStokes.PhysicalExpression

/-! # Master All-`d` Marked-Wave Stokes Theorem (`d ≥ 3`)

Connects the unconditional algebraic & geometric engines (`BesicovitchCore`,
`UniversalThimble`, `ExtremeRayProjection`, `AllDFormalTransfer`) with the
extreme-ray marked-wave engine (`TrackedWaves`) to establish:

1. `theta_d_dilations_diff_indep`: For EVERY `d ≥ 3` (odd and even, zero tilt)
   and ANY finite family of distinct positive integers `a : Fin s → ℕ+`, given
   `P : AllDStokesProfile d hd`, the same-degree dilations
   `{Θ_d(q^{a_1}), …, Θ_d(q^{a_s})}` are jointly differentially independent over `ℂ(q)`.
2. `theta_d_dfree_dilations_diff_indep`: Explicit specialization to distinct
   `d`-th-power-free positive integers.
3. `theta_d_marked_wave_non_ade`: For every `d ≥ 3`, given `AllDStokesProfile d hd`,
   `Θ_d(q) = ∑_{n ≥ 0} q^{n^d}` satisfies NO nontrivial ADE over `ℂ(q)`.
4. `theta_d_waring_power_non_ade`: For every `d ≥ 3` and every `k ≥ 1`, given
   `AllDStokesProfile d hd`, the Waring power `Θ_d(q)^k` satisfies NO nontrivial ADE
   over `ℂ(q)`.
5. Concrete unconditional `d = 3` instantiations (`theta_3_non_ade_via_allD`,
   `theta_3_waring_power_non_ade`, `theta_3_dilations_diff_indep`) via
   `stokesProfileThree`, proving non-vacuity and extending the kernel-checked `d = 3`
   library to Waring powers and arbitrary same-degree dilations with ZERO hypotheses. -/
public section
namespace CubicTheta.AllD
open Complex Filter Set
open scoped Topology Matrix
noncomputable section

private theorem coeff_restrictVars {R σ ι : Type*} [CommRing R] [DecidableEq σ]
    (marks : ι → σ) (hinj : Function.Injective marks)
    (f : MvPowerSeries σ R) (m : ι →₀ ℕ) :
    MvPowerSeries.coeff m (restrictVars marks hinj f) =
      MvPowerSeries.coeff (m.mapDomain marks) f := rfl

private theorem rayCoeff_expansion_value (a : Physical.RayCoefficient) (x : ℝ) :
    a.expansion.value x = a.value x := by
  unfold WaveExpansion.value WaveExpansion.term Physical.RayCoefficient.expansion
  simp

private theorem tendsto_finset_sum' {ι α : Type*} {l : Filter α} (S : Finset ι)
    (f : ι → α → ℂ) (L : ι → ℂ) (hf : ∀ i ∈ S, Tendsto (f i) l (𝓝 (L i))) :
    Tendsto (fun x ↦ ∑ i ∈ S, f i x) l (𝓝 (∑ i ∈ S, L i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a S)).add
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

private theorem tendsto_finset_prod' {ι α : Type*} {l : Filter α} (S : Finset ι)
    (f : ι → α → ℂ) (L : ι → ℂ) (hf : ∀ i ∈ S, Tendsto (f i) l (𝓝 (L i))) :
    Tendsto (fun x ↦ ∏ i ∈ S, f i x) l (𝓝 (∏ i ∈ S, L i)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using tendsto_const_nhds
  | @insert a S ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self a S)).mul
      (ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))

/-! ### 1. Polynomial-in-`q` Algebra on `RayGerm` and `Option` Re-grouping -/

private def optionToPolyMv (ι : Type*) :
    MvPolynomial (Option ι) ℂ →ₐ[ℂ] MvPolynomial ι (Polynomial ℂ) :=
  MvPolynomial.aeval fun
    | none => MvPolynomial.C Polynomial.X
    | some x => MvPolynomial.X x

private def polyMvToOption (ι : Type*) :
    MvPolynomial ι (Polynomial ℂ) →+* MvPolynomial (Option ι) ℂ :=
  MvPolynomial.eval₂Hom (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none))
    (fun x ↦ MvPolynomial.X (some x))

private theorem polyMvToOption_optionToPolyMv (ι : Type*) (Q : MvPolynomial (Option ι) ℂ) :
    polyMvToOption ι (optionToPolyMv ι Q) = Q := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp [optionToPolyMv, polyMvToOption]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p u hp =>
    rw [map_mul, map_mul, hp]
    cases u <;> simp [optionToPolyMv, polyMvToOption]

private theorem optionToPolyMv_injective (ι : Type*) :
    Function.Injective (optionToPolyMv ι) :=
  Function.LeftInverse.injective (polyMvToOption_optionToPolyMv ι)

private theorem eval₂_optionToPolyMv {ι : Type*} (q : ℂ) (f : ι → ℂ)
    (Q : MvPolynomial (Option ι) ℂ) :
    MvPolynomial.eval₂ (Polynomial.evalRingHom q) f (optionToPolyMv ι Q) =
      MvPolynomial.eval (Option.elim' q f) Q := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    simp [optionToPolyMv]
  | add p r hp hr =>
    rw [map_add, MvPolynomial.eval₂_add, map_add, hp, hr]
  | mul_X p u hp =>
    rw [map_mul, MvPolynomial.eval₂_mul, map_mul, hp]
    cases u <;> simp [optionToPolyMv]

/-- Evaluation of `R ∈ ℂ[X]` along the real nome ray `qRayD d p = exp(-p^{-(d-1)})` as a germ. -/
private def polyToGerm (d : ℕ) : Polynomial ℂ →+* RayGerm :=
  (Germ.coeRingHom (atTop : Filter ℝ)).comp
    { toFun := fun R p ↦ R.eval (qRayD d p)
      map_one' := by funext p; simp
      map_mul' := fun R S ↦ by funext p; simp
      map_zero' := by funext p; simp
      map_add' := fun R S ↦ by funext p; simp }

private theorem polyToGerm_injective {d : ℕ} (hd : 3 ≤ d) :
    Function.Injective (polyToGerm d) := by
  intro R S hRS
  suffices h0 : R - S = 0 from sub_eq_zero.mp h0
  have hev : ∀ᶠ p : ℝ in atTop, (R - S).eval (qRayD d p) = 0 := by
    have hsub : polyToGerm d (R - S) = 0 := by rw [map_sub, hRS, sub_self]
    exact Germ.coe_eq.mp hsub
  obtain ⟨L, hL⟩ := eventually_atTop.1 hev
  let L₀ : ℝ := max L 1
  have hq_inj : Set.InjOn (qRayD d) (Ici L₀) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one ((le_max_right L 1).trans hx)
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one ((le_max_right L 1).trans hy)
    have hreal : Real.exp (-(1 / x ^ (d - 1))) = Real.exp (-(1 / y ^ (d - 1))) :=
      Complex.ofReal_injective hxy
    have hpow : x ^ (d - 1) = y ^ (d - 1) := by
      have h1 := neg_inj.mp (Real.exp_injective hreal)
      have h2 := inv_injective (by simpa only [one_div] using h1)
      exact h2
    have hne : d - 1 ≠ 0 := by omega
    exact (pow_left_inj₀ hx0.le hy0.le hne).mp hpow
  have hinf : (qRayD d '' Ici L₀).Infinite :=
    (Ici_infinite L₀).image hq_inj
  by_contra hne0
  obtain ⟨z, ⟨p, hp, rfl⟩, hnot⟩ := hinf.exists_notMem_finset (R - S).roots.toFinset
  have hroot : (R - S).eval (qRayD d p) = 0 := hL p ((le_max_left L 1).trans hp)
  have hmem : qRayD d p ∈ (R - S).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hne0]
    exact hroot
  exact hnot hmem

private def polyRayCoeff (d : ℕ) (R : Polynomial ℂ) : Physical.RayCoefficient where
  value := fun p ↦ R.eval (qRayD d p)
  budget := ∑ k ∈ R.support, ‖R.coeff k‖
  loss := 0
  nonneg := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  bound := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
    rw [pow_zero, mul_one, Polynomial.eval_eq_sum]
    calc ‖R.sum fun k c ↦ c * qRayD d p ^ k‖
        ≤ ∑ k ∈ R.support, ‖R.coeff k * qRayD d p ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ R.support, ‖R.coeff k‖ := by
          apply Finset.sum_le_sum; intro k _
          rw [norm_mul, norm_pow]
          have hq : ‖qRayD d p‖ ≤ 1 := (qRayD_disk hp).le
          exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hq)

private theorem polyRayCoeff_powerClass {d : ℕ} (hd : 3 ≤ d) (R : Polynomial ℂ) :
    PowerClass 0 (polyRayCoeff d R).value := by
  have hq : PowerClass 0 (qRayD d) := by
    have h := exp_inv_pow_powerClass (r := d - 1) (by omega) (-1)
    refine h.congr ?_
    filter_upwards with p
    simp [qRayD, neg_div]
  have hpow : ∀ n : ℕ, PowerClass 0 (fun p ↦ qRayD d p ^ n) := by
    intro n
    induction n with
    | zero => simpa using PowerClass.const (1 : ℂ)
    | succ n ih =>
      have hm := ih.mul hq
      rw [zero_add] at hm
      simpa only [pow_succ] using hm
  induction R using Polynomial.induction_on' with
  | add P Q hP hQ =>
    refine (hP.add hQ).congr ?_
    filter_upwards with p
    simp [polyRayCoeff]
  | monomial n c =>
    have hm := (PowerClass.const c).mul (hpow n)
    rw [zero_add] at hm
    refine hm.congr ?_
    filter_upwards with p
    simp [polyRayCoeff, Polynomial.eval_monomial]

/-! ### 2. `poleD` Derivatives and Background + Pole `RayCoefficient` -/

private def poleDerivConst (d : ℕ) : ℕ → ℂ
  | 0 => 1
  | ℓ + 1 => poleDerivConst d ℓ * ((((d - 1 : ℕ) : ℝ) / (d : ℝ) - (ℓ : ℝ) : ℝ) : ℂ)

private theorem poleD_iteratedDeriv (d : ℕ) (ℓ : ℕ) {p : ℝ} (hp : 0 < p) :
    iteratedDeriv ℓ (poleD d) p =
      poleDerivConst d ℓ * ((p ^ ((((d - 1 : ℕ) : ℝ) / (d : ℝ)) - (ℓ : ℝ)) : ℝ) : ℂ) := by
  induction ℓ generalizing p with
  | zero =>
    simp [poleD, poleDerivConst]
  | succ ℓ ih =>
    rw [iteratedDeriv_succ]
    have hnear : iteratedDeriv ℓ (poleD d) =ᶠ[𝓝 p]
        fun x ↦ poleDerivConst d ℓ * ((x ^ ((((d - 1 : ℕ) : ℝ) / (d : ℝ)) - (ℓ : ℝ)) : ℝ) : ℂ) :=
      (lt_mem_nhds hp).mono fun x hx ↦ ih hx
    rw [hnear.deriv_eq]
    have hpow := (Real.hasDerivAt_rpow_const (x := p)
      (p := (((d - 1 : ℕ) : ℝ) / (d : ℝ)) - (ℓ : ℝ)) (Or.inl hp.ne')).ofReal_comp
    have hmul := hpow.const_mul (poleDerivConst d ℓ)
    rw [hmul.deriv]
    simp only [poleDerivConst, Complex.ofReal_mul, Nat.cast_add, Nat.cast_one]
    rw [show (((d - 1 : ℕ) : ℝ) / (d : ℝ) - (ℓ : ℝ) - 1) =
        (((d - 1 : ℕ) : ℝ) / (d : ℝ) - ((ℓ : ℝ) + 1)) by ring]
    ring

private theorem poleD_iteratedDeriv_powerClass (d : ℕ) (ℓ : ℕ) :
    PowerClass (((d - 1 : ℕ) : ℝ) / (d : ℝ)) (iteratedDeriv ℓ (poleD d)) := by
  refine ⟨-(ℓ : ℤ), ?_⟩
  have h1 := (AtPower.const (poleDerivConst d ℓ)).shift ((((d - 1 : ℕ) : ℝ) / (d : ℝ)) - (ℓ : ℝ))
  have hexp : (((d - 1 : ℕ) : ℝ) / (d : ℝ)) - (ℓ : ℝ) + 0 =
      (((d - 1 : ℕ) : ℝ) / (d : ℝ)) + ((-(ℓ : ℤ) : ℤ) : ℝ) := by
    push_cast; ring
  rw [hexp] at h1
  refine h1.congr ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
  rw [poleD_iteratedDeriv d ℓ hp, Complex.real_smul, mul_comm]

private theorem poleD_iteratedDeriv_bound {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    ∀ᶠ p : ℝ in atTop, ‖iteratedDeriv ℓ (poleD d) p‖ ≤ ‖poleDerivConst d ℓ‖ * p ^ 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with p hp
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  rw [poleD_iteratedDeriv d ℓ hp0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hp0.le _), pow_one]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hexp : (((d - 1 : ℕ) : ℝ) / (d : ℝ)) - (ℓ : ℝ) ≤ 1 := by
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hlt : ((d - 1 : ℕ) : ℝ) / (d : ℝ) ≤ 1 := by
      rw [div_le_one hdpos]; exact_mod_cast (by omega : d - 1 ≤ d)
    have hℓ : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg ℓ
    linarith
  simpa using Real.rpow_le_rpow_of_exponent_le hp hexp

private theorem poleD_finiteParities {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    FiniteParities (2 * d) (iteratedDeriv ℓ (poleD d)) := by
  let r : Fin (2 * d) := ⟨2 * (d - 1), by omega⟩
  have hr : ((r : ℕ) : ℝ) / ((2 * d : ℕ) : ℝ) = ((d - 1 : ℕ) : ℝ) / (d : ℝ) := by
    change ((2 * (d - 1) : ℕ) : ℝ) / ((2 * d : ℕ) : ℝ) = _
    push_cast
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    rw [mul_div_mul_left _ _ h2]
  exact FiniteParities.of_class r (hr ▸ poleD_iteratedDeriv_powerClass d ℓ)

private def dilatedScale (d m : ℕ) : ℝ := (m : ℝ) ^ (-(1 / ((d - 1 : ℕ) : ℝ)))

private theorem dilatedScale_pos {d m : ℕ} (hm : 0 < m) : 0 < dilatedScale d m :=
  Real.rpow_pos_of_pos (by exact_mod_cast hm) _

private theorem qRayD_dilatedScale {d : ℕ} (hd : 3 ≤ d) (m : ℕ+) {p : ℝ} (_hp : 0 < p) :
    qRayD d (dilatedScale d m.val * p) = (qRayD d p) ^ m.val := by
  have hm : (0 : ℝ) < (m.val : ℝ) := by exact_mod_cast m.property
  have hr : ((d - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : d - 1 ≠ 0)
  have hσ_pow : (dilatedScale d m.val) ^ (d - 1) = (m.val : ℝ)⁻¹ := by
    unfold dilatedScale
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le, neg_mul, one_div, inv_mul_cancel₀ hr,
        Real.rpow_neg_one]
  unfold qRayD
  rw [← Complex.ofReal_pow, ← Real.exp_nat_mul]
  congr 2
  rw [mul_pow, hσ_pow, div_mul_eq_div_div, div_inv_eq_mul]
  ring

private theorem dilated_value_regular {d : ℕ} (hd : 3 ≤ d) (m : ℕ+) {p : ℝ} (hp : 0 < p) :
    psValue (thetaDDilated d m.val) (qRayD d p) =
      regularThetaD d (dilatedScale d m.val * p) +
        (1 / 2 + ((Real.Gamma (1 + 1 / (d : ℝ)) *
          (dilatedScale d m.val) ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) : ℝ) : ℂ) * poleD d p) := by
  have hσ : 0 < dilatedScale d m.val := dilatedScale_pos m.property
  have hval : psValue (thetaDDilated d m.val) (qRayD d p) =
      psValue (thetaD d) (qRayD d (dilatedScale d m.val * p)) := by
    rw [dilated_value_eq (d := d) (a := m.val) (by omega) m.property (qRayD d p),
        qRayD_dilatedScale hd m hp, thetaD, dilated_value_eq (d := d) (a := 1) (by omega) le_rfl]
    apply tsum_congr; intro n
    rw [one_mul, ← pow_mul, mul_comm]
  have hreg := regularThetaD_at hd (mul_pos hσ hp)
  change regularThetaD d (dilatedScale d m.val * p) =
      psValue (thetaD d) (qRayD d (dilatedScale d m.val * p)) -
        (1 / 2 + ((Real.Gamma (1 + 1 / (d : ℝ)) : ℝ) : ℂ) * poleD d (dilatedScale d m.val * p)) at hreg
  have hpole : poleD d (dilatedScale d m.val * p) =
      (((dilatedScale d m.val) ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) : ℝ) : ℂ) * poleD d p := by
    unfold poleD
    rw [Real.mul_rpow hσ.le hp.le, Complex.ofReal_mul]
  rw [hval, eq_add_of_sub_eq' hreg.symm, hpole, Complex.ofReal_mul]
  ring

private theorem dilated_iteratedDeriv_split {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    (m : ℕ+) (ℓ : ℕ) :
    let σ := dilatedScale d m.val
    let hσ := dilatedScale_pos (d := d) m.property
    let γ : ℂ := ((Real.Gamma (1 + 1 / (d : ℝ)) * σ ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) : ℝ) : ℂ)
    iteratedDeriv ℓ (fun p ↦ psValue (thetaDDilated d m.val) (qRayD d p)) =ᶠ[atTop]
      fun p ↦ (((σ ^ ℓ : ℝ) : ℂ) * iteratedDeriv ℓ P.bg (σ * p) +
          ((if ℓ = 0 then (1 / 2 : ℂ) else 0) + γ * iteratedDeriv ℓ (poleD d) p)) +
        (P.scaledWaves σ hσ ℓ).value p := by
  intro σ hσ γ
  have hconst_pole (k : ℕ) :
      iteratedDeriv k (fun p ↦ (1 / 2 : ℂ) + γ * poleD d p) =ᶠ[atTop]
        fun p ↦ (if k = 0 then (1 / 2 : ℂ) else 0) + γ * iteratedDeriv k (poleD d) p := by
    induction k with
    | zero => filter_upwards with p; simp
    | succ k ih =>
      obtain ⟨L, hL⟩ := eventually_atTop.1 ih
      filter_upwards [eventually_gt_atTop (max L 0)] with p hp
      have hLp : L < p := lt_of_le_of_lt (le_max_left L 0) hp
      have hp0 : 0 < p := lt_of_le_of_lt (le_max_right L 0) hp
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      have hnear : iteratedDeriv k (fun x ↦ (1 / 2 : ℂ) + γ * poleD d x) =ᶠ[𝓝 p]
          fun x ↦ (if k = 0 then (1 / 2 : ℂ) else 0) + γ * iteratedDeriv k (poleD d) x :=
        (lt_mem_nhds hLp).mono fun x hx ↦ hL x hx.le
      rw [hnear.deriv_eq]
      have hpd : DifferentiableAt ℝ (iteratedDeriv k (poleD d)) p := by
        have han : ∀ t, AnalyticAt ℝ (iteratedDeriv t (poleD d)) p := by
          intro t; induction t with
          | zero => exact poleD_analytic hp0
          | succ t iht => rw [iteratedDeriv_succ]; exact iht.deriv
        exact (han k).differentiableAt
      have hd1 : HasDerivAt (fun x ↦ (if k = 0 then (1 / 2 : ℂ) else 0) +
          γ * iteratedDeriv k (poleD d) x) (0 + γ * deriv (iteratedDeriv k (poleD d)) p) p :=
        (hasDerivAt_const p _).add (hpd.hasDerivAt.const_mul γ)
      rw [hd1.deriv]
      simp
  have hsum_deriv (k : ℕ) :
      iteratedDeriv k (fun p ↦ psValue (thetaDDilated d m.val) (qRayD d p)) =ᶠ[atTop]
        fun p ↦ iteratedDeriv k (fun x ↦ regularThetaD d (σ * x)) p +
          iteratedDeriv k (fun x ↦ (1 / 2 : ℂ) + γ * poleD d x) p := by
    induction k with
    | zero =>
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
      exact dilated_value_regular hd m hp
    | succ k ih =>
      obtain ⟨L, hL⟩ := eventually_atTop.1 ih
      filter_upwards [eventually_gt_atTop (max L 0)] with p hp
      have hLp : L < p := lt_of_le_of_lt (le_max_left L 0) hp
      have hp0 : 0 < p := lt_of_le_of_lt (le_max_right L 0) hp
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ]
      have hnear : iteratedDeriv k (fun x ↦ psValue (thetaDDilated d m.val) (qRayD d x)) =ᶠ[𝓝 p]
          fun x ↦ iteratedDeriv k (fun y ↦ regularThetaD d (σ * y)) x +
            iteratedDeriv k (fun y ↦ (1 / 2 : ℂ) + γ * poleD d y) x :=
        (lt_mem_nhds hLp).mono fun x hx ↦ hL x hx.le
      rw [hnear.deriv_eq]
      have hreg_an : ∀ t, AnalyticAt ℝ (iteratedDeriv t (fun y ↦ regularThetaD d (σ * y))) p := by
        intro t; induction t with
        | zero =>
          exact (regularThetaD_analytic hd (mul_pos hσ hp0)).comp
            (analyticAt_const.mul analyticAt_id)
        | succ t iht => rw [iteratedDeriv_succ]; exact iht.deriv
      have hpole_an : ∀ t, AnalyticAt ℝ (iteratedDeriv t (fun y ↦ (1 / 2 : ℂ) + γ * poleD d y)) p := by
        intro t; induction t with
        | zero => exact analyticAt_const.add (analyticAt_const.mul (poleD_analytic hp0))
        | succ t iht => rw [iteratedDeriv_succ]; exact iht.deriv
      have hadd : HasDerivAt
          (fun x ↦ iteratedDeriv k (fun y ↦ regularThetaD d (σ * y)) x +
            iteratedDeriv k (fun y ↦ (1 / 2 : ℂ) + γ * poleD d y) x)
          (deriv (iteratedDeriv k (fun y ↦ regularThetaD d (σ * y))) p +
            deriv (iteratedDeriv k (fun y ↦ (1 / 2 : ℂ) + γ * poleD d y)) p) p :=
        (hreg_an k).differentiableAt.hasDerivAt.add (hpole_an k).differentiableAt.hasDerivAt
      rw [hadd.deriv]
  filter_upwards [hsum_deriv ℓ, P.scaled_regular_derivatives σ hσ ℓ, hconst_pole ℓ] with p hs hr hpole
  rw [hs, hr, hpole]
  ring

private theorem dilated_qjet_split {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    (m : ℕ+) (j : ℕ) :
    let σ := dilatedScale d m.val
    let hσ := dilatedScale_pos (d := d) m.property
    let γ : ℂ := ((Real.Gamma (1 + 1 / (d : ℝ)) * σ ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) : ℝ) : ℂ)
    let bgPart (p : ℝ) : ℂ := ∑ ℓ ∈ Finset.range (j + 1), qPolyCoeff d j ℓ p *
      (((σ ^ ℓ : ℝ) : ℂ) * iteratedDeriv ℓ P.bg (σ * p) +
        ((if ℓ = 0 then (1 / 2 : ℂ) else 0) + γ * iteratedDeriv ℓ (poleD d) p))
    ∀ᶠ p : ℝ in atTop,
      psValue (formalJet (thetaDDilated d m.val) j) (qRayD d p) =
        bgPart p + ∑ ℓ ∈ Finset.range (j + 1),
          qPolyCoeff d j ℓ p * (P.scaledWaves σ hσ ℓ).value p := by
  intro σ hσ γ bgPart
  have hsmooth : ∀ ℓ ≤ j, ∀ᶠ p : ℝ in atTop,
      DifferentiableAt ℝ (iteratedDeriv ℓ (fun x ↦ psValue (thetaDDilated d m.val) (qRayD d x))) p := by
    intro ℓ _
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
    have han : ∀ t, AnalyticAt ℝ (iteratedDeriv t (fun x ↦ psValue (thetaDDilated d m.val) (qRayD d x))) p := by
      intro t; induction t with
      | zero =>
        exact (((dilated_jet_analytic d m.val 0) _ (by simpa using qRayD_disk hp)).restrictScalars
          (𝕜 := ℝ)).comp (qRayD_analytic hp)
      | succ t iht => rw [iteratedDeriv_succ]; exact iht.deriv
    exact (han ℓ).differentiableAt
  have hchain := iterQDeriv_eq_sum hd (fun x ↦ psValue (thetaDDilated d m.val) (qRayD d x)) j hsmooth
  have hall : ∀ᶠ p : ℝ in atTop, ∀ ℓ ∈ Finset.range (j + 1),
      iteratedDeriv ℓ (fun x ↦ psValue (thetaDDilated d m.val) (qRayD d x)) p =
        (((σ ^ ℓ : ℝ) : ℂ) * iteratedDeriv ℓ P.bg (σ * p) +
          ((if ℓ = 0 then (1 / 2 : ℂ) else 0) + γ * iteratedDeriv ℓ (poleD d) p)) +
        (P.scaledWaves σ hσ ℓ).value p :=
    (Filter.eventually_all_finset (Finset.range (j + 1))).mpr
      fun ℓ _ ↦ dilated_iteratedDeriv_split hd P m ℓ
  filter_upwards [eventually_gt_atTop (0 : ℝ), hchain, hall] with p hp hch hl
  rw [dilated_jet_eq_iterQDeriv hd j hp, hch]
  have hsum : ∑ ℓ ∈ Finset.range (j + 1), qPolyCoeff d j ℓ p *
        iteratedDeriv ℓ (fun x ↦ psValue (thetaDDilated d m.val) (qRayD d x)) p =
      ∑ ℓ ∈ Finset.range (j + 1), (qPolyCoeff d j ℓ p *
        (((σ ^ ℓ : ℝ) : ℂ) * iteratedDeriv ℓ P.bg (σ * p) +
          ((if ℓ = 0 then (1 / 2 : ℂ) else 0) + γ * iteratedDeriv ℓ (poleD d) p)) +
        qPolyCoeff d j ℓ p * (P.scaledWaves σ hσ ℓ).value p) := by
    apply Finset.sum_congr rfl; intro ℓ hℓ
    rw [hl ℓ hℓ, mul_add]
  rw [hsum, Finset.sum_add_distrib]

private def qPolyRayCoeff {d : ℕ} (hd : 3 ≤ d) (j ℓ : ℕ) : Physical.RayCoefficient := by
  by_cases hℓ : ℓ ≤ j
  · have hq := qPolyCoeff_QCoeff hd j ℓ hℓ
    have hb := hq.poly_bound
    exact ⟨qPolyCoeff d j ℓ, Classical.choose hb, Classical.choose (Classical.choose_spec hb),
      (Classical.choose_spec (Classical.choose_spec hb)).1,
      (Classical.choose_spec (Classical.choose_spec hb)).2⟩
  · exact ⟨qPolyCoeff d j ℓ, 0, 0, le_rfl,
      Eventually.of_forall fun p ↦ by rw [qPolyCoeff_gt j ℓ (by omega)]; simp⟩

private theorem qPolyRayCoeff_powerClass {d : ℕ} (hd : 3 ≤ d) (j ℓ : ℕ) :
    PowerClass 0 (qPolyRayCoeff hd j ℓ).value := by
  unfold qPolyRayCoeff
  split_ifs with hℓ
  · exact (qPolyCoeff_QCoeff hd j ℓ hℓ).powerClass_zero hd
  · refine (PowerClass.const 0).congr ?_
    filter_upwards with p
    exact (qPolyCoeff_gt j ℓ (by omega) p).symm

private def scaledBgPoleCoeff {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    (m : ℕ+) (ℓ : ℕ) : Physical.RayCoefficient :=
  let σ := dilatedScale d m.val
  let hσ := dilatedScale_pos (d := d) m.property
  let γ : ℂ := ((Real.Gamma (1 + 1 / (d : ℝ)) * σ ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) : ℝ) : ℂ)
  let hbg := P.bg_bound ℓ
  let B := Classical.choose hbg
  let L := Classical.choose (Classical.choose_spec hbg)
  have hB : 0 ≤ B := (Classical.choose_spec (Classical.choose_spec hbg)).1
  have hbg_ev : ∀ᶠ p : ℝ in atTop, ‖iteratedDeriv ℓ P.bg p‖ ≤ B * p ^ L :=
    (Classical.choose_spec (Classical.choose_spec hbg)).2
  { value := fun p ↦ ((σ ^ ℓ : ℝ) : ℂ) * iteratedDeriv ℓ P.bg (σ * p) +
      ((if ℓ = 0 then (1 / 2 : ℂ) else 0) + γ * iteratedDeriv ℓ (poleD d) p)
    budget := σ ^ ℓ * B * σ ^ L + 1 + ‖γ‖ * ‖poleDerivConst d ℓ‖
    loss := max L 1
    nonneg := by
      have hσ0 : 0 < σ := hσ
      positivity
    bound := by
      have hσ0 : 0 < σ := hσ
      have hbg_s := (tendsto_id.const_mul_atTop hσ).eventually hbg_ev
      filter_upwards [eventually_ge_atTop (1 : ℝ), hbg_s, poleD_iteratedDeriv_bound hd ℓ]
        with p hp1 hbp hpole
      simp only [id_eq] at hbp
      have hpL : p ^ L ≤ p ^ (max L 1) := pow_le_pow_right₀ hp1 (le_max_left L 1)
      have hp1m : p ^ 1 ≤ p ^ (max L 1) := pow_le_pow_right₀ hp1 (le_max_right L 1)
      have h1m : (1 : ℝ) ≤ p ^ (max L 1) := one_le_pow₀ hp1
      have hnorm1 : ‖((σ ^ ℓ : ℝ) : ℂ) * iteratedDeriv ℓ P.bg (σ * p)‖ ≤
          (σ ^ ℓ * B * σ ^ L) * p ^ (max L 1) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hσ0 ℓ)]
        calc σ ^ ℓ * ‖iteratedDeriv ℓ P.bg (σ * p)‖
            ≤ σ ^ ℓ * (B * (σ * p) ^ L) := mul_le_mul_of_nonneg_left hbp (pow_nonneg hσ0.le ℓ)
          _ = (σ ^ ℓ * B * σ ^ L) * p ^ L := by rw [mul_pow]; ring
          _ ≤ (σ ^ ℓ * B * σ ^ L) * p ^ (max L 1) := by gcongr
      have hnorm2 : ‖if ℓ = 0 then (1 / 2 : ℂ) else 0‖ ≤ 1 * p ^ (max L 1) := by
        split_ifs
        · rw [one_mul]; norm_num; linarith
        · rw [norm_zero, one_mul]; positivity
      have hnorm3 : ‖γ * iteratedDeriv ℓ (poleD d) p‖ ≤
          (‖γ‖ * ‖poleDerivConst d ℓ‖) * p ^ (max L 1) := by
        rw [norm_mul]
        calc ‖γ‖ * ‖iteratedDeriv ℓ (poleD d) p‖
            ≤ ‖γ‖ * (‖poleDerivConst d ℓ‖ * p ^ 1) := by gcongr
          _ = (‖γ‖ * ‖poleDerivConst d ℓ‖) * p ^ 1 := by ring
          _ ≤ (‖γ‖ * ‖poleDerivConst d ℓ‖) * p ^ (max L 1) := by gcongr
      have htri1 := norm_add_le (((σ ^ ℓ : ℝ) : ℂ) * iteratedDeriv ℓ P.bg (σ * p))
        ((if ℓ = 0 then (1 / 2 : ℂ) else 0) + γ * iteratedDeriv ℓ (poleD d) p)
      have htri2 := norm_add_le (if ℓ = 0 then (1 / 2 : ℂ) else 0) (γ * iteratedDeriv ℓ (poleD d) p)
      linarith }

private theorem scaledBgPole_finiteParities {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    (m : ℕ+) (ℓ : ℕ) :
    FiniteParities (2 * d) (scaledBgPoleCoeff hd P m ℓ).value := by
  have hM : 0 < 2 * d := by omega
  have h1 : FiniteParities (2 * d) (fun p ↦ ((dilatedScale d m.val ^ ℓ : ℝ) : ℂ) *
      iteratedDeriv ℓ P.bg (dilatedScale d m.val * p)) := by
    have hpc := (PowerClass.const ((dilatedScale d m.val ^ ℓ : ℝ) : ℂ)).mul
      (powerClass_scale_arg (P.bg_powerClass ℓ) (dilatedScale_pos (d := d) m.property))
    rw [zero_add] at hpc
    exact FiniteParities.of_zero hM hpc
  have h2 : FiniteParities (2 * d) (fun _ : ℝ ↦ if ℓ = 0 then (1 / 2 : ℂ) else 0) :=
    FiniteParities.of_zero hM (PowerClass.const _)
  have h3 : FiniteParities (2 * d) (fun p ↦ ((Real.Gamma (1 + 1 / (d : ℝ)) *
      (dilatedScale d m.val) ^ (((d - 1 : ℕ) : ℝ) / (d : ℝ)) : ℝ) : ℂ) *
      iteratedDeriv ℓ (poleD d) p) :=
    (FiniteParities.of_zero hM (PowerClass.const _)).mul hM (poleD_finiteParities hd ℓ)
  exact h1.add (h2.add h3)

/-! ### 3. Extreme-Ray Dilation Lattice, Fresh Primes, and Block Dominance -/

/-- Additive extreme-ray frequency map for same-degree dilations with common denominator `A`. -/
private def dilKeyRate (d A : ℕ) : (Core (d - 1) →₀ ℕ) →+ ℂ where
  toFun k := (((readRootKey (d - 1) k / (A : ℝ) : ℝ) : ℂ) *
    ((modeScale d : ℝ) : ℂ)) * principalSaddle d
  map_zero' := by simp
  map_add' k₁ k₂ := by
    simp only [map_add, add_div, Complex.ofReal_add, add_mul]

private theorem dilKeyRate_injective {d A : ℕ} (hd : 3 ≤ d) (hA : 0 < A) :
    Function.Injective (dilKeyRate d A) := by
  intro k₁ k₂ h
  have h1 : (((readRootKey (d - 1) k₁ / (A : ℝ) : ℝ) : ℂ) * ((modeScale d : ℝ) : ℂ)) =
      (((readRootKey (d - 1) k₂ / (A : ℝ) : ℝ) : ℂ) * ((modeScale d : ℝ) : ℂ)) :=
    mul_right_cancel₀ (principalSaddle_ne_zero hd) h
  have h2 : ((readRootKey (d - 1) k₁ / (A : ℝ) : ℝ) : ℂ) =
      ((readRootKey (d - 1) k₂ / (A : ℝ) : ℝ) : ℂ) :=
    mul_right_cancel₀ (by exact_mod_cast (modeScale_pos hd).ne') h1
  have h3 : readRootKey (d - 1) k₁ / (A : ℝ) = readRootKey (d - 1) k₂ / (A : ℝ) :=
    Complex.ofReal_injective h2
  have h4 : readRootKey (d - 1) k₁ = readRootKey (d - 1) k₂ :=
    (div_left_inj₀ (by exact_mod_cast hA.ne')).mp h3
  exact readRootKey_injective (d - 1) (by omega) h4

private theorem rotIm_dilKeyRate {d A : ℕ} (hd : 3 ≤ d) (k : Core (d - 1) →₀ ℕ) :
    rotIm d (dilKeyRate d A k) = 0 := by
  change rotIm d ((((readRootKey (d - 1) k / (A : ℝ) : ℝ) : ℂ) *
    ((modeScale d : ℝ) : ℂ)) * principalSaddle d) = 0
  rw [← Complex.ofReal_mul, rotIm_smul_real, rotIm_principal hd, mul_zero]

private def dilCore {d : ℕ} (hd : 3 ≤ d) (m n : ℕ+) : Core (d - 1) :=
  rFreeCore (d - 1) (by omega) ⟨m.val ^ (d - 2) * n.val, mul_pos (pow_pos m.property _) n.property⟩

private def dilRoot {d : ℕ} (hd : 3 ≤ d) (m n : ℕ+) : ℕ :=
  rFreeRoot (d - 1) (by omega) ⟨m.val ^ (d - 2) * n.val, mul_pos (pow_pos m.property _) n.property⟩

private def dilExp {d : ℕ} (hd : 3 ≤ d) (A : ℕ) (m n : ℕ+) : ℕ :=
  (A / m.val) * n.val * dilRoot hd m n

private def dilModeExp {d : ℕ} (hd : 3 ≤ d) (A : ℕ) (m n : ℕ+) : Core (d - 1) →₀ ℕ :=
  Finsupp.single (dilCore hd m n) (dilExp hd A m n)

private theorem dilExp_pos {d : ℕ} (hd : 3 ≤ d) {A : ℕ} (hA : 0 < A) {m : ℕ+}
    (hdiv : m.val ∣ A) (n : ℕ+) : 0 < dilExp hd A m n := by
  have hq : 0 < A / m.val := Nat.div_pos (Nat.le_of_dvd hA hdiv) m.property
  have hr : 0 < dilRoot hd m n := rFreeRoot_pos (d - 1) (by omega) _
  have hn : 0 < n.val := n.property
  exact mul_pos (mul_pos hq hn) hr

/-- Pure-`ℕ` key identity: `m * e(m, n)^{d-1} * c(m, n) = A^{d-1} * n^d`. -/
private theorem dil_nat_identity {d : ℕ} (hd : 3 ≤ d) {A : ℕ} {m : ℕ+}
    (hdiv : m.val ∣ A) (n : ℕ+) :
    m.val * (dilExp hd A m n) ^ (d - 1) * (dilCore hd m n).val = A ^ (d - 1) * n.val ^ d := by
  have hfac : (dilRoot hd m n) ^ (d - 1) * (dilCore hd m n).val = m.val ^ (d - 2) * n.val :=
    rFreeRoot_pow_mul_core (d - 1) (by omega) _
  have hmul : m.val * (A / m.val) = A := Nat.mul_div_cancel' hdiv
  have hd_sub : 1 + (d - 2) = d - 1 := by omega
  have hd_add : (d - 1) + 1 = d := by omega
  calc m.val * (dilExp hd A m n) ^ (d - 1) * (dilCore hd m n).val
      = m.val * ((A / m.val) ^ (d - 1) * n.val ^ (d - 1) * (dilRoot hd m n) ^ (d - 1)) *
          (dilCore hd m n).val := by
        simp only [dilExp, mul_pow]
    _ = m.val * (A / m.val) ^ (d - 1) * n.val ^ (d - 1) *
          ((dilRoot hd m n) ^ (d - 1) * (dilCore hd m n).val) := by ring
    _ = m.val * (A / m.val) ^ (d - 1) * n.val ^ (d - 1) * (m.val ^ (d - 2) * n.val) := by
        rw [hfac]
    _ = (m.val ^ 1 * m.val ^ (d - 2)) * (A / m.val) ^ (d - 1) * (n.val ^ (d - 1) * n.val ^ 1) := by
        ring
    _ = m.val ^ (d - 1) * (A / m.val) ^ (d - 1) * n.val ^ d := by
        rw [← pow_add, hd_sub, ← pow_add, hd_add]
    _ = (m.val * (A / m.val)) ^ (d - 1) * n.val ^ d := by rw [← mul_pow]
    _ = A ^ (d - 1) * n.val ^ d := by rw [hmul]

private theorem dilKeyRate_dilModeExp {d : ℕ} (hd : 3 ≤ d) {A : ℕ} (hA : 0 < A)
    {m : ℕ+} (hdiv : m.val ∣ A) (n : ℕ+) :
    dilKeyRate d A (dilModeExp hd A m n) =
      ((dilatedScale d m.val : ℝ) : ℂ) *
        allDRate d (((modeScale d : ℝ) : ℂ) * principalSaddle d) n := by
  have hreal : readRootKey (d - 1) (dilModeExp hd A m n) / (A : ℝ) =
      dilatedScale d m.val * rAction d n.val := by
    rw [dilModeExp, readRootKey_single]
    have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have hmpos : (0 : ℝ) < (m.val : ℝ) := by exact_mod_cast m.property
    have hnpos : (0 : ℝ) < (n.val : ℝ) := by exact_mod_cast n.property
    have hrne : d - 1 ≠ 0 := by omega
    have hrpos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - 1)
    have hlhs_nn : 0 ≤ ((dilExp hd A m n : ℝ) * ((dilCore hd m n).val : ℝ) ^
        (1 / ((d - 1 : ℕ) : ℝ))) / (A : ℝ) := by positivity
    have hrhs_nn : 0 ≤ dilatedScale d m.val * rAction d n.val :=
      mul_nonneg (dilatedScale_pos m.property).le (Real.rpow_nonneg hnpos.le _)
    apply (pow_left_inj₀ hlhs_nn hrhs_nn hrne).mp
    have hpow_lhs : (((dilExp hd A m n : ℝ) * ((dilCore hd m n).val : ℝ) ^
        (1 / ((d - 1 : ℕ) : ℝ))) / (A : ℝ)) ^ (d - 1) =
        ((dilExp hd A m n : ℝ) ^ (d - 1) * ((dilCore hd m n).val : ℝ)) / (A : ℝ) ^ (d - 1) := by
      rw [div_pow, mul_pow, ← Real.rpow_natCast (((dilCore hd m n).val : ℝ) ^ _),
          ← Real.rpow_mul (Nat.cast_nonneg _), one_div, inv_mul_cancel₀ hrpos.ne', Real.rpow_one]
    have hpow_rhs : (dilatedScale d m.val * rAction d n.val) ^ (d - 1) =
        (m.val : ℝ)⁻¹ * (n.val : ℝ) ^ d := by
      rw [mul_pow]
      congr 1
      · unfold dilatedScale
        rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le, neg_mul, one_div,
            inv_mul_cancel₀ hrpos.ne', Real.rpow_neg_one]
      · unfold rAction
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le,
            div_mul_cancel₀ _ hrpos.ne', Real.rpow_natCast]
    rw [hpow_lhs, hpow_rhs]
    have hnat : ((m.val : ℝ) * (dilExp hd A m n : ℝ) ^ (d - 1) * ((dilCore hd m n).val : ℝ)) =
        (A : ℝ) ^ (d - 1) * (n.val : ℝ) ^ d := by
      exact_mod_cast dil_nat_identity hd hdiv n
    field_simp [hApos.ne', hmpos.ne']
    linarith
  change (((readRootKey (d - 1) (dilModeExp hd A m n) / (A : ℝ) : ℝ) : ℂ) *
      ((modeScale d : ℝ) : ℂ)) * principalSaddle d = _
  rw [hreal, allDRate, Complex.ofReal_mul]
  ring

private theorem dilModeExp_injective {d : ℕ} (hd : 3 ≤ d) {A : ℕ} (hA : 0 < A)
    {m : ℕ+} (hdiv : m.val ∣ A) :
    Function.Injective (dilModeExp hd A m) := by
  intro n₁ n₂ heq
  have h1 := congrArg (dilKeyRate d A) heq
  rw [dilKeyRate_dilModeExp hd hA hdiv n₁, dilKeyRate_dilModeExp hd hA hdiv n₂] at h1
  have h2 : allDRate d (((modeScale d : ℝ) : ℂ) * principalSaddle d) n₁ =
      allDRate d (((modeScale d : ℝ) : ℂ) * principalSaddle d) n₂ :=
    mul_left_cancel₀ (by exact_mod_cast (dilatedScale_pos (d := d) m.property).ne') h1
  have h3 : ((rAction d n₁.val : ℝ) : ℂ) = ((rAction d n₂.val : ℝ) : ℂ) :=
    mul_right_cancel₀ (mul_ne_zero (by exact_mod_cast (modeScale_pos hd).ne')
      (principalSaddle_ne_zero hd)) h2
  have h4 : (n₁.val : ℝ) ^ ((d : ℝ) / ((d - 1 : ℕ) : ℝ)) =
      (n₂.val : ℝ) ^ ((d : ℝ) / ((d - 1 : ℕ) : ℝ)) := Complex.ofReal_injective h3
  have hexp : (0 : ℝ) < (d : ℝ) / ((d - 1 : ℕ) : ℝ) := by
    have h1' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have h2' : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - 1)
    positivity
  have h5 : (n₁.val : ℝ) = (n₂.val : ℝ) :=
    (Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) hexp.ne').mp h4
  exact PNat.eq (Nat.cast_injective h5)

/-- Prime-divisibility signature of `dilCore hd m q` when `q` is a prime `> m`. -/
private theorem dilCore_prime_dvd_iff {d : ℕ} (hd : 3 ≤ d) (m q : ℕ+)
    (hq_prime : q.val.Prime) (hm_lt : m.val < q.val) :
    q.val ∣ (dilCore hd m q).val ∧
      ∀ p : ℕ, p.Prime → m.val < p → (p ∣ (dilCore hd m q).val ↔ p = q.val) := by
  have hcop_m : Nat.Coprime (m.val ^ (d - 2)) q.val :=
    (hq_prime.coprime_iff_not_dvd.mpr fun h ↦
      (not_le.mpr hm_lt) (Nat.le_of_dvd m.property h)).symm.pow_left _
  obtain ⟨c₀, m₀, hm₀, hfac₀⟩ :=
    rfree_factorization (r := d - 1) (by omega) (m.val ^ (d - 2)) (pow_pos m.property (d - 2))
  have hc₀_dvd : c₀.val ∣ m.val ^ (d - 2) := ⟨m₀ ^ (d - 1), by linarith⟩
  have hcop_c₀ : Nat.Coprime c₀.val q.val := hcop_m.coprime_dvd_left hc₀_dvd
  have hrf_q : RFree (d - 1) q.val := rfree_of_prime (by omega) hq_prime
  have hrf_prod : RFree (d - 1) (c₀.val * q.val) :=
    rfree_mul_of_coprime (by omega) c₀.property hrf_q hcop_c₀
  let cProd : Core (d - 1) := ⟨c₀.val * q.val, hrf_prod⟩
  have hprod_eq : m₀ ^ (d - 1) * cProd.val = m.val ^ (d - 2) * q.val := by
    change m₀ ^ (d - 1) * (c₀.val * q.val) = _
    rw [← mul_assoc, hfac₀]
  have huniq := rfree_factor_unique (r := d - 1) (by omega)
    (c₁ := dilCore hd m q) (c₂ := cProd)
    (m₁ := dilRoot hd m q) (m₂ := m₀)
    (rFreeRoot_pos (d - 1) (by omega) _) hm₀
    ((rFreeRoot_pow_mul_core (d - 1) (by omega) _).trans hprod_eq.symm)
  have hc_val : (dilCore hd m q).val = c₀.val * q.val := congrArg Subtype.val huniq.1
  refine ⟨⟨c₀.val, by rw [hc_val, mul_comm]⟩, fun p hp hm_lt_p ↦ ⟨fun hp_dvd ↦ ?_, ?_⟩⟩
  · rw [hc_val] at hp_dvd
    rcases hp.dvd_mul.mp hp_dvd with hp_c₀ | hp_q
    · have hp_m : p ∣ m.val := hp.dvd_of_dvd_pow (hp_c₀.trans hc₀_dvd)
      exact absurd (Nat.le_of_dvd m.property hp_m) (not_le.mpr hm_lt_p)
    · exact (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hp_q
  · rintro rfl; exact ⟨c₀.val, by rw [hc_val, mul_comm]⟩

/-- **Pure-`ℕ` Block Dominance Lemma**: if `m₂ ≤ m₁` and `q` is a prime `> max m₁ m₂`,
then any mode `n` of dilation `m₂` landing on `dilCore hd m₁ q` satisfies
`dilExp hd A m₂ n ≥ dilExp hd A m₁ q`, with equality iff `m₂ = m₁` and `n = q`! -/
private theorem dil_block_dominance {d : ℕ} (hd : 3 ≤ d) {A : ℕ} (hA : 0 < A)
    {m₁ m₂ q n : ℕ+} (hdiv₁ : m₁.val ∣ A) (hdiv₂ : m₂.val ∣ A)
    (hq_prime : q.val.Prime) (hq₁ : m₁.val < q.val) (hq₂ : m₂.val < q.val)
    (hm_le : m₂.val ≤ m₁.val) (hcore : dilCore hd m₂ n = dilCore hd m₁ q) :
    dilExp hd A m₁ q ≤ dilExp hd A m₂ n ∧
      (dilExp hd A m₂ n = dilExp hd A m₁ q → m₂ = m₁ ∧ n = q) := by
  have hq_dvd_c : q.val ∣ (dilCore hd m₂ n).val := by
    rw [hcore]; exact (dilCore_prime_dvd_iff hd m₁ q hq_prime hq₁).1
  have hfac₂ : (dilRoot hd m₂ n) ^ (d - 1) * (dilCore hd m₂ n).val = m₂.val ^ (d - 2) * n.val :=
    rFreeRoot_pow_mul_core (d - 1) (by omega) _
  have hq_dvd_prod : q.val ∣ m₂.val ^ (d - 2) * n.val :=
    hq_dvd_c.trans ⟨(dilRoot hd m₂ n) ^ (d - 1), by linarith⟩
  have hq_not_m₂ : ¬ q.val ∣ m₂.val := fun h ↦
    (not_le.mpr hq₂) (Nat.le_of_dvd m₂.property h)
  have hq_dvd_n : q.val ∣ n.val :=
    (hq_prime.dvd_mul.mp hq_dvd_prod).resolve_left fun h ↦ hq_not_m₂ (hq_prime.dvd_of_dvd_pow h)
  obtain ⟨w, hw_eq⟩ := hq_dvd_n
  have hw_pos : 0 < w := by
    by_contra hw0
    have : w = 0 := by omega
    rw [this, mul_zero] at hw_eq
    exact n.property.ne' hw_eq
  have hid₁ := dil_nat_identity hd hdiv₁ q
  have hid₂ := dil_nat_identity hd hdiv₂ n
  rw [hcore] at hid₂
  have hc_pos : 0 < (dilCore hd m₁ q).val := rfree_pos (dilCore hd m₁ q).property
  have hpow_eq : m₂.val * (dilExp hd A m₂ n) ^ (d - 1) =
      m₁.val * (dilExp hd A m₁ q) ^ (d - 1) * w ^ d := by
    apply Nat.eq_of_mul_eq_mul_right hc_pos
    calc m₂.val * (dilExp hd A m₂ n) ^ (d - 1) * (dilCore hd m₁ q).val
        = A ^ (d - 1) * n.val ^ d := hid₂
      _ = A ^ (d - 1) * (q.val ^ d * w ^ d) := by rw [hw_eq, mul_pow]
      _ = (A ^ (d - 1) * q.val ^ d) * w ^ d := by ring
      _ = (m₁.val * (dilExp hd A m₁ q) ^ (d - 1) * (dilCore hd m₁ q).val) * w ^ d := by rw [hid₁]
      _ = m₁.val * (dilExp hd A m₁ q) ^ (d - 1) * w ^ d * (dilCore hd m₁ q).val := by ring
  have hw_pow : 1 ≤ w ^ d := one_le_pow₀ hw_pos
  have hle_pow : (dilExp hd A m₁ q) ^ (d - 1) ≤ (dilExp hd A m₂ n) ^ (d - 1) := by
    have hmul_le : m₂.val * (dilExp hd A m₁ q) ^ (d - 1) ≤ m₂.val * (dilExp hd A m₂ n) ^ (d - 1) := by
      rw [hpow_eq]
      calc m₂.val * (dilExp hd A m₁ q) ^ (d - 1)
          ≤ m₁.val * (dilExp hd A m₁ q) ^ (d - 1) := Nat.mul_le_mul_right _ hm_le
        _ ≤ m₁.val * (dilExp hd A m₁ q) ^ (d - 1) * w ^ d :=
            Nat.le_mul_of_pos_right _ (by omega)
    exact Nat.le_of_mul_le_mul_left hmul_le m₂.property
  have hle : dilExp hd A m₁ q ≤ dilExp hd A m₂ n := by
    by_contra hlt
    have hlt' : dilExp hd A m₂ n < dilExp hd A m₁ q := by omega
    have := Nat.pow_lt_pow_left hlt' (by omega : d - 1 ≠ 0)
    omega
  refine ⟨hle, fun heq ↦ ?_⟩
  rw [heq] at hpow_eq
  have he_pos : 0 < (dilExp hd A m₁ q) ^ (d - 1) := pow_pos (dilExp_pos hd hA hdiv₁ q) _
  have hmw : m₂.val = m₁.val * w ^ d := by
    apply Nat.eq_of_mul_eq_mul_right he_pos
    calc m₂.val * (dilExp hd A m₁ q) ^ (d - 1)
        = m₁.val * (dilExp hd A m₁ q) ^ (d - 1) * w ^ d := hpow_eq
      _ = m₁.val * w ^ d * (dilExp hd A m₁ q) ^ (d - 1) := by ring
  have hw1 : w ^ d = 1 := by
    have hge : m₁.val * 1 ≤ m₁.val * w ^ d := Nat.mul_le_mul_left _ hw_pow
    have hle1 : m₁.val * w ^ d ≤ m₁.val * 1 := by rw [← hmw, mul_one]; exact hm_le
    exact Nat.eq_of_mul_eq_mul_left m₁.property (le_antisymm hle1 hge)
  have hw_eq1 : w = 1 := by
    by_contra hne
    have h2 : 2 ≤ w := by omega
    have hpow2 : 2 ^ d ≤ w ^ d := Nat.pow_le_pow_left h2 d
    have hgt1 : 1 < 2 ^ d := one_lt_pow₀ (by norm_num) (by omega)
    omega
  have hm_eq : m₂ = m₁ := PNat.eq (by rw [hmw, hw1, mul_one])
  have hn_eq : n = q := PNat.eq (by rw [hw_eq, hw_eq1, mul_one])
  exact ⟨hm_eq, hn_eq⟩

/-! ### 4. Single-Variable Product Formula & Polynomial Evaluation in `TrackedExpansion` -/

/-- Exact coefficient extraction for a product of single-variable power series. -/
private theorem coeff_prod_singleVar {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (g : ι → MvPowerSeries ι R)
    (hsingle : ∀ r (m : ι →₀ ℕ), MvPowerSeries.coeff m (g r) ≠ 0 → ∃ k : ℕ, m = Finsupp.single r k)
    (m : ι →₀ ℕ) :
    MvPowerSeries.coeff m (∏ r : ι, g r) =
      ∏ r : ι, MvPowerSeries.coeff (Finsupp.single r (m r)) (g r) := by
  classical
  suffices ∀ (S : Finset ι) (m : ι →₀ ℕ),
      ((∃ i ∉ S, m i ≠ 0) → MvPowerSeries.coeff m (∏ r ∈ S, g r) = 0) ∧
      ((∀ i ∉ S, m i = 0) → MvPowerSeries.coeff m (∏ r ∈ S, g r) =
        ∏ r ∈ S, MvPowerSeries.coeff (Finsupp.single r (m r)) (g r)) by
    exact (this Finset.univ m).2 fun i hi ↦ (hi (Finset.mem_univ i)).elim
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro m
    constructor
    · rintro ⟨i, _, hi⟩
      rw [Finset.prod_empty, MvPowerSeries.coeff_one]
      have hm : m ≠ 0 := fun h ↦ hi (by simp [h])
      exact ite_eq_right hm
    · intro hall
      have hm : m = 0 := Finsupp.ext fun i ↦ hall i (Finset.notMem_empty i)
      rw [Finset.prod_empty, Finset.prod_empty, hm, MvPowerSeries.coeff_one]
      simp
  | @insert a S ha ih =>
    intro m
    rw [Finset.prod_insert ha]
    constructor
    · rintro ⟨i, hi_not, hmi⟩
      rw [MvPowerSeries.coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨u, v⟩ huv
      rw [Finset.mem_antidiagonal] at huv
      dsimp only at huv
      by_cases hu0 : MvPowerSeries.coeff u (g a) = 0
      · rw [hu0, zero_mul]
      · obtain ⟨k, rfl⟩ := hsingle a u hu0
        have hia : i ≠ a := fun h ↦ hi_not (h ▸ Finset.mem_insert_self a S)
        have hiS : i ∉ S := fun h ↦ hi_not (Finset.mem_insert_of_mem h)
        have hvi : v i ≠ 0 := by
          have := DFunLike.congr_fun huv i
          rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hia, zero_add] at this
          rwa [this]
        rw [(ih v).1 ⟨i, hiS, hvi⟩, mul_zero]
    · intro hall
      rw [MvPowerSeries.coeff_mul, Finset.prod_insert ha]
      let u₀ : ι →₀ ℕ := Finsupp.single a (m a)
      let v₀ : ι →₀ ℕ := m.erase a
      have huv₀ : u₀ + v₀ = m := by
        ext i
        rw [Finsupp.add_apply]
        by_cases hi : i = a
        · subst hi; simp [u₀, v₀]
        · simp [u₀, v₀, Finsupp.single_eq_of_ne hi, Finsupp.erase_ne hi]
      have honly : ∀ p ∈ Finset.antidiagonal m, p ≠ (u₀, v₀) →
          MvPowerSeries.coeff p.1 (g a) * MvPowerSeries.coeff p.2 (∏ r ∈ S, g r) = 0 := by
        rintro ⟨u, v⟩ huv hne
        rw [Finset.mem_antidiagonal] at huv
        dsimp only at huv
        by_contra hnz
        have hu_nz : MvPowerSeries.coeff u (g a) ≠ 0 := left_ne_zero_of_mul hnz
        have hv_nz : MvPowerSeries.coeff v (∏ r ∈ S, g r) ≠ 0 := right_ne_zero_of_mul hnz
        obtain ⟨k, rfl⟩ := hsingle a u hu_nz
        have hva : v a = 0 := by
          by_contra hne0
          exact hv_nz ((ih v).1 ⟨a, ha, hne0⟩)
        have hk : k = m a := by
          have := DFunLike.congr_fun huv a
          rw [Finsupp.add_apply, Finsupp.single_eq_same, hva, add_zero] at this
          exact this
        have hv_eq : v = v₀ := by
          ext i
          by_cases hi : i = a
          · subst hi; simp [v₀, hva]
          · have := DFunLike.congr_fun huv i
            rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hi, zero_add] at this
            simpa [v₀, Finsupp.erase_ne hi] using this
        exact hne (Prod.ext (by rw [hk]) hv_eq)
      rw [Finset.sum_eq_single (u₀, v₀) honly
          (fun hnot ↦ (hnot (Finset.mem_antidiagonal.mpr huv₀)).elim)]
      have hv₀_out : ∀ i ∉ S, v₀ i = 0 := by
        intro i hiS
        by_cases hia : i = a
        · subst hia; simp [v₀]
        · rw [Finsupp.erase_ne hia]
          exact hall i fun hmem ↦ (Finset.mem_insert.mp hmem).elim hia hiS
      rw [(ih v₀).2 hv₀_out]
      congr 1
      apply Finset.prod_congr rfl; intro r hr
      have hra : r ≠ a := fun h ↦ ha (h ▸ hr)
      simp [v₀, Finsupp.erase_ne hra]

/-- `Tendsto` for matrix determinants from entrywise limits. -/
private theorem tendsto_matrix_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ℝ → Matrix ι ι ℂ) (L : Matrix ι ι ℂ)
    (hM : ∀ i j, Tendsto (fun p ↦ M p i j) atTop (𝓝 (L i j))) :
    Tendsto (fun p ↦ (M p).det) atTop (𝓝 L.det) := by
  simp_rw [Matrix.det_apply]
  apply tendsto_finset_sum'
  intro π _
  have hprod : Tendsto (fun p ↦ ∏ i : ι, M p (π i) i) atTop (𝓝 (∏ i : ι, L (π i) i)) :=
    tendsto_finset_prod' Finset.univ (fun i p ↦ M p (π i) i) (fun i ↦ L (π i) i)
      fun i _ ↦ hM (π i) i
  have hsmul := hprod.const_mul ((Equiv.Perm.sign π : ℤ) : ℂ)
  simpa only [Units.smul_def, zsmul_eq_mul] using hsmul

/-! ### 5. `TrackedExpansion` for Dilated Jets and Polynomial Combinations -/

private def scaledWaveTracked {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (ℓ : ℕ) :
    TrackedExpansion d (2 * d) (dilKeyRate d A) where
  Index := P.Saddle × ℕ+
  exp := P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ
  finite_window := P.scaledWaves_finite_window _ _ ℓ
  parities := fun sn ↦ FiniteParities.of_half (by omega)
    (P.scaledWaves_powerClass_half _ _ ℓ sn)
  halfSpace := P.scaledWaves_halfSpace _ _ ℓ
  extreme_range := fun sn h0 ↦ by
    have hs : sn.1 = P.principal := (P.scaledWaves_rotIm_eq_zero_iff _ _ ℓ sn).mp h0
    refine ⟨dilModeExp hd A m sn.2, ?_⟩
    change ((dilatedScale d m.val : ℝ) : ℂ) * allDRate d (P.branchAction sn.1) sn.2 = _
    rw [hs, AllDStokesProfile.branchAction, P.saddleDir_principal,
        dilKeyRate_dilModeExp hd hA hdiv sn.2]

private theorem scaledWaveTracked_coeff_modeExp {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (ℓ : ℕ) (n₀ : ℕ+) :
    MvPowerSeries.coeff (dilModeExp hd A m n₀) (scaledWaveTracked hd P hA m hdiv ℓ).marked =
      Germ.ofFun ((P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ).amplitude
        (P.principal, n₀)) := by
  classical
  change (∑ i : (scaledWaveTracked hd P hA m hdiv ℓ).Fiber (dilModeExp hd A m n₀),
    Germ.ofFun ((scaledWaveTracked hd P hA m hdiv ℓ).exp.amplitude i.val)) = _
  have hmem : (P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ).rate
      (P.principal, n₀) = dilKeyRate d A (dilModeExp hd A m n₀) := by
    rw [dilKeyRate_dilModeExp hd hA hdiv n₀]
    simp [AllDStokesProfile.scaledWaves, AllDStokesProfile.branchAction, P.saddleDir_principal]
  let i₀ : (scaledWaveTracked hd P hA m hdiv ℓ).Fiber (dilModeExp hd A m n₀) :=
    ⟨(P.principal, n₀), hmem⟩
  have huniq : ∀ i : (scaledWaveTracked hd P hA m hdiv ℓ).Fiber (dilModeExp hd A m n₀), i = i₀ := by
    rintro ⟨⟨s, n⟩, hi⟩
    apply Subtype.ext
    have hi' : (P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ).rate (s, n) =
        dilKeyRate d A (dilModeExp hd A m n₀) := hi
    have hrot : rotIm d ((P.scaledWaves (dilatedScale d m.val)
        (dilatedScale_pos m.property) ℓ).rate (s, n)) = 0 := by
      rw [hi']; exact rotIm_dilKeyRate hd _
    have hs : s = P.principal :=
      (P.scaledWaves_rotIm_eq_zero_iff _ _ ℓ (s, n)).mp hrot
    have hrate_eq : dilKeyRate d A (dilModeExp hd A m n) =
        dilKeyRate d A (dilModeExp hd A m n₀) := by
      rw [dilKeyRate_dilModeExp hd hA hdiv n, ← hi']
      change ((dilatedScale d m.val : ℝ) : ℂ) *
          allDRate d (((modeScale d : ℝ) : ℂ) * principalSaddle d) n =
        ((dilatedScale d m.val : ℝ) : ℂ) * allDRate d (P.branchAction s) n
      rw [hs, AllDStokesProfile.branchAction, P.saddleDir_principal]
    have hn : n = n₀ :=
      dilModeExp_injective hd hA hdiv (dilKeyRate_injective hd hA hrate_eq)
    exact Prod.ext hs hn
  rw [Finset.sum_eq_single i₀ (fun i _ hne ↦ (hne (huniq i)).elim)
      (fun hnot ↦ (hnot (Finset.mem_univ i₀)).elim)]
  rfl

private theorem scaledWaveTracked_coeff_of_not_range {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (ℓ : ℕ) {k : Core (d - 1) →₀ ℕ}
    (hnot : ∀ n : ℕ+, k ≠ dilModeExp hd A m n) :
    MvPowerSeries.coeff k (scaledWaveTracked hd P hA m hdiv ℓ).marked = 0 := by
  classical
  change (∑ i : (scaledWaveTracked hd P hA m hdiv ℓ).Fiber k,
    Germ.ofFun ((scaledWaveTracked hd P hA m hdiv ℓ).exp.amplitude i.val)) = 0
  have : IsEmpty ((scaledWaveTracked hd P hA m hdiv ℓ).Fiber k) := ⟨fun ⟨⟨s, n⟩, hi⟩ ↦ by
    have hi' : (P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ).rate (s, n) =
        dilKeyRate d A k := hi
    have hrot : rotIm d ((P.scaledWaves (dilatedScale d m.val)
        (dilatedScale_pos m.property) ℓ).rate (s, n)) = 0 := by
      rw [hi']; exact rotIm_dilKeyRate hd k
    have hs : s = P.principal :=
      (P.scaledWaves_rotIm_eq_zero_iff _ _ ℓ (s, n)).mp hrot
    have hrate_eq : dilKeyRate d A (dilModeExp hd A m n) = dilKeyRate d A k := by
      rw [dilKeyRate_dilModeExp hd hA hdiv n, ← hi']
      change ((dilatedScale d m.val : ℝ) : ℂ) *
          allDRate d (((modeScale d : ℝ) : ℂ) * principalSaddle d) n =
        ((dilatedScale d m.val : ℝ) : ℂ) * allDRate d (P.branchAction s) n
      rw [hs, AllDStokesProfile.branchAction, P.saddleDir_principal]
    exact hnot n (dilKeyRate_injective hd hA hrate_eq).symm⟩
  simp

private def dilatedJetStep {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j ℓ : ℕ) :
    TrackedExpansion d (2 * d) (dilKeyRate d A) :=
  let hM : 0 < 2 * d := by omega
  let qE := TrackedExpansion.ofCoeff (d := d) (M := 2 * d) (keyRate := dilKeyRate d A)
    (qPolyRayCoeff hd j ℓ) (FiniteParities.of_zero hM (qPolyRayCoeff_powerClass hd j ℓ))
  let bgE := TrackedExpansion.ofCoeff (d := d) (M := 2 * d) (keyRate := dilKeyRate d A)
    (scaledBgPoleCoeff hd P m ℓ) (scaledBgPole_finiteParities hd P m ℓ)
  qE.mul hM (bgE.add (scaledWaveTracked hd P hA m hdiv ℓ))

private def dilatedJetGo {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ) :
    ℕ → TrackedExpansion d (2 * d) (dilKeyRate d A)
  | 0 => TrackedExpansion.ofCoeff ⟨fun _ ↦ 0, 0, 0, le_rfl, by simp⟩
      (FiniteParities.of_zero (by omega) (PowerClass.const 0))
  | k + 1 => (dilatedJetGo hd P hA m hdiv j k).add (dilatedJetStep hd P hA m hdiv j k)

private def dilatedJetTracked {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ) :
    TrackedExpansion d (2 * d) (dilKeyRate d A) :=
  dilatedJetGo hd P hA m hdiv j (j + 1)

private theorem dilatedJetTracked_value {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ) :
    (dilatedJetTracked hd P hA m hdiv j).exp.value =ᶠ[atTop]
      fun p ↦ psValue (formalJet (thetaDDilated d m.val) j) (qRayD d p) := by
  have hstep_val (ℓ : ℕ) :
      (dilatedJetStep hd P hA m hdiv j ℓ).exp.value =ᶠ[atTop] fun p ↦
        qPolyCoeff d j ℓ p * ((scaledBgPoleCoeff hd P m ℓ).value p +
          (P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ).value p) := by
    have hq_val : (qPolyRayCoeff hd j ℓ).value = qPolyCoeff d j ℓ := by
      unfold qPolyRayCoeff; split_ifs <;> rfl
    let bW := (TrackedExpansion.ofCoeff (d := d) (M := 2 * d) (keyRate := dilKeyRate d A)
      (scaledBgPoleCoeff hd P m ℓ) (scaledBgPole_finiteParities hd P m ℓ)).add
      (scaledWaveTracked hd P hA m hdiv ℓ)
    filter_upwards [(qPolyRayCoeff hd j ℓ).expansion.value_mul bW.exp,
      (scaledBgPoleCoeff hd P m ℓ).expansion.value_add
        (P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ)]
      with p hmul hadd
    change ((qPolyRayCoeff hd j ℓ).expansion.mul bW.exp).value p = _
    rw [hmul, rayCoeff_expansion_value, hq_val]
    congr 1
    change ((scaledBgPoleCoeff hd P m ℓ).expansion.add
        (P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ)).value p = _
    rw [hadd, rayCoeff_expansion_value]
  have hgo : ∀ N, (dilatedJetGo hd P hA m hdiv j N).exp.value =ᶠ[atTop]
      fun p ↦ ∑ ℓ ∈ Finset.range N, qPolyCoeff d j ℓ p *
        ((scaledBgPoleCoeff hd P m ℓ).value p +
          (P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ).value p) := by
    intro N
    induction N with
    | zero =>
      filter_upwards with p
      change (Physical.RayCoefficient.expansion ⟨fun _ ↦ 0, 0, 0, le_rfl, _⟩).value p = 0
      rw [rayCoeff_expansion_value]
    | succ N ih =>
      filter_upwards [ih, hstep_val N,
        (dilatedJetGo hd P hA m hdiv j N).exp.value_add (dilatedJetStep hd P hA m hdiv j N).exp]
        with p hp hs hadd
      change ((dilatedJetGo hd P hA m hdiv j N).exp.add (dilatedJetStep hd P hA m hdiv j N).exp).value p = _
      rw [hadd, hp, hs, Finset.sum_range_succ]
  filter_upwards [hgo (j + 1), dilated_qjet_split hd P m j] with p h1 h2
  rw [h2]
  change (dilatedJetGo hd P hA m hdiv j (j + 1)).exp.value p = _
  rw [h1]
  simp only [mul_add, Finset.sum_add_distrib, scaledBgPoleCoeff]

private theorem dilatedJetGo_marked_coeff_ne_zero {d : ℕ} (hd : 3 ≤ d)
    (P : AllDStokesProfile d hd) {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ)
    {k : Core (d - 1) →₀ ℕ} (hk : k ≠ 0) (N : ℕ) :
    MvPowerSeries.coeff k (dilatedJetGo hd P hA m hdiv j N).marked =
      ∑ ℓ ∈ Finset.range N,
        Germ.ofFun (qPolyCoeff d j ℓ) *
          MvPowerSeries.coeff k (scaledWaveTracked hd P hA m hdiv ℓ).marked := by
  have hM : 0 < 2 * d := by omega
  have hinj := dilKeyRate_injective hd hA
  have hface : ∀ t, rotIm d (dilKeyRate d A t) = 0 := rotIm_dilKeyRate hd
  induction N with
  | zero =>
    change MvPowerSeries.coeff k (TrackedExpansion.ofCoeff _ _).marked = 0
    rw [TrackedExpansion.marked_coeff _ _ hinj, MvPowerSeries.coeff_C, ite_eq_right hk]
  | succ N ih =>
    change MvPowerSeries.coeff k
      ((dilatedJetGo hd P hA m hdiv j N).add (dilatedJetStep hd P hA m hdiv j N)).marked = _
    rw [TrackedExpansion.marked_add, map_add, ih, Finset.sum_range_succ]
    congr 1
    unfold dilatedJetStep
    rw [TrackedExpansion.marked_mul hM _ _ hinj hface, TrackedExpansion.marked_add,
        TrackedExpansion.marked_coeff (qPolyRayCoeff hd j N) _ hinj,
        TrackedExpansion.marked_coeff (scaledBgPoleCoeff hd P m N) _ hinj]
    have hq_val : (qPolyRayCoeff hd j N).value = qPolyCoeff d j N := by
      unfold qPolyRayCoeff; split_ifs <;> rfl
    rw [hq_val, mul_add, map_add, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
        MvPowerSeries.coeff_C, ite_eq_right hk, mul_zero, zero_add]

private theorem dilatedJetTracked_coeff_modeExp {d : ℕ} (hd : 3 ≤ d)
    (P : AllDStokesProfile d hd) {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ)
    (n : ℕ+) :
    MvPowerSeries.coeff (dilModeExp hd A m n) (dilatedJetTracked hd P hA m hdiv j).marked =
      Germ.ofFun fun p ↦ ∑ ℓ ∈ Finset.range (j + 1),
        qPolyCoeff d j ℓ p *
          (P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ).amplitude
            (P.principal, n) p := by
  have hk : dilModeExp hd A m n ≠ 0 := by
    intro h0
    have h1 := DFunLike.congr_fun h0 (dilCore hd m n)
    rw [dilModeExp, Finsupp.single_eq_same, Finsupp.zero_apply] at h1
    exact (dilExp_pos hd hA hdiv n).ne' h1
  unfold dilatedJetTracked
  rw [dilatedJetGo_marked_coeff_ne_zero hd P hA m hdiv j hk (j + 1)]
  let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
  have hterm : ∀ ℓ ∈ Finset.range (j + 1),
      Germ.ofFun (qPolyCoeff d j ℓ) *
        MvPowerSeries.coeff (dilModeExp hd A m n) (scaledWaveTracked hd P hA m hdiv ℓ).marked =
      H (fun p ↦ qPolyCoeff d j ℓ p *
        (P.scaledWaves (dilatedScale d m.val) (dilatedScale_pos m.property) ℓ).amplitude
          (P.principal, n) p) := by
    intro ℓ _
    rw [scaledWaveTracked_coeff_modeExp hd P hA m hdiv ℓ n]
    rfl
  rw [Finset.sum_congr rfl hterm, ← map_sum]
  apply Germ.coe_eq.mpr
  filter_upwards with p
  simp [Finset.sum_apply]

private theorem dilatedJetTracked_coeff_of_not_range {d : ℕ} (hd : 3 ≤ d)
    (P : AllDStokesProfile d hd) {A : ℕ} (hA : 0 < A) (m : ℕ+) (hdiv : m.val ∣ A) (j : ℕ)
    {k : Core (d - 1) →₀ ℕ} (hk : k ≠ 0) (hnot : ∀ n : ℕ+, k ≠ dilModeExp hd A m n) :
    MvPowerSeries.coeff k (dilatedJetTracked hd P hA m hdiv j).marked = 0 := by
  unfold dilatedJetTracked
  rw [dilatedJetGo_marked_coeff_ne_zero hd P hA m hdiv j hk (j + 1)]
  apply Finset.sum_eq_zero; intro ℓ _
  rw [scaledWaveTracked_coeff_of_not_range hd P hA m hdiv ℓ hnot, mul_zero]

/-- Exact leading limit of the dilated jet amplitude at prime/mode `n`:
scaling by `p^{-(1/2) - d * j}` isolates the diagonal `ℓ = j` term, yielding a
nonzero row constant times `(-((d - 1)⁻¹ * σ_m * rate_n))^j`. -/
private theorem dilatedJet_amp_limit {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    (m n : ℕ+) (j : ℕ) :
    let σ := dilatedScale d m.val
    let hσ := dilatedScale_pos (d := d) m.property
    let C₀ : ℂ := ((σ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * P.pref P.principal n * P.kernel P.principal n 0
    let α : ℂ := -(((d - 1 : ℕ) : ℂ)⁻¹) * (((σ : ℝ) : ℂ) * allDRate d (P.branchAction P.principal) n)
    Tendsto (fun p : ℝ ↦
        ((p ^ (-(1 / 2 : ℝ) - ((d * j : ℕ) : ℝ)) : ℝ) : ℂ) *
          ∑ ℓ ∈ Finset.range (j + 1),
            qPolyCoeff d j ℓ p * (P.scaledWaves σ hσ ℓ).amplitude (P.principal, n) p)
      atTop (𝓝 (C₀ * α ^ j)) := by
  intro σ hσ C₀ α
  have hterm (ℓ : ℕ) (hℓ : ℓ ∈ Finset.range (j + 1)) :
      Tendsto (fun p : ℝ ↦
          ((p ^ (-(1 / 2 : ℝ) - ((d * j : ℕ) : ℝ)) : ℝ) : ℂ) *
            (qPolyCoeff d j ℓ p * (P.scaledWaves σ hσ ℓ).amplitude (P.principal, n) p))
        atTop (𝓝 (if ℓ = j then C₀ * α ^ j else 0)) := by
    have hℓ_le : ℓ ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hℓ)
    have hwave := P.scaledWaves_limit σ hσ ℓ (P.principal, n)
    have hsplit : ∀ᶠ p : ℝ in atTop,
        ((p ^ (-(1 / 2 : ℝ) - ((d * j : ℕ) : ℝ)) : ℝ) : ℂ) *
          (qPolyCoeff d j ℓ p * (P.scaledWaves σ hσ ℓ).amplitude (P.principal, n) p) =
        (((p ^ (-((d * j : ℕ) : ℝ)) : ℝ) : ℂ) * qPolyCoeff d j ℓ p) *
          (((p ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * (P.scaledWaves σ hσ ℓ).amplitude (P.principal, n) p) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
      have hrp : p ^ (-(1 / 2 : ℝ) - ((d * j : ℕ) : ℝ)) =
          p ^ (-((d * j : ℕ) : ℝ)) * p ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.rpow_add hp]; congr 1; ring
      rw [hrp, Complex.ofReal_mul]
      ring
    by_cases heq : ℓ = j
    · subst heq
      rw [ite_eq_left rfl]
      have hdiag := qPolyCoeff_diag_limit hd ℓ
      have hmul := hdiag.mul hwave
      have hlim_eq : ((((d - 1 : ℕ) : ℂ)⁻¹) ^ ℓ) *
          (C₀ * (-(((σ : ℝ) : ℂ) * allDRate d (P.branchAction P.principal) n)) ^ ℓ) =
          C₀ * α ^ ℓ := by
        simp only [α]
        rw [show -(((d - 1 : ℕ) : ℂ)⁻¹) * (((σ : ℝ) : ℂ) * allDRate d (P.branchAction P.principal) n) =
            (((d - 1 : ℕ) : ℂ)⁻¹) * (-(((σ : ℝ) : ℂ) * allDRate d (P.branchAction P.principal) n)) by ring,
            mul_pow]
        ring
      rw [hlim_eq] at hmul
      exact hmul.congr' (hsplit.mono fun _ h ↦ h.symm)
    · rw [ite_eq_right heq]
      have hlt : (((d : ℤ) * (j : ℤ)) - ((j - ℓ : ℕ) : ℤ)) < ((d * j : ℕ) : ℤ) := by
        push_cast; omega
      have hq0 := (qPolyCoeff_QCoeff hd j ℓ hℓ_le).tendsto_zero_of_lt hd hlt
      have hq0' : Tendsto (fun p : ℝ ↦ ((p ^ (-((d * j : ℕ) : ℝ)) : ℝ) : ℂ) * qPolyCoeff d j ℓ p)
          atTop (𝓝 0) := by
        apply hq0.congr'
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with p hp
        congr 2
      have hmul := hq0'.mul hwave
      rw [zero_mul] at hmul
      exact hmul.congr' (hsplit.mono fun _ h ↦ h.symm)
  have hsum := tendsto_finset_sum' (Finset.range (j + 1)) _ _ hterm
  rw [Finset.sum_ite_eq' (Finset.range (j + 1)) j,
      ite_eq_left (Finset.mem_range.mpr (Nat.lt_succ_self j))] at hsum
  apply hsum.congr'
  filter_upwards with p
  rw [Finset.mul_sum]

/-- Evaluate any `Q₁ : MvPolynomial ι (Polynomial ℂ)` on a family of `TrackedExpansion`s,
preserving both the real-ray value and the `Polynomial ℂ`-algebra marked power series! -/
private theorem evalPolyMv_tracked {d : ℕ} (hd : 3 ≤ d) {A : ℕ} (hA : 0 < A) {ι : Type*}
    (f : ι → TrackedExpansion d (2 * d) (dilKeyRate d A))
    (Q₁ : MvPolynomial ι (Polynomial ℂ)) :
    letI : Algebra (Polynomial ℂ) RayGerm := (polyToGerm d).toAlgebra
    ∃ E : TrackedExpansion d (2 * d) (dilKeyRate d A),
      (E.exp.value =ᶠ[atTop] fun p ↦
        MvPolynomial.eval₂ (Polynomial.evalRingHom (qRayD d p)) (fun x ↦ (f x).exp.value p) Q₁) ∧
      E.marked = MvPolynomial.aeval (R := Polynomial ℂ) (fun x ↦ (f x).marked) Q₁ := by
  let _ : Algebra (Polynomial ℂ) RayGerm := (polyToGerm d).toAlgebra
  have hM : 0 < 2 * d := by omega
  have hinj := dilKeyRate_injective hd hA
  have hface : ∀ k, rotIm d (dilKeyRate d A k) = 0 := rotIm_dilKeyRate hd
  induction Q₁ using MvPolynomial.induction_on with
  | C R =>
    refine ⟨TrackedExpansion.ofCoeff (polyRayCoeff d R)
        (FiniteParities.of_zero hM (polyRayCoeff_powerClass hd R)), ?_, ?_⟩
    · filter_upwards with p
      change (polyRayCoeff d R).expansion.value p = _
      rw [rayCoeff_expansion_value]
      simp [polyRayCoeff]
    · rw [TrackedExpansion.marked_coeff _ _ hinj, MvPolynomial.aeval_C,
          MvPowerSeries.algebraMap_apply]
      rfl
  | add P₁ P₂ h₁ h₂ =>
    obtain ⟨E₁, hv₁, hm₁⟩ := h₁
    obtain ⟨E₂, hv₂, hm₂⟩ := h₂
    refine ⟨E₁.add E₂, ?_, ?_⟩
    · filter_upwards [hv₁, hv₂, E₁.exp.value_add E₂.exp] with p h1 h2 hadd
      change (E₁.exp.add E₂.exp).value p = _
      rw [hadd, h1, h2, MvPolynomial.eval₂_add]
    · rw [TrackedExpansion.marked_add, hm₁, hm₂, map_add]
  | mul_X P₁ x h₁ =>
    obtain ⟨E₁, hv₁, hm₁⟩ := h₁
    refine ⟨E₁.mul hM (f x), ?_, ?_⟩
    · filter_upwards [hv₁, E₁.exp.value_mul (f x).exp] with p h1 hmul
      change (E₁.exp.mul (f x).exp).value p = _
      rw [hmul, h1, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    · rw [TrackedExpansion.marked_mul hM _ _ hinj hface, hm₁, map_mul, MvPolynomial.aeval_X]

/-! ### 6. Core Multi-Dilation Theorem for Strictly Decreasing Dilations -/

/-- Core algebraic independence of the marked power series of dilated jets on `Fin s ×ₗ Fin J`
over `K = Polynomial ℂ`, proved via block-triangular lex-minimum Jacobian dominance and
Vandermonde unit blocks! -/
private theorem dilated_marked_algIndep {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {s J : ℕ} (hJ_pos : 0 < J) (a : Fin s → ℕ+)
    (hdec : ∀ i j : Fin s, i < j → (a j).val < (a i).val) :
    letI : Algebra (Polynomial ℂ) RayGerm := (polyToGerm d).toAlgebra
    let A : ℕ := ∏ i : Fin s, (a i).val
    let hA_pos : 0 < A := Finset.prod_pos fun i _ ↦ (a i).property
    let hA_dvd : ∀ i : Fin s, (a i).val ∣ A := fun i ↦
      Finset.dvd_prod_of_mem (fun k ↦ (a k).val) (Finset.mem_univ i)
    AlgebraicIndependent (Polynomial ℂ) (fun r : Fin s ×ₗ Fin J ↦
      (dilatedJetTracked hd P hA_pos (a (ofLex r).1) (hA_dvd (ofLex r).1) (ofLex r).2.val).marked) := by
  classical
  let _ : Algebra (Polynomial ℂ) RayGerm := (polyToGerm d).toAlgebra
  have hpoly_inj : Function.Injective (algebraMap (Polynomial ℂ) RayGerm) := polyToGerm_injective hd
  have hdec_le : ∀ i j : Fin s, i ≤ j → (a j).val ≤ (a i).val := by
    intro i j hij
    rcases hij.eq_or_lt with rfl | hlt
    · exact le_rfl
    · exact (hdec i j hlt).le
  let A : ℕ := ∏ i : Fin s, (a i).val
  have hA_pos : 0 < A := Finset.prod_pos fun i _ ↦ (a i).property
  have hA_dvd : ∀ i : Fin s, (a i).val ∣ A := fun i ↦
    Finset.dvd_prod_of_mem (fun k ↦ (a k).val) (Finset.mem_univ i)
  have hA_ge : ∀ i : Fin s, (a i).val ≤ A := fun i ↦ Nat.le_of_dvd hA_pos (hA_dvd i)
  let ι := Fin s ×ₗ Fin J
  let fTracked : ι → TrackedExpansion d (2 * d) (dilKeyRate d A) :=
    fun r ↦ dilatedJetTracked hd P hA_pos (a (ofLex r).1) (hA_dvd (ofLex r).1) (ofLex r).2.val
  -- Choose `s * J` fresh primes strictly greater than `A` and form the prime-core marks.
  let idx (r : ι) : ℕ := A + 1 + (ofLex r).1.val * J + (ofLex r).2.val
  have hidx_inj : Function.Injective idx := by
    intro u v huv
    have h1 : (ofLex u).1.val * J + (ofLex u).2.val = (ofLex v).1.val * J + (ofLex v).2.val := by
      dsimp only [idx] at huv; omega
    have hq : (ofLex u).1.val = (ofLex v).1.val := by
      have hdiv1 : ((ofLex u).1.val * J + (ofLex u).2.val) / J = (ofLex u).1.val := by
        rw [mul_comm (ofLex u).1.val J, Nat.mul_add_div hJ_pos, Nat.div_eq_of_lt (ofLex u).2.isLt, add_zero]
      have hdiv2 : ((ofLex v).1.val * J + (ofLex v).2.val) / J = (ofLex v).1.val := by
        rw [mul_comm (ofLex v).1.val J, Nat.mul_add_div hJ_pos, Nat.div_eq_of_lt (ofLex v).2.isLt, add_zero]
      rw [← hdiv1, ← hdiv2, h1]
    have hr : (ofLex u).2.val = (ofLex v).2.val := by rw [hq] at h1; omega
    exact ofLex.injective (Prod.ext (Fin.ext hq) (Fin.ext hr))
  let primeOf (r : ι) : ℕ+ :=
    ⟨Nat.nth Nat.Prime (idx r), (Nat.prime_nth_prime (idx r)).pos⟩
  have hprime_prime (r : ι) : (primeOf r).val.Prime :=
    Nat.prime_nth_prime (idx r)
  have hprime_gt_A (r : ι) : A < (primeOf r).val := by
    have hmono : StrictMono (Nat.nth Nat.Prime) := Nat.nth_strictMono Nat.infinite_setOfPred_prime
    have hle : idx r ≤ Nat.nth Nat.Prime (idx r) := hmono.id_le (idx r)
    have hlt : A < idx r := by dsimp only [idx]; omega
    exact lt_of_lt_of_le hlt hle
  have hprime_inj : Function.Injective primeOf := by
    intro u v h
    have hnth : Nat.nth Nat.Prime (idx u) = Nat.nth Nat.Prime (idx v) := congrArg Subtype.val h
    exact hidx_inj ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective hnth)
  let marks (r : ι) : Core (d - 1) := dilCore hd (a (ofLex r).1) (primeOf r)
  have hmarks_inj : Function.Injective marks := by
    intro u v huv
    have hdvd : (primeOf u).val ∣ (dilCore hd (a (ofLex u).1) (primeOf u)).val :=
      (dilCore_prime_dvd_iff hd (a (ofLex u).1) (primeOf u) (hprime_prime u)
        (lt_of_le_of_lt (hA_ge (ofLex u).1) (hprime_gt_A u))).1
    rw [show dilCore hd (a (ofLex u).1) (primeOf u) = dilCore hd (a (ofLex v).1) (primeOf v) from huv] at hdvd
    have heq_p := ((dilCore_prime_dvd_iff hd (a (ofLex v).1) (primeOf v) (hprime_prime v)
        (lt_of_le_of_lt (hA_ge (ofLex v).1) (hprime_gt_A v))).2 (primeOf u).val (hprime_prime u)
        (lt_of_le_of_lt (hA_ge (ofLex v).1) (hprime_gt_A u))).mp hdvd
    exact hprime_inj (PNat.eq heq_p)
  -- Project marked power series onto the `ι = Fin s ×ₗ Fin J` marked variables.
  let restr := restrictVars (R := RayGerm) marks hmarks_inj
  let fRestr : ι → MvPowerSeries ι RayGerm := fun r ↦ restr (fTracked r).marked
  have hrestr_alg : ∀ P₀ : MvPolynomial ι (Polynomial ℂ),
      restr (MvPolynomial.aeval (R := Polynomial ℂ) (fun r ↦ (fTracked r).marked) P₀) =
        MvPolynomial.aeval (R := Polynomial ℂ) fRestr P₀ := by
    intro P₀
    induction P₀ using MvPolynomial.induction_on with
    | C R =>
      rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, MvPowerSeries.algebraMap_apply,
          MvPowerSeries.algebraMap_apply, restrictVars_C]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p r hp => simp only [map_mul, hp, MvPolynomial.aeval_X, fRestr]
  -- Define the Jacobian matrix `Jac` and target lex-minimum monomial `mStar`.
  let Jac : Matrix ι ι (MvPowerSeries ι RayGerm) :=
    Matrix.of fun r c ↦ MvPowerSeries.pderiv r (fRestr c)
  let mStar : ι →₀ ℕ :=
    Finsupp.equivFunOnFinite.symm fun r ↦ dilExp hd A (a (ofLex r).1) (primeOf r) - 1
  have hmStar_apply (r : ι) : mStar r = dilExp hd A (a (ofLex r).1) (primeOf r) - 1 := rfl
  -- Every entry `Jac r c` depends ONLY on the single variable `r`!
  have hJac_single (r c : ι) (m : ι →₀ ℕ)
      (hnz : MvPowerSeries.coeff m (Jac r c) ≠ 0) :
      ∃ n : ℕ+, dilCore hd (a (ofLex c).1) n = marks r ∧
        m = Finsupp.single r (dilExp hd A (a (ofLex c).1) n - 1) := by
    have hpd : MvPowerSeries.coeff m (MvPowerSeries.pderiv r (fRestr c)) ≠ 0 := hnz
    rw [MvPowerSeries.coeff_pderiv] at hpd
    have hfc_nz : MvPowerSeries.coeff (m + Finsupp.single r 1) (fRestr c) ≠ 0 :=
      left_ne_zero_of_mul hpd
    rw [show fRestr c = restrictVars marks hmarks_inj (fTracked c).marked from rfl,
        coeff_restrictVars] at hfc_nz
    have hmap_ne0 : (m + Finsupp.single r 1).mapDomain marks ≠ 0 := by
      intro h0
      have h1 := DFunLike.congr_fun h0 (marks r)
      rw [Finsupp.mapDomain_apply_of_injective hmarks_inj, Finsupp.add_apply,
          Finsupp.single_eq_same, Finsupp.zero_apply] at h1
      omega
    have hex : ∃ n : ℕ+, (m + Finsupp.single r 1).mapDomain marks =
        dilModeExp hd A (a (ofLex c).1) n := by
      by_contra hnot
      push Not at hnot
      exact hfc_nz (dilatedJetTracked_coeff_of_not_range hd P hA_pos
        (a (ofLex c).1) (hA_dvd (ofLex c).1) (ofLex c).2.val hmap_ne0 hnot)
    obtain ⟨n, hn⟩ := hex
    have hmap_eq : (m + Finsupp.single r 1).mapDomain marks =
        Finsupp.single (dilCore hd (a (ofLex c).1) n) (dilExp hd A (a (ofLex c).1) n) := hn
    have he_pos : 0 < dilExp hd A (a (ofLex c).1) n := dilExp_pos hd hA_pos (hA_dvd (ofLex c).1) n
    have hcore_eq : dilCore hd (a (ofLex c).1) n = marks r := by
      by_contra hne
      have h1 := DFunLike.congr_fun hmap_eq (marks r)
      rw [Finsupp.mapDomain_apply_of_injective hmarks_inj, Finsupp.add_apply,
          Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hne)] at h1
      omega
    refine ⟨n, hcore_eq, ?_⟩
    ext u
    have h1 := DFunLike.congr_fun hmap_eq (marks u)
    rw [Finsupp.mapDomain_apply_of_injective hmarks_inj, hcore_eq, Finsupp.add_apply] at h1
    by_cases hu : u = r
    · subst hu
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same] at h1
      rw [Finsupp.single_eq_same]
      omega
    · rw [Finsupp.single_eq_of_ne hu, add_zero,
          Finsupp.single_eq_of_ne (fun h ↦ hu (hmarks_inj h))] at h1
      rw [Finsupp.single_eq_of_ne hu]
      exact h1
  -- Step A: `mStar` is the lexicographical minimum of `Jac.det`!
  have hmin : ∀ m : ι →₀ ℕ,
      MvPowerSeries.coeff m Jac.det ≠ 0 → toLex mStar ≤ toLex m := by
    intro m hm_nz
    rw [Matrix.det_apply, map_sum] at hm_nz
    obtain ⟨π, _, hπ_nz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm_nz
    rw [Units.smul_def, map_zsmul] at hπ_nz
    have hprod_nz : MvPowerSeries.coeff m (∏ r : ι, Jac (π r) r) ≠ 0 := by
      intro h0; rw [h0, smul_zero] at hπ_nz; exact hπ_nz rfl
    have hprod_eq : (∏ r : ι, Jac (π r) r) = ∏ r : ι, Jac r (π.symm r) :=
      Fintype.prod_equiv π _ (fun r ↦ Jac r (π.symm r)) fun r ↦ by simp
    rw [hprod_eq, coeff_prod_singleVar (fun r ↦ Jac r (π.symm r))
        (fun r m' hm' ↦ by obtain ⟨n, _, rfl⟩ := hJac_single r (π.symm r) m' hm'; exact ⟨_, rfl⟩)]
      at hprod_nz
    have hrow_nz : ∀ r : ι,
        MvPowerSeries.coeff (Finsupp.single r (m r)) (Jac r (π.symm r)) ≠ 0 :=
      fun r hr ↦ hprod_nz (Finset.prod_eq_zero (Finset.mem_univ r) hr)
    by_contra hlt_lex
    have hlt_m : toLex m < toLex mStar := not_le.mp hlt_lex
    obtain ⟨r₀, hr₀_eq, hr₀_lt⟩ := Finsupp.Lex.lt_iff.mp hlt_m
    have hblock_fixed : ∀ k ≤ (ofLex r₀).1.val, ∀ r : ι, (ofLex r).1.val < k →
        (ofLex (π.symm r)).1 = (ofLex r).1 := by
      intro k
      induction k with
      | zero => intro _ r hr; omega
      | succ k ih =>
        intro hk r hr
        by_cases hrk : (ofLex r).1.val < k
        · exact ih (by omega) r hrk
        · have hr_eq : (ofLex r).1.val = k := by omega
          have hlt_r₀ : r < r₀ := Prod.Lex.lt_iff.mpr (Or.inl (by change (ofLex r).1.val < (ofLex r₀).1.val; omega))
          have hm_eq : m r = mStar r := hr₀_eq r hlt_r₀
          obtain ⟨n, hcore, hm_single⟩ := hJac_single r (π.symm r) _ (hrow_nz r)
          have hmr : m r = dilExp hd A (a (ofLex (π.symm r)).1) n - 1 := by
            have := DFunLike.congr_fun hm_single r
            simpa only [Finsupp.single_eq_same] using this
          have hge_k : k ≤ (ofLex (π.symm r)).1.val := by
            by_contra hlt_k
            push Not at hlt_k
            let S : Finset ι := Finset.univ.filter fun x ↦ (ofLex x).1.val < k
            have hmaps : Set.MapsTo (π.symm : ι → ι) S S := by
              intro x hx
              simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              rw [ih (by omega) x hx]; exact hx
            have hsurj : Set.SurjOn (π.symm : ι → ι) S S :=
              Finset.surjOn_of_injOn_of_card_le _ (fun x hx ↦ hmaps hx)
                (π.symm.injective.injOn) le_rfl
            have hmem : π.symm r ∈ (S : Set ι) := by
              simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hlt_k
            obtain ⟨x, hxS, hxeq⟩ := hsurj hmem
            have hxr : x = r := π.symm.injective hxeq
            subst hxr
            simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and] at hxS
            omega
          have hle_a : (a (ofLex (π.symm r)).1).val ≤ (a (ofLex r).1).val :=
            hdec_le (ofLex r).1 (ofLex (π.symm r)).1 (by omega)
          have hdom := dil_block_dominance hd hA_pos (hA_dvd (ofLex r).1) (hA_dvd (ofLex (π.symm r)).1)
            (hprime_prime r) (lt_of_le_of_lt (hA_ge (ofLex r).1) (hprime_gt_A r))
            (lt_of_le_of_lt (hA_ge (ofLex (π.symm r)).1) (hprime_gt_A r)) hle_a hcore
          have he_eq : dilExp hd A (a (ofLex (π.symm r)).1) n =
              dilExp hd A (a (ofLex r).1) (primeOf r) := by
            have h1 := dilExp_pos hd hA_pos (hA_dvd (ofLex r).1) (primeOf r)
            have h2 := dilExp_pos hd hA_pos (hA_dvd (ofLex (π.symm r)).1) n
            rw [hmStar_apply] at hm_eq
            omega
          have h_a_eq : a (ofLex (π.symm r)).1 = a (ofLex r).1 := (hdom.2 he_eq).1
          by_contra hne_blk
          rcases lt_or_gt_of_ne hne_blk with hlt' | hgt'
          · exact (hdec _ _ hlt').ne' (congrArg Subtype.val h_a_eq)
          · exact (hdec _ _ hgt').ne (congrArg Subtype.val h_a_eq)
    have hge_r₀ : (ofLex r₀).1.val ≤ (ofLex (π.symm r₀)).1.val := by
      by_contra hlt_k
      push Not at hlt_k
      let S : Finset ι := Finset.univ.filter fun x ↦ (ofLex x).1.val < (ofLex r₀).1.val
      have hmaps : Set.MapsTo (π.symm : ι → ι) S S := by
        intro x hx
        simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        rw [hblock_fixed (ofLex r₀).1.val le_rfl x hx]; exact hx
      have hsurj : Set.SurjOn (π.symm : ι → ι) S S :=
        Finset.surjOn_of_injOn_of_card_le _ (fun x hx ↦ hmaps hx)
          (π.symm.injective.injOn) le_rfl
      have hmem : π.symm r₀ ∈ (S : Set ι) := by
        simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hlt_k
      obtain ⟨x, hxS, hxeq⟩ := hsurj hmem
      have hxr : x = r₀ := π.symm.injective hxeq
      subst hxr
      simp only [Finset.mem_coe, S, Finset.mem_filter, Finset.mem_univ, true_and] at hxS
      omega
    obtain ⟨n₀, hcore₀, hm_single₀⟩ := hJac_single r₀ (π.symm r₀) _ (hrow_nz r₀)
    have hmr₀ : m r₀ = dilExp hd A (a (ofLex (π.symm r₀)).1) n₀ - 1 := by
      have := DFunLike.congr_fun hm_single₀ r₀
      simpa only [Finsupp.single_eq_same] using this
    have hle_a₀ : (a (ofLex (π.symm r₀)).1).val ≤ (a (ofLex r₀).1).val :=
      hdec_le (ofLex r₀).1 (ofLex (π.symm r₀)).1 hge_r₀
    have hdom₀ := (dil_block_dominance hd hA_pos (hA_dvd (ofLex r₀).1) (hA_dvd (ofLex (π.symm r₀)).1)
      (hprime_prime r₀) (lt_of_le_of_lt (hA_ge (ofLex r₀).1) (hprime_gt_A r₀))
      (lt_of_le_of_lt (hA_ge (ofLex (π.symm r₀)).1) (hprime_gt_A r₀)) hle_a₀ hcore₀).1
    have hlt_r₀' : m r₀ < dilExp hd A (a (ofLex r₀).1) (primeOf r₀) - 1 := hr₀_lt
    omega
  -- Step B: `MvPowerSeries.coeff mStar Jac.det` equals `B.det` for a block-triangular matrix `B`,
  -- whose diagonal blocks are Vandermonde units in `RayGerm`!
  let B : Matrix ι ι RayGerm :=
    Matrix.of fun r c ↦ MvPowerSeries.coeff (Finsupp.single r (mStar r)) (Jac r c)
  have hcoeff_det : MvPowerSeries.coeff mStar Jac.det = B.det := by
    rw [Matrix.det_apply, Matrix.det_apply, map_sum]
    apply Finset.sum_congr rfl; intro π _
    rw [Units.smul_def, Units.smul_def, map_zsmul]
    congr 1
    have hprod_eq : (∏ r : ι, Jac (π r) r) = ∏ r : ι, Jac r (π.symm r) :=
      Fintype.prod_equiv π _ (fun r ↦ Jac r (π.symm r)) fun r ↦ by simp
    have hprod_B : (∏ r : ι, B (π r) r) = ∏ r : ι, B r (π.symm r) :=
      Fintype.prod_equiv π _ (fun r ↦ B r (π.symm r)) fun r ↦ by simp
    rw [hprod_eq, hprod_B, coeff_prod_singleVar (fun r ↦ Jac r (π.symm r))
        (fun r m' hm' ↦ by obtain ⟨n, _, rfl⟩ := hJac_single r (π.symm r) m' hm'; exact ⟨_, rfl⟩)]
    rfl
  let blk (r : ι) : Fin s := (ofLex r).1
  have hB_tri : Bᵀ.BlockTriangular blk := by
    intro c r hlt
    change B r c = 0
    by_contra hnz
    obtain ⟨n, hcore, hm_single⟩ := hJac_single r c _ hnz
    have hmr : mStar r = dilExp hd A (a (ofLex c).1) n - 1 := by
      have := DFunLike.congr_fun hm_single r
      simpa only [Finsupp.single_eq_same] using this
    have hdom := dil_block_dominance hd hA_pos (hA_dvd (ofLex r).1) (hA_dvd (ofLex c).1)
      (hprime_prime r) (lt_of_le_of_lt (hA_ge (ofLex r).1) (hprime_gt_A r))
      (lt_of_le_of_lt (hA_ge (ofLex c).1) (hprime_gt_A r)) (hdec_le (ofLex r).1 (ofLex c).1 hlt.le) hcore
    have he_eq : dilExp hd A (a (ofLex c).1) n = dilExp hd A (a (ofLex r).1) (primeOf r) := by
      have h1 := dilExp_pos hd hA_pos (hA_dvd (ofLex r).1) (primeOf r)
      have h2 := dilExp_pos hd hA_pos (hA_dvd (ofLex c).1) n
      rw [hmStar_apply] at hmr
      omega
    have ha_eq : a (ofLex c).1 = a (ofLex r).1 := (hdom.2 he_eq).1
    exact (hdec (ofLex r).1 (ofLex c).1 hlt).ne (congrArg Subtype.val ha_eq)
  have hB_det : B.det = ∏ i : Fin s, (Matrix.of fun ν j : Fin J ↦ B (toLex (i, ν)) (toLex (i, j))).det := by
    rw [← Matrix.det_transpose, hB_tri.det_fintype]
    apply Finset.prod_congr rfl; intro i _
    let e : {x : ι // blk x = i} ≃ Fin J :=
      { toFun := fun x ↦ (ofLex x.val).2
        invFun := fun ν ↦ ⟨toLex (i, ν), rfl⟩
        left_inv := fun ⟨x, hx⟩ ↦ Subtype.ext (ofLex.injective (Prod.ext hx.symm rfl))
        right_inv := fun _ ↦ rfl }
    rw [← Matrix.det_reindex_self e (Bᵀ.toSquareBlock blk i), ← Matrix.det_transpose]
    rfl
  -- Each diagonal block `B_i` has determinant a unit in `RayGerm` (Vandermonde limit ≠ 0!).
  have hblock_unit : ∀ i : Fin s,
      IsUnit (Matrix.of fun ν j : Fin J ↦ B (toLex (i, ν)) (toLex (i, j))).det := by
    intro i
    let σ := dilatedScale d (a i).val
    let hσ := dilatedScale_pos (d := d) (a i).property
    let M (p : ℝ) : Matrix (Fin J) (Fin J) ℂ :=
      Matrix.of fun ν j ↦ ((dilExp hd A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ) *
        ∑ ℓ ∈ Finset.range (j.val + 1),
          qPolyCoeff d j.val ℓ p *
            (P.scaledWaves σ hσ ℓ).amplitude (P.principal, primeOf (toLex (i, ν))) p
    have hB_eq : ∀ ν j : Fin J, B (toLex (i, ν)) (toLex (i, j)) = Germ.ofFun (fun p ↦ M p ν j) := by
      intro ν j
      let r := toLex (i, ν)
      let c := toLex (i, j)
      change MvPowerSeries.coeff (Finsupp.single r (mStar r))
          (MvPowerSeries.pderiv r (fRestr c)) = _
      rw [MvPowerSeries.coeff_pderiv]
      have he_pos : 0 < dilExp hd A (a i) (primeOf r) :=
        dilExp_pos hd hA_pos (hA_dvd i) (primeOf r)
      have hsucc : mStar r + 1 = dilExp hd A (a i) (primeOf r) := by
        rw [hmStar_apply]; change dilExp hd A (a i) (primeOf r) - 1 + 1 = _; omega
      have hadd_single : Finsupp.single r (mStar r) + Finsupp.single r 1 =
          Finsupp.single r (dilExp hd A (a i) (primeOf r)) := by
        rw [← Finsupp.single_add, hsucc]
      have hmap_single : (Finsupp.single r (dilExp hd A (a i) (primeOf r))).mapDomain marks =
          dilModeExp hd A (a i) (primeOf r) := by
        rw [Finsupp.mapDomain_single]; rfl
      rw [Finsupp.single_eq_same, hadd_single,
          show fRestr c = restrictVars marks hmarks_inj (fTracked c).marked from rfl,
          coeff_restrictVars, hmap_single,
          show fTracked c = dilatedJetTracked hd P hA_pos (a i) (hA_dvd i) j.val from rfl,
          dilatedJetTracked_coeff_modeExp hd P hA_pos (a i) (hA_dvd i) j.val (primeOf r)]
      have hnat : ((mStar r : RayGerm) + 1) =
          Germ.ofFun (fun _ : ℝ ↦ ((dilExp hd A (a i) (primeOf r) : ℕ) : ℂ)) := by
        rw [show ((mStar r : RayGerm) + 1) = ((mStar r + 1 : ℕ) : RayGerm) by push_cast; rfl, hsucc]
        rfl
      rw [hnat, mul_comm]
      rfl
    have hdet_germ : (Matrix.of fun ν j : Fin J ↦ B (toLex (i, ν)) (toLex (i, j))).det =
        Germ.ofFun (fun p ↦ (M p).det) := by
      let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
      have hmat : (Matrix.of fun ν j : Fin J ↦ B (toLex (i, ν)) (toLex (i, j))) =
          H.mapMatrix (Matrix.of fun ν j : Fin J ↦ fun p ↦ M p ν j) := by
        ext ν j; exact hB_eq ν j
      rw [hmat, ← RingHom.map_det]
      apply Germ.coe_eq.mpr
      filter_upwards with p
      simp only [Matrix.det_apply, Finset.sum_apply, Pi.smul_apply, Finset.prod_apply, Matrix.of_apply]
    rw [hdet_germ]
    let colScale (p : ℝ) (j : Fin J) : ℂ := ((p ^ (-(1 / 2 : ℝ) - ((d * j.val : ℕ) : ℝ)) : ℝ) : ℂ)
    let Mscaled (p : ℝ) : Matrix (Fin J) (Fin J) ℂ :=
      Matrix.of fun ν j ↦ colScale p j * M p ν j
    let rowC (ν : Fin J) : ℂ := ((dilExp hd A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ) *
      (((σ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * P.pref P.principal (primeOf (toLex (i, ν))) *
        P.kernel P.principal (primeOf (toLex (i, ν))) 0)
    let α (ν : Fin J) : ℂ := -(((d - 1 : ℕ) : ℂ)⁻¹) *
      (((σ : ℝ) : ℂ) * allDRate d (P.branchAction P.principal) (primeOf (toLex (i, ν))))
    let L : Matrix (Fin J) (Fin J) ℂ := Matrix.of fun ν j ↦ rowC ν * (α ν) ^ j.val
    have hlim_entry : ∀ ν j : Fin J,
        Tendsto (fun p ↦ Mscaled p ν j) atTop (𝓝 (L ν j)) := by
      intro ν j
      have hl := (dilatedJet_amp_limit hd P (a i) (primeOf (toLex (i, ν))) j.val).const_mul
        ((dilExp hd A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ)
      have hL_val : ((dilExp hd A (a i) (primeOf (toLex (i, ν))) : ℕ) : ℂ) *
          ((((σ ^ (1 / 2 : ℝ) : ℝ) : ℂ) * P.pref P.principal (primeOf (toLex (i, ν))) *
            P.kernel P.principal (primeOf (toLex (i, ν))) 0) * (α ν) ^ j.val) = L ν j := by
        simp only [L, rowC, Matrix.of_apply]; ring
      rw [hL_val] at hl
      refine hl.congr' ?_
      filter_upwards with p
      simp only [Mscaled, M, colScale, Matrix.of_apply]
      ring
    have hlim_det : Tendsto (fun p ↦ (Mscaled p).det) atTop (𝓝 L.det) :=
      tendsto_matrix_det Mscaled L hlim_entry
    have hL_det_ne0 : L.det ≠ 0 := by
      have hL_eq : L = Matrix.diagonal rowC * Matrix.vandermonde α := by
        ext ν j; simp [L, Matrix.diagonal_mul, Matrix.vandermonde_apply]
      rw [hL_eq, Matrix.det_mul, Matrix.det_diagonal]
      apply mul_ne_zero
      · apply Finset.prod_ne_zero_iff.mpr; intro ν _
        refine mul_ne_zero (by exact_mod_cast (dilExp_pos hd hA_pos (hA_dvd i) (primeOf (toLex (i, ν)))).ne') ?_
        refine mul_ne_zero (mul_ne_zero ?_ (P.pref_principal_ne_zero _)) (P.kernel_principal_zero _)
        exact_mod_cast (Real.rpow_pos_of_pos hσ _).ne'
      · rw [Matrix.det_vandermonde_ne_zero_iff]
        intro ν₁ ν₂ hα
        have hc_ne : -(((d - 1 : ℕ) : ℂ)⁻¹) * ((σ : ℝ) : ℂ) * (P.branchAction P.principal) ≠ 0 := by
          refine mul_ne_zero (mul_ne_zero ?_ (by exact_mod_cast hσ.ne')) ?_
          · exact neg_ne_zero.mpr (inv_ne_zero (by exact_mod_cast (by omega : d - 1 ≠ 0)))
          · rw [AllDStokesProfile.branchAction, P.saddleDir_principal]
            exact mul_ne_zero (by exact_mod_cast (modeScale_pos hd).ne') (principalSaddle_ne_zero hd)
        have hα' : (-(((d - 1 : ℕ) : ℂ)⁻¹) * ((σ : ℝ) : ℂ) * P.branchAction P.principal) *
              ((rAction d (primeOf (toLex (i, ν₁))).val : ℝ) : ℂ) =
            (-(((d - 1 : ℕ) : ℂ)⁻¹) * ((σ : ℝ) : ℂ) * P.branchAction P.principal) *
              ((rAction d (primeOf (toLex (i, ν₂))).val : ℝ) : ℂ) := by
          change -(((d - 1 : ℕ) : ℂ)⁻¹) * (((σ : ℝ) : ℂ) *
              (((rAction d (primeOf (toLex (i, ν₁))).val : ℝ) : ℂ) * P.branchAction P.principal)) =
            -(((d - 1 : ℕ) : ℂ)⁻¹) * (((σ : ℝ) : ℂ) *
              (((rAction d (primeOf (toLex (i, ν₂))).val : ℝ) : ℂ) * P.branchAction P.principal)) at hα
          linear_combination hα
        have hr_eq := Complex.ofReal_injective (mul_left_cancel₀ hc_ne hα')
        have hexp : (0 : ℝ) < (d : ℝ) / ((d - 1 : ℕ) : ℝ) := by
          have h1' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
          have h2' : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < d - 1)
          positivity
        have hp_eq : (primeOf (toLex (i, ν₁))).val = (primeOf (toLex (i, ν₂))).val :=
          Nat.cast_injective ((Real.rpow_left_inj (Nat.cast_nonneg _) (Nat.cast_nonneg _) hexp.ne').mp hr_eq)
        have hlex := hprime_inj (PNat.eq hp_eq)
        exact congrArg (fun x ↦ (ofLex x).2) hlex
    have hev_nz : ∀ᶠ p : ℝ in atTop, (M p).det ≠ 0 := by
      have hsc_nz : ∀ᶠ p : ℝ in atTop, (Mscaled p).det ≠ 0 :=
        hlim_det.eventually_ne hL_det_ne0
      filter_upwards [eventually_gt_atTop (0 : ℝ), hsc_nz] with p hp hdet_sc
      have hsc_eq : Mscaled p = M p * Matrix.diagonal (colScale p) := by
        ext ν j; simp [Mscaled, Matrix.mul_diagonal, mul_comm]
      rw [hsc_eq, Matrix.det_mul, Matrix.det_diagonal] at hdet_sc
      exact left_ne_zero_of_mul hdet_sc
    refine isUnit_iff_exists_inv.mpr ⟨Germ.ofFun (fun p ↦ ((M p).det)⁻¹), ?_⟩
    apply Germ.coe_eq.mpr
    filter_upwards [hev_nz] with p hp
    exact mul_inv_cancel₀ hp
  have hunit_det : IsUnit (MvPowerSeries.coeff mStar Jac.det) := by
    rw [hcoeff_det, hB_det]
    exact Finset.prod_induction _ (fun x ↦ IsUnit x) (fun _ _ ha hb ↦ ha.mul hb) isUnit_one
      (fun i _ ↦ hblock_unit i)
  have hnzd : Jac.det ∈ nonZeroDivisors (MvPowerSeries ι RayGerm) :=
    lex_nonZeroDivisor_of_unit Jac.det mStar hunit_det hmin
  have hindep : AlgebraicIndependent (Polynomial ℂ) fRestr :=
    independent_of_marked_jacobian_domain hpoly_inj id fRestr hnzd
  rw [algebraicIndependent_iff]
  intro Q₁ hQ₁
  apply (algebraicIndependent_iff.mp hindep) Q₁
  rw [← hrestr_alg Q₁, hQ₁, map_zero]

private theorem theta_d_dilations_diff_indep_dec {d : ℕ} (hd : 3 ≤ d)
    (P : AllDStokesProfile d hd) {s : ℕ} (a : Fin s → ℕ+)
    (hdec : ∀ i j : Fin s, i < j → (a j).val < (a i).val) :
    AlgebraicIndependent ℂ (dilationCoordinates d a) := by
  classical
  let A : ℕ := ∏ i : Fin s, (a i).val
  have hA_pos : 0 < A := Finset.prod_pos fun i _ ↦ (a i).property
  have hA_dvd : ∀ i : Fin s, (a i).val ∣ A := fun i ↦
    Finset.dvd_prod_of_mem (fun k ↦ (a k).val) (Finset.mem_univ i)
  let _ : Algebra (Polynomial ℂ) RayGerm := (polyToGerm d).toAlgebra
  rw [algebraicIndependent_iff]
  intro Q hQ_eval
  let J : ℕ := (Q.vars.sup fun u ↦ Option.elim' 0 (fun ij ↦ ij.2) u) + 1
  have hJ_pos : 0 < J := Nat.succ_pos _
  have hQ_vars : ∀ u ∈ Q.vars, ∀ ij : Fin s × ℕ, u = some ij → ij.2 < J := by
    intro u hu ij heq
    subst heq
    have hle : ij.2 ≤ Q.vars.sup (fun v ↦ Option.elim' 0 (fun p ↦ p.2) v) :=
      Finset.le_sup (f := fun v ↦ Option.elim' 0 (fun p ↦ p.2) v) hu
    omega
  let ι := Fin s ×ₗ Fin J
  let emb : Option ι → Option (Fin s × ℕ) :=
    Option.map fun r ↦ ((ofLex r).1, (ofLex r).2.val)
  let liftVar (u : Option (Fin s × ℕ)) : Option ι :=
    match u with
    | none => none
    | some (i, j) => if h : j < J then some (toLex (i, ⟨j, h⟩)) else none
  let Q₀ : MvPolynomial (Option ι) ℂ := MvPolynomial.rename liftVar Q
  have hQ_eq : MvPolynomial.rename emb Q₀ = Q := by
    rw [MvPolynomial.rename_rename]
    have hcongr : ∀ u ∈ Q.vars, emb (liftVar u) = u := by
      intro u hu
      cases u with
      | none => rfl
      | some ij =>
        simp only [liftVar, hQ_vars (some ij) hu ij rfl, ↓reduceDIte, emb, Option.map_some,
          ofLex_toLex]
    rw [MvPolynomial.rename_eq_aeval]
    have h1 : MvPolynomial.aeval (MvPolynomial.X (R := ℂ) ∘ (emb ∘ liftVar)) Q =
        MvPolynomial.aeval (MvPolynomial.X (R := ℂ)) Q := by
      simp only [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
      apply Finset.sum_congr rfl; intro m hm
      congr 1
      apply Finsupp.prod_congr; intro u hu
      have huQ : u ∈ Q.vars := (MvPolynomial.mem_vars_iff_mem_support u).mpr ⟨m, hm, hu⟩
      simp only [Function.comp_apply, hcongr u huQ]
    rw [h1]
    exact congrFun (congrArg DFunLike.coe (MvPolynomial.aeval_X_left (R := ℂ) (σ := Option (Fin s × ℕ)))) Q
  let Q₁ : MvPolynomial ι (Polynomial ℂ) := optionToPolyMv ι Q₀
  let fTracked : ι → TrackedExpansion d (2 * d) (dilKeyRate d A) :=
    fun r ↦ dilatedJetTracked hd P hA_pos (a (ofLex r).1) (hA_dvd (ofLex r).1) (ofLex r).2.val
  obtain ⟨E, hE_val, hE_marked⟩ := evalPolyMv_tracked hd hA_pos fTracked Q₁
  have hE_zero : ∀ᶠ p : ℝ in atTop, E.exp.value p = 0 := by
    have hall_f : ∀ᶠ p : ℝ in atTop, ∀ r : ι,
        (fTracked r).exp.value p =
          psValue (formalJet (thetaDDilated d (a (ofLex r).1).val) (ofLex r).2.val) (qRayD d p) :=
      ((Filter.eventually_all_finset (Finset.univ : Finset ι)).mpr fun r _ ↦
        dilatedJetTracked_value hd P hA_pos (a (ofLex r).1) (hA_dvd (ofLex r).1) (ofLex r).2.val).mono
        fun p hp r ↦ hp r (Finset.mem_univ r)
    filter_upwards [eventually_gt_atTop (0 : ℝ), hE_val, hall_f] with p hp hEv hfv
    rw [hEv]
    have hcongr_ev : MvPolynomial.eval₂ (Polynomial.evalRingHom (qRayD d p))
          (fun r ↦ (fTracked r).exp.value p) Q₁ =
        MvPolynomial.eval₂ (Polynomial.evalRingHom (qRayD d p))
          (fun r ↦ psValue (formalJet (thetaDDilated d (a (ofLex r).1).val) (ofLex r).2.val) (qRayD d p)) Q₁ := by
      congr 1; funext r; exact hfv r
    rw [hcongr_ev, eval₂_optionToPolyMv]
    let g_p : Option (Fin s × ℕ) → ℂ := fun u ↦ psValue (dilationCoordinates d a u) (qRayD d p)
    have hps_coord : Option.elim' (qRayD d p)
          (fun r ↦ psValue (formalJet (thetaDDilated d (a (ofLex r).1).val) (ofLex r).2.val) (qRayD d p)) =
        g_p ∘ emb := by
      funext u; cases u with
      | none => exact (ps_nome_abs (qRayD d p)).2.symm
      | some r => rfl
    have habs_coord : ∀ u : Option (Fin s × ℕ), PSAbsAt (dilationCoordinates d a u) (qRayD d p) := by
      rintro (_ | ⟨i, j⟩)
      · exact (ps_nome_abs (qRayD d p)).1
      · exact dilated_jet_abs d (a i).val j (qRayD_disk hp)
    rw [hps_coord, ← MvPolynomial.eval_rename emb g_p Q₀, hQ_eq]
    have hps := (ps_polynomial_value Q habs_coord).2
    rw [← hps, hQ_eval]
    simp [psValue, psTerm]
  have hmarked_zero : MvPolynomial.aeval (R := Polynomial ℂ) (fun r ↦ (fTracked r).marked) Q₁ = 0 := by
    rw [← hE_marked]
    exact E.marked_zero (by omega) hE_zero
  have hindep := dilated_marked_algIndep hd P hJ_pos a hdec
  have hQ₁_zero : Q₁ = 0 := (algebraicIndependent_iff.mp hindep) Q₁ hmarked_zero
  have hQ₀_zero : Q₀ = 0 := optionToPolyMv_injective ι (hQ₁_zero.trans (map_zero _).symm)
  rw [← hQ_eq, hQ₀_zero, map_zero]

/-! ### 7. Master Public All-`d` Theorems -/

/-- **All-`d` Same-Degree Dilations Differential Independence Theorem (`d ≥ 3`)**:
For EVERY `d ≥ 3` (odd and even, zero transcendental tilt), given `P : AllDStokesProfile d hd`
and ANY finite family of distinct positive integers `a : Fin s → ℕ+`, the dilated `d`-th power
theta series `{Θ_d(q^{a_1}), …, Θ_d(q^{a_s})}` are **jointly differentially independent** over
`ℂ(q)` (every nontrivial polynomial in `q` and finitely many `q`-derivatives of `Θ_d(q^{a_i})`
is nonzero). -/
theorem theta_d_dilations_diff_indep {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (dilationCoordinates d a) := by
  classical
  -- Sort `a` into strictly decreasing order via a permutation `π : Fin s ≃ Fin s`.
  let S : Finset ℕ := Finset.univ.image fun i : Fin s ↦ (a i).val
  have hcard : S.card = s := by
    rw [Finset.card_image_of_injective _ (fun _ _ h ↦ ha (PNat.eq h)), Finset.card_fin]
  let ord : Fin s ≃o S := S.orderIsoOfFin hcard
  have hex : ∀ k : Fin s, ∃ i : Fin s, (a i).val = (ord (Fin.rev k)).val := fun k ↦ by
    have hmem : (ord (Fin.rev k)).val ∈ S := (ord (Fin.rev k)).property
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    exact ⟨i, hi⟩
  let fπ : Fin s → Fin s := fun k ↦ Classical.choose (hex k)
  have hfπ_val (k : Fin s) : (a (fπ k)).val = (ord (Fin.rev k)).val := Classical.choose_spec (hex k)
  have hdec : ∀ i j : Fin s, i < j → (a (fπ j)).val < (a (fπ i)).val := by
    intro i j hij
    rw [hfπ_val i, hfπ_val j]
    exact ord.strictMono (Fin.rev_lt_rev.mpr hij)
  have hfπ_inj : Function.Injective fπ := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (hdec i j hlt).ne (by rw [hij])
    · exact (hdec j i hgt).ne (by rw [hij])
  let π : Fin s ≃ Fin s := Equiv.ofBijective fπ (Finite.injective_iff_bijective.mp hfπ_inj)
  have hindep_dec : AlgebraicIndependent ℂ (dilationCoordinates d (a ∘ π)) :=
    theta_d_dilations_diff_indep_dec hd P (a ∘ π) hdec
  let e : Option (Fin s × ℕ) ≃ Option (Fin s × ℕ) :=
    Equiv.optionCongr (π.prodCongr (Equiv.refl ℕ))
  have hcomp : dilationCoordinates d (a ∘ π) = dilationCoordinates d a ∘ e := by
    funext u; cases u <;> rfl
  rw [hcomp] at hindep_dec
  exact (algebraicIndependent_equiv' e rfl).mp hindep_dec

/-- Explicit specialization of `theta_d_dilations_diff_indep` to distinct `d`-th-power-free
positive integers `a_1, …, a_s`. -/
theorem theta_d_dfree_dilations_diff_indep {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) (_hdfree : ∀ i, RFree d (a i).val) :
    AlgebraicIndependent ℂ (dilationCoordinates d a) :=
  theta_d_dilations_diff_indep hd P a ha

/-- **All-`d` Marked-Wave Stokes Theorem (`d ≥ 3`)**:
For EVERY `d ≥ 3` (odd and even, zero transcendental tilt), given `P : AllDStokesProfile d hd`,
the `d`-th power theta series `Θ_d(q) = ∑_{n ≥ 0} q^{n^d}` satisfies **NO nontrivial algebraic
differential equation over `ℂ(q)`**. -/
theorem theta_d_marked_wave_non_ade {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd) :
    AlgebraicIndependent ℂ (thetaDCoordinates d) := by
  let a : Fin 1 → ℕ+ := fun _ ↦ 1
  have ha : Function.Injective a := fun i j _ ↦ Subsingleton.elim i j
  have h1 := theta_d_dilations_diff_indep hd P a ha
  let e : ℕ ≃ Option (Fin 1 × ℕ) :=
    { toFun := fun
        | 0 => none
        | j + 1 => some (0, j)
      invFun := fun
        | none => 0
        | some (_, j) => j + 1
      left_inv := fun
        | 0 => rfl
        | _ + 1 => rfl
      right_inv := fun
        | none => rfl
        | some (i, _) => by rw [Subsingleton.elim i 0] }
  have hcomp : dilationCoordinates d a ∘ e = thetaDCoordinates d := by
    funext n
    cases n with
    | zero => rfl
    | succ j => rfl
  exact (algebraicIndependent_equiv' e hcomp).mpr h1

/-- **All-`d` Waring Power Differential Transcendence Theorem (`d ≥ 3`, `k ≥ 1`)**:
For EVERY `d ≥ 3` and EVERY positive integer `k ≥ 1`, given `P : AllDStokesProfile d hd`,
the Waring power `Θ_d(q)^k` satisfies **NO nontrivial ADE over `ℂ(q)`**. -/
theorem theta_d_waring_power_non_ade {d : ℕ} (hd : 3 ≤ d) (P : AllDStokesProfile d hd)
    {k : ℕ} (hk : 1 ≤ k) :
    AlgebraicIndependent ℂ (waringCoordinates d k) :=
  waring_algebraicIndependent_of_base (thetaD d) hk (theta_d_marked_wave_non_ade hd P)

/-! ### 8. Unconditional `d = 3` Corollaries (Non-Vacuity Witness Instantiations) -/

/-- Unconditional `d = 3` differential transcendence of `Θ_3(q)` instantiated from the
all-`d` theorem via `stokesProfileThree` (ZERO external hypotheses!). -/
theorem theta_3_non_ade_via_allD :
    AlgebraicIndependent ℂ (thetaDCoordinates 3) :=
  theta_d_marked_wave_non_ade (by decide) stokesProfileThree

/-- **Unconditional** differential transcendence of ALL cubic Waring powers `Θ_3(q)^k` (`k ≥ 1`)! -/
theorem theta_3_waring_power_non_ade {k : ℕ} (hk : 1 ≤ k) :
    AlgebraicIndependent ℂ (waringCoordinates 3 k) :=
  theta_d_waring_power_non_ade (by decide) stokesProfileThree hk

/-- **Unconditional** joint differential independence of ALL finite families of distinct
same-degree cubic dilations `{Θ_3(q^{a_1}), …, Θ_3(q^{a_s})}`! -/
theorem theta_3_dilations_diff_indep {s : ℕ} (a : Fin s → ℕ+) (ha : Function.Injective a) :
    AlgebraicIndependent ℂ (dilationCoordinates 3 a) :=
  theta_d_dilations_diff_indep (by decide) stokesProfileThree a ha

end
end CubicTheta.AllD
