module

public import PakPrimes.FishburnStrongDTrans
public import PakPrimes.HigherOrderStokes
public import PakPrimes.PakYeliussizovEGF
public import PakPrimes.RiemannHypothesisStokes

/-! # Universal Strong `ℂ({w})` Lift for Higher-Order Rotated-Ray Borel–Stokes–Vandermonde

This module lifts the higher-order rotated-ray Borel–Stokes–Vandermonde engine
(`PakPrimes.HigherOrderStokes`) from rational coefficients `ℂ(u)` to the full field
`ℂ({w}) = FractionRing ConvergentPowerSeries` of **convergent meromorphic germs at `0`**
(matching Bostan–Di Vizio–Raschel, AJM 2024, Theorem 3, and Klazar 2003, without difference
Galois theory).

### Non-Circular Parameter Schedule
1. **Rotation Reduction (`θ₀ → 0`) over `ℂ{w}`**:
   Given `h : HigherOrderBorelData φ θ₀ ω ord pp`, set `μ := exp (I * θ₀)` (`‖μ‖ = 1`) and
   `φ_rot z := φ (μ * z)`. The convergent rescaling automorphism `rescaleConv μ` on `ℂ{w}`
   combined with the diagonal jet scaling `Y_j ↦ μ^{j+1} Y_j` reduces `formalEvalConv (formalSeries φ) Q = 0`
   to `formalEvalConv (formalSeries φ_rot) (rotConvPoly r μ Q) = 0` along `θ₀ = 0`, where
   injectivity follows from `triangular_aeval_injective`.
2. **Section 1 — Convergent-Germ Borel Transfer (`higherOrder_conv_borel_transfer`)**:
   On `θ₀ = 0`, fix `ε₀ := min h.ε (ω 0 / 2)`, flanking rays `d_± := exp (± I * h.θ)`, and
   star-shaped flanking wedges `wedgePlusH`, `wedgeMinusH`. Embedding every `a ∈ ℂ{w}` via
   `convMinor a` (entire exponential-type minor with zero Stokes jump) transfers
   `formalEvalConv (formalSeries φ) Q = 0` identically to both lateral Borel sums `g_pos`, `g_neg`.
3. **Section 2 — Higher-Order Stokes Jump & Lowest-`w`-Order Descent (`L_higher_conv`, `no_conv_ade_of_higher_order_borel`)**:
   For each pole `ω m` of order `ord m ≥ 1`, let `d_m := ord m - 1` and reverse the polynomial jet
   `Q_jet (polePolyH pp ord m) (ω m) j ∈ ℂ[u]` (degree `≤ d_m`) to
   `P_higher pp ord ω m j := revPolyH d_m (Q_jet (polePolyH pp ord m) (ω m) j) ∈ ℂ[w]`.
   Then:
   - `(P_higher pp ord ω m j).eval u⁻¹ * (u^{d_m} exp(-ω m * u)) = (Q_jet (polePolyH pp ord m) (ω m) j).eval u * exp(-ω m * u)`,
   - `(P_higher pp ord ω m j).coeff 0 = (polePolyH pp ord m).leadingCoeff * (-ω m)^j` with nonzero leading factor.
   Choosing minimal `Y`-total-degree `Qmin`, strong induction on `n < r + 1` kills all lower modes
   `m < n` by exact shift invariance, isolates `L_higher_conv pp ord ω r n Qmin = 0` via the
   Lipschitz + Taylor + exponential-flatness bridge (with `δ₀ := min (ω 0) (min_{n ≤ r} (ω (n+1) - ω n)/2) > 0`),
   and extracts `[w^{minNonConstWOrd Qmin}]` to obtain `D_freq r (ω n) (coeffW k₀ Qmin) = 0` for
   `r + 1` distinct frequencies, yielding the complex Vandermonde contradiction.
4. **Section 3 — Invertible Triangular `ℂ{t}` Transfers & Unconditional Flagships**:
   Proves `StronglyDTransOverConvergent` closure under addition and nonzero multiplication by
   `a ∈ ℂ{t}`, proves the `X * F → F` convergent triangular transfer, and derives strong
   D-transcendence over `ℂ({t})` for `formalSeries φ`, `ogfOfEGF E`, Bernoulli `bernOGF`,
   Tangent `tanOGF`, Secant `secOGF`, `sec²` / `sec^p`, general Briot–Bouquet `(1 - c e^{λξ})^{-p}`,
   Euler/Genocchi `(1 + e^ξ)^{-p}`, Trigamma / Lambert / Dirichlet-pole OGFs, and the RH-conditional
   critical-line series `G_Lambda` and `G_Lambda_laplace`.
-/

set_option maxHeartbeats 1600000

public section
namespace PakPrimes.HigherOrderStrongDTrans

open Complex Real Filter MeasureTheory Set MvPolynomial Matrix
open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes
  PakPrimes.FishburnStrongDTrans PakPrimes.PakYeliussizovEGF PakPrimes.HolderGamma
  PakPrimes.PrimeNome PakPrimes.RiemannHypothesisStokes
open scoped Topology Interval BigOperators

noncomputable section

/-! ### 1. Convergent-Germ Borel Transfer for `HigherOrderBorelData` (`θ₀ = 0`) -/

private def ε₀H {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : ℝ :=
  min h.ε (ω 0 / 2)

private lemma ε₀H_pos {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : 0 < ε₀H h :=
  lt_min h.hε_pos (half_pos h.ω_pos)

private lemma ε₀H_le_ε {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : ε₀H h ≤ h.ε :=
  min_le_left _ _

private lemma ε₀H_lt_ω {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) (m : ℕ) :
    ε₀H h < ω m :=
  lt_of_le_of_lt (min_le_right _ _)
    (lt_of_lt_of_le (half_lt_self h.ω_pos) (h.ω_mono.monotone (Nat.zero_le m)))

/-- Upper flanking ray `e^{i h.θ}` for unrotated `HigherOrderBorelData`. -/
@[expose] def dPlusH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : ℂ :=
  Complex.exp (I * (h.θ : ℂ))

/-- Lower flanking ray `e^{-i h.θ}` for unrotated `HigherOrderBorelData`. -/
@[expose] def dMinusH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) : ℂ :=
  Complex.exp (I * ((-h.θ : ℝ) : ℂ))

private lemma dPlusH_re {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (dPlusH h).re = Real.cos h.θ := by
  unfold dPlusH
  rw [show I * (h.θ : ℂ) = (h.θ : ℂ) * I by ring, Complex.exp_ofReal_mul_I_re]

private lemma dPlusH_im {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (dPlusH h).im = Real.sin h.θ := by
  unfold dPlusH
  rw [show I * (h.θ : ℂ) = (h.θ : ℂ) * I by ring, Complex.exp_ofReal_mul_I_im]

private lemma dMinusH_re {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (dMinusH h).re = Real.cos h.θ := by
  unfold dMinusH
  rw [show I * ((-h.θ : ℝ) : ℂ) = ((-h.θ : ℝ) : ℂ) * I by ring,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]

private lemma dMinusH_im {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (dMinusH h).im = -Real.sin h.θ := by
  unfold dMinusH
  rw [show I * ((-h.θ : ℝ) : ℂ) = ((-h.θ : ℝ) : ℂ) * I by ring,
    Complex.exp_ofReal_mul_I_im, Real.sin_neg]

private lemma norm_dPlusH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    ‖dPlusH h‖ = 1 := by
  unfold dPlusH
  rw [show I * (h.θ : ℂ) = (h.θ : ℂ) * I by ring]
  exact Complex.norm_exp_ofReal_mul_I h.θ

private lemma norm_dMinusH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    ‖dMinusH h‖ = 1 := by
  unfold dMinusH
  rw [show I * ((-h.θ : ℝ) : ℂ) = ((-h.θ : ℝ) : ℂ) * I by ring]
  exact Complex.norm_exp_ofReal_mul_I (-h.θ)

private lemma cos_pos_θH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    0 < Real.cos h.θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [h.hθ_pos, Real.pi_pos], lt_trans h.hθ_lt h.hα₀_lt⟩

private lemma sin_pos_θH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    0 < Real.sin h.θ :=
  Real.sin_pos_of_pos_of_lt_pi h.hθ_pos (by linarith [h.hθ_lt, h.hα₀_lt, Real.pi_pos])

private lemma tan_pos_of_memH {x : ℝ} (hx0 : 0 < x) (hx1 : x < Real.pi / 2) : 0 < Real.tan x :=
  Real.tan_pos_of_pos_of_lt_pi_div_two hx0 hx1

private lemma tan_lt_tanH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    Real.tan h.θ < Real.tan h.α₀ :=
  Real.strictMonoOn_tan ⟨by linarith [h.hθ_pos, Real.pi_pos], lt_trans h.hθ_lt h.hα₀_lt⟩
    ⟨by linarith [h.hθ_pos, h.hθ_lt, Real.pi_pos], h.hα₀_lt⟩ h.hθ_lt

private lemma rotatedPuncturedWedge_zero_eq (α₀ ε : ℝ) (ω : ℕ → ℝ) :
    rotatedPuncturedWedge 0 α₀ ε ω = puncturedWedge α₀ ε ω := by
  ext z; simp [rotatedPuncturedWedge]

private def wedgePlusH (α₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.im < Real.tan α₀ * z.re}

private def wedgeMinusH (α₀ ε : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ε ∪ {z : ℂ | 0 < z.re ∧ z.im < 0 ∧ -(Real.tan α₀ * z.re) < z.im}

private lemma wedgePlusH_domain (α₀ : ℝ) {ε : ℝ} (hε : 0 < ε) : Domain (wedgePlusH α₀ ε) := by
  refine ⟨Metric.isOpen_ball.union ?_, fun z hz t ht => ?_⟩
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt continuous_const Complex.continuous_im).inter
        (isOpen_lt Complex.continuous_im (continuous_const.mul Complex.continuous_re)))
  · rcases hz with hball | ⟨hre, him, hlt⟩
    · left
      rw [Metric.mem_ball, dist_zero_right] at hball ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hball
    · rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · left; simpa [Metric.mem_ball] using hε
      · right
        refine ⟨by simp [Complex.mul_re]; exact mul_pos ht0 hre,
                by simp [Complex.mul_im]; exact mul_pos ht0 him, ?_⟩
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, add_zero]
        nlinarith

private lemma wedgeMinusH_domain (α₀ : ℝ) {ε : ℝ} (hε : 0 < ε) : Domain (wedgeMinusH α₀ ε) := by
  refine ⟨Metric.isOpen_ball.union ?_, fun z hz t ht => ?_⟩
  · exact (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_im continuous_const).inter
        (isOpen_lt (continuous_const.mul Complex.continuous_re).neg Complex.continuous_im))
  · rcases hz with hball | ⟨hre, him, hlt⟩
    · left
      rw [Metric.mem_ball, dist_zero_right] at hball ⊢
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg z) ht.2).trans_lt hball
    · rcases eq_or_lt_of_le ht.1 with rfl | ht0
      · left; simpa [Metric.mem_ball] using hε
      · right
        refine ⟨by simp [Complex.mul_re]; exact mul_pos ht0 hre,
                by simp [Complex.mul_im]; exact mul_neg_of_pos_of_neg ht0 him, ?_⟩
        simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero, add_zero]
        nlinarith

private lemma isPreconnected_of_starH {U : Set ℂ} (hU : Domain U) (h0 : (0 : ℂ) ∈ U) :
    IsPreconnected U := by
  refine isPreconnected_iff_subset_of_disjoint_closed.mpr fun s t hs ht hUst hst => ?_
  have hseg : ∀ z ∈ U, (z ∈ s ↔ (0 : ℂ) ∈ s) := fun z hz => by
    let γ : ℝ → ℂ := fun r => (r : ℂ) * z
    have hγ_cont : Continuous γ := Complex.continuous_ofReal.mul continuous_const
    have hγ_sub : γ '' Icc (0 : ℝ) 1 ⊆ U := by
      rintro w ⟨r, hr, rfl⟩; exact hU.star z hz r hr
    have hconn : IsPreconnected (γ '' Icc (0 : ℝ) 1) :=
      (isPreconnected_Icc).image γ hγ_cont.continuousOn
    have hsub_empty : (γ '' Icc (0 : ℝ) 1) ∩ (s ∩ t) = ∅ :=
      Set.subset_empty_iff.mp ((Set.inter_subset_inter_left _ hγ_sub).trans hst.subset)
    have hsplit := isPreconnected_iff_subset_of_disjoint_closed.mp hconn s t hs ht
      (hγ_sub.trans hUst) hsub_empty
    have h0im : (0 : ℂ) ∈ γ '' Icc (0 : ℝ) 1 := ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [γ]⟩
    have hzim : z ∈ γ '' Icc (0 : ℝ) 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, by simp [γ]⟩
    rcases hsplit with hsub_s | hsub_t
    · exact ⟨fun _ => hsub_s h0im, fun _ => hsub_s hzim⟩
    · have h0t : (0 : ℂ) ∈ t := hsub_t h0im
      have hzt : z ∈ t := hsub_t hzim
      exact ⟨fun hzs => by have hm : z ∈ U ∩ (s ∩ t) := ⟨hz, hzs, hzt⟩; rw [hst] at hm; exact hm.elim,
             fun h0s => by have hm : (0 : ℂ) ∈ U ∩ (s ∩ t) := ⟨h0, h0s, h0t⟩; rw [hst] at hm; exact hm.elim⟩
  rcases hUst h0 with h0s | h0t
  · left; intro z hz; exact (hseg z hz).mpr h0s
  · right; intro z hz
    rcases hUst hz with hzs | hzt
    · exfalso
      have h0s : (0 : ℂ) ∈ s := (hseg z hz).mp hzs
      have hm : (0 : ℂ) ∈ U ∩ (s ∩ t) := ⟨h0, h0s, h0t⟩
      rw [hst] at hm; exact hm
    · exact hzt

private lemma wedgePlusH_containsRay {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    ContainsRay (wedgePlusH h.α₀ (ε₀H h)) (dPlusH h) := fun v hv => by
  rcases eq_or_lt_of_le hv with rfl | hv0
  · left; simp [ε₀H_pos h]
  · right
    have hre : (dPlusH h * (v : ℂ)).re = Real.cos h.θ * v := by simp [dPlusH_re h, Complex.mul_re]
    have him : (dPlusH h * (v : ℂ)).im = Real.sin h.θ * v := by simp [dPlusH_im h, Complex.mul_im]
    refine ⟨by rw [hre]; exact mul_pos (cos_pos_θH h) hv0,
            by rw [him]; exact mul_pos (sin_pos_θH h) hv0, ?_⟩
    rw [hre, him]
    have htan : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
      rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θH h).ne']
    rw [htan]
    nlinarith [tan_lt_tanH h, mul_pos (cos_pos_θH h) hv0]

private lemma wedgeMinusH_containsRay {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    ContainsRay (wedgeMinusH h.α₀ (ε₀H h)) (dMinusH h) := fun v hv => by
  rcases eq_or_lt_of_le hv with rfl | hv0
  · left; simp [ε₀H_pos h]
  · right
    have hre : (dMinusH h * (v : ℂ)).re = Real.cos h.θ * v := by simp [dMinusH_re h, Complex.mul_re]
    have him : (dMinusH h * (v : ℂ)).im = -(Real.sin h.θ * v) := by simp [dMinusH_im h, Complex.mul_im]
    refine ⟨by rw [hre]; exact mul_pos (cos_pos_θH h) hv0,
            by rw [him]; exact neg_lt_zero.mpr (mul_pos (sin_pos_θH h) hv0), ?_⟩
    rw [hre, him]
    have htan : Real.sin h.θ = Real.tan h.θ * Real.cos h.θ := by
      rw [Real.tan_eq_sin_div_cos, div_mul_cancel₀ _ (cos_pos_θH h).ne']
    rw [htan]
    nlinarith [tan_lt_tanH h, mul_pos (cos_pos_θH h) hv0]

private lemma wedgePlusH_subset_punctured {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    wedgePlusH h.α₀ (ε₀H h) ⊆ rotatedPuncturedWedge 0 h.α₀ h.ε ω := by
  rw [rotatedPuncturedWedge_zero_eq]
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hball | ⟨hre, him, hlt⟩
    · left; rw [Metric.mem_ball] at hball ⊢; exact hball.trans_le (ε₀H_le_ε h)
    · right; exact ⟨hre, by rw [abs_of_pos him]; exact hlt⟩
  · rintro ⟨m, rfl⟩
    rcases hz with hball | ⟨_, him, _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))).le] at hball
      linarith [ε₀H_lt_ω h m]
    · simp at him

private lemma wedgeMinusH_subset_punctured {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    wedgeMinusH h.α₀ (ε₀H h) ⊆ rotatedPuncturedWedge 0 h.α₀ h.ε ω := by
  rw [rotatedPuncturedWedge_zero_eq]
  intro z hz
  refine ⟨?_, ?_⟩
  · rcases hz with hball | ⟨hre, him, hlt⟩
    · left; rw [Metric.mem_ball] at hball ⊢; exact hball.trans_le (ε₀H_le_ε h)
    · right; exact ⟨hre, by rw [abs_of_neg him]; linarith⟩
  · rintro ⟨m, rfl⟩
    rcases hz with hball | ⟨_, him, _⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real,
        Real.norm_of_nonneg (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))).le] at hball
      linarith [ε₀H_lt_ω h m]
    · simp at him

/-- The higher-order Borel minor `⟨0, φ⟩`. -/
@[expose] def aPhiH (φ : ℂ → ℂ) : Minor := ⟨0, φ⟩

private lemma aPhiH_toSeries (φ : ℂ → ℂ) : (aPhiH φ).toSeries = formalSeries φ := rfl

private lemma aPhiH_good_plus {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (aPhiH φ).Good (wedgePlusH h.α₀ (ε₀H h)) (dPlusH h) :=
  ⟨h.analyticOn.mono (wedgePlusH_subset_punctured h), by simpa [aPhiH, dPlusH] using h.expType_plus⟩

private lemma aPhiH_good_minus {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) :
    (aPhiH φ).Good (wedgeMinusH h.α₀ (ε₀H h)) (dMinusH h) :=
  ⟨h.analyticOn.mono (wedgeMinusH_subset_punctured h), by simpa [aPhiH, dMinusH] using h.expType_minus⟩

private inductive ConvBorelExprH where
  | conv (a : ConvergentPowerSeries)
  | leaf
  | add (e f : ConvBorelExprH)
  | mul (e f : ConvBorelExprH)
  | jet (e : ConvBorelExprH)

private def ConvBorelExprH.residual (a : Minor) : ConvBorelExprH → Minor
  | .conv c => convMinor c
  | .leaf => a
  | .add e f => (e.residual a).plus (f.residual a)
  | .mul e f => (e.residual a).times (f.residual a)
  | .jet e => (e.residual a).jet

private def ConvBorelExprH.eval (a : Minor) (d : ℂ) : ConvBorelExprH → ℂ → ℂ
  | .conv c => fun p => evalConv c p⁻¹
  | .leaf => a.value d
  | .add e f => fun p => e.eval a d p + f.eval a d p
  | .mul e f => fun p => e.eval a d p * f.eval a d p
  | .jet e => fun p => deriv (e.eval a d) p

private def ConvBorelExprH.ofBorel : BorelExpr → ConvBorelExprH
  | .const c => .conv (convC c)
  | .leaf => .leaf
  | .add e f => .add (ofBorel e) (ofBorel f)
  | .mul e f => .mul (ofBorel e) (ofBorel f)
  | .jet e => .jet (ofBorel e)

private lemma ConvBorelExprH.ofBorel_eval (e : BorelExpr) (a : Minor) (d : ℂ) :
    (ofBorel e).eval a d = e.eval a d := by
  induction e with
  | const c => funext p; simp [ofBorel, eval, BorelExpr.eval, evalConv_C]
  | leaf => rfl
  | add e f he hf => funext p; simp [ofBorel, eval, BorelExpr.eval, he, hf]
  | mul e f he hf => funext p; simp [ofBorel, eval, BorelExpr.eval, he, hf]
  | jet e he => funext p; simp [ofBorel, eval, BorelExpr.eval, he]

private lemma ConvBorelExprH.ofBorel_jetIter (j : ℕ) :
    ofBorel (Nat.iterate BorelExpr.jet j BorelExpr.leaf) = Nat.iterate .jet j .leaf := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ofBorel, ih]

private lemma ConvBorelExprH.represents (e : ConvBorelExprH) {U : Set ℂ} {d : ℂ} (hU : Domain U)
    (ray : ContainsRay U d) {a : Minor} (ha : a.Good U d) :
    (e.residual a).Good U d ∧ e.eval a d =ᶠ[BorelStokesVandermonde.far d] (e.residual a).value d := by
  induction e with
  | conv c =>
    refine ⟨convMinor_good c U d, ?_⟩
    filter_upwards [convMinor_value_eventually c d] with p hp
    exact hp.symm
  | leaf => exact ⟨ha, .rfl⟩
  | add e f he hf =>
    refine ⟨he.1.plus hf.1, ?_⟩
    filter_upwards [he.2, hf.2, Minor.good_plus_value ray he.1 hf.1] with p hp hq h
    simp only [residual, eval, h, hp, hq]
  | mul e f he hf =>
    refine ⟨he.1.times hU hf.1, ?_⟩
    filter_upwards [he.2, hf.2, Minor.good_times_value ray hU he.1 hf.1] with p hp hq h
    simp only [residual, eval, h, hp, hq]
  | jet e he =>
    refine ⟨he.1.jet, ?_⟩
    obtain ⟨R, hR⟩ := eventually_atTop.mp (eventually_comap.mp he.2)
    filter_upwards [eventually_bound_far d R, Minor.good_jet_derivative ray he.1] with p hp h
    have loc : e.eval a d =ᶠ[𝓝 p] (e.residual a).value d := by
      filter_upwards [(isOpen_lt continuous_const (Complex.continuous_re.comp
        (continuous_id.mul_const d))).mem_nhds hp] with q hq
      exact hR _ (le_of_lt hq) q rfl
    simp only [eval, residual, loc.deriv_eq, h.deriv]

private lemma ConvBorelExprH.exists_of_mvPoly {r : ℕ}
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) :
    ∃ e : ConvBorelExprH,
      (∀ (U : Set ℂ) (d : ℂ) (a : Minor), Domain U → ContainsRay U d → a.Good U d →
        (e.residual a).toSeries = formalEvalConv a.toSeries Q) ∧
      (∀ (U : Set ℂ) (d : ℂ) (a : Minor), Domain U → ContainsRay U d → a.Good U d → 0 < d.re →
        ∀ᶠ u : ℝ in atTop,
          e.eval a d (u : ℂ) =
            MvPolynomial.eval
              (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => a.value d (t : ℂ)) u)
              (evalConvMvPoly Q (u : ℂ)⁻¹)) := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
    refine ⟨.conv c, fun _ _ _ _ _ _ => by simp [residual, formalEvalConv, convMinor_toSeries],
      fun _ _ _ _ _ _ _ => .of_forall fun u => by simp [eval, evalConvMvPoly_C]⟩
  | add Q₁ Q₂ h₁ h₂ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    obtain ⟨e₂, hs₂, he₂⟩ := h₂
    refine ⟨.add e₁ e₂, fun U d a hU ray ha => ?_, fun U d a hU ray ha hd => ?_⟩
    · have hg₁ := (e₁.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      have hg₂ := (e₂.represents hU ray ha).1.1 0 (by simpa using ray 0 le_rfl)
      rw [residual, Minor.toSeries_plus hg₁ hg₂, hs₁ U d a hU ray ha, hs₂ U d a hU ray ha,
        formalEvalConv, formalEvalConv, formalEvalConv, MvPolynomial.eval₂_add]
    · filter_upwards [he₁ U d a hU ray ha hd, he₂ U d a hU ray ha hd,
        evalConvMvPoly_add_eventually Q₁ Q₂] with u hu₁ hu₂ hadd
      simp only [eval, hu₁, hu₂, hadd, map_add]
  | mul_X Q₁ j h₁ =>
    obtain ⟨e₁, hs₁, he₁⟩ := h₁
    let ej : ConvBorelExprH := Nat.iterate ConvBorelExprH.jet j.val ConvBorelExprH.leaf
    refine ⟨.mul e₁ ej, fun U d a hU ray ha => ?_, fun U d a hU ray ha hd => ?_⟩
    · have h0 : (0 : ℂ) ∈ U := by simpa using ray 0 le_rfl
      have hg₁ := (e₁.represents hU ray ha).1.1 0 h0
      have hgj := (ej.represents hU ray ha).1.1 0 h0
      rw [residual, Minor.toSeries_times hg₁ hgj, hs₁ U d a hU ray ha]
      have hj_ser : ∀ k : ℕ, ((Nat.iterate ConvBorelExprH.jet k ConvBorelExprH.leaf).residual a).toSeries =
          d_u^[k] a.toSeries := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih =>
          have hgk := ((Nat.iterate ConvBorelExprH.jet k ConvBorelExprH.leaf).represents hU ray ha).1.1 0 h0
          rw [Function.iterate_succ_apply' ConvBorelExprH.jet k ConvBorelExprH.leaf,
            Function.iterate_succ_apply' d_u k a.toSeries]
          exact (Minor.toSeries_jet hgk).trans (congrArg d_u ih)
      rw [hj_ser j.val, formalEvalConv, formalEvalConv, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    · have hjet_eq := (BorelExpr.jetIter_eval_eq_iteratedDeriv a hU ray ha hd j.val).1
      filter_upwards [he₁ U d a hU ray ha hd, hjet_eq] with u hu₁ huj
      have heval_eq : ej.eval a d (u : ℂ) =
          (Nat.iterate BorelExpr.jet j.val BorelExpr.leaf).eval a d (u : ℂ) := by
        dsimp only [ej]; rw [← ofBorel_jetIter, ofBorel_eval]
      simp only [eval, evalConvMvPoly_mul_X, map_mul, MvPolynomial.eval_X]
      rw [heval_eq, hu₁, huj]

private lemma analyticOnNhd_eqOn_zero_of_iteratedDeriv_zeroH {U : Set ℂ} {f : ℂ → ℂ}
    (hpre : IsPreconnected U) (h0 : (0 : ℂ) ∈ U) (hf : AnalyticOnNhd ℂ f U)
    (hderiv : ∀ k : ℕ, iteratedDeriv k f 0 = 0) : Set.EqOn f 0 U := by
  refine hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre h0 ?_
  by_contra hne
  obtain ⟨n, g, hg, hg0, hfac⟩ := (hf 0 h0).exists_eventuallyEq_pow_smul_ne_zero_iff.mpr hne
  have hloc : f =ᶠ[𝓝 (0 : ℂ)] fun z => z ^ n * g z := by
    filter_upwards [hfac] with z hz; simpa [smul_eq_mul] using hz
  have hdn : iteratedDeriv n f 0 = (n.factorial : ℂ) * g 0 := by
    rw [hloc.iteratedDeriv_eq n]
    have hpow_an : AnalyticAt ℂ (fun z : ℂ => z ^ n) 0 := analyticAt_id.pow n
    have hmul := iteratedDeriv_fun_mul (n := n) (x := (0 : ℂ)) hpow_an.contDiffAt hg.contDiffAt
    rw [hmul]
    have hterm : ∀ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i (fun z : ℂ => z ^ n) (0 : ℂ) * iteratedDeriv (n - i) g 0 =
          if i = n then (n.factorial : ℂ) * g 0 else 0 := fun i _ => by
      rw [iteratedDeriv_fun_pow_zero]
      split_ifs with hin
      · subst hin; simp [Nat.choose_self]
      · simp
    rw [Finset.sum_congr rfl hterm]; simp
  have hzero := hderiv n
  rw [hdn] at hzero
  exact (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero n) hg0) hzero

/-- **Section 1 — Convergent-Germ Higher-Order Borel Transfer (`θ₀ = 0`)**:
If `Q ∈ ℂ{w}[Y_0, ..., Y_r]` annihilates `formalSeries φ`, then `evalConvMvPoly Q u⁻¹`
annihilates BOTH lateral Borel sums `g_pos` and `g_neg` eventually as `u → +∞`. -/
theorem higherOrder_conv_borel_transfer {φ ω ord pp}
    (h : HigherOrderBorelData φ 0 ω ord pp)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries φ) Q = 0) :
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ)) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) ∧
    (∀ᶠ u : ℝ in atTop,
      MvPolynomial.eval
        (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (aPhiH φ).value (dMinusH h) (t : ℂ)) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) := by
  let Up := wedgePlusH h.α₀ (ε₀H h)
  let Um := wedgeMinusH h.α₀ (ε₀H h)
  have hUp_dom : Domain Up := wedgePlusH_domain h.α₀ (ε₀H_pos h)
  have hUm_dom : Domain Um := wedgeMinusH_domain h.α₀ (ε₀H_pos h)
  have hrayP : ContainsRay Up (dPlusH h) := wedgePlusH_containsRay h
  have hrayM : ContainsRay Um (dMinusH h) := wedgeMinusH_containsRay h
  have hgoodP : (aPhiH φ).Good Up (dPlusH h) := aPhiH_good_plus h
  have hgoodM : (aPhiH φ).Good Um (dMinusH h) := aPhiH_good_minus h
  have hreP : 0 < (dPlusH h).re := by rw [dPlusH_re h]; exact cos_pos_θH h
  have hreM : 0 < (dMinusH h).re := by rw [dMinusH_re h]; exact cos_pos_θH h
  obtain ⟨e, hs, he⟩ := ConvBorelExprH.exists_of_mvPoly Q
  have hres_series : (e.residual (aPhiH φ)).toSeries = 0 := by
    rw [hs Up (dPlusH h) (aPhiH φ) hUp_dom hrayP hgoodP, aPhiH_toSeries, hQ]
  have hatom : (e.residual (aPhiH φ)).atom = 0 := by
    have := congrArg (PowerSeries.coeff 0) hres_series; simpa [Minor.toSeries] using this
  have hderiv_zero : ∀ k : ℕ, iteratedDeriv k (e.residual (aPhiH φ)).density 0 = 0 := fun k => by
    have := congrArg (PowerSeries.coeff (k + 1)) hres_series; simpa [Minor.toSeries] using this
  have h0P : (0 : ℂ) ∈ Up := by simpa using hrayP 0 le_rfl
  have h0M : (0 : ℂ) ∈ Um := by simpa using hrayM 0 le_rfl
  have hplus_dens : Set.EqOn (e.residual (aPhiH φ)).density 0 Up :=
    analyticOnNhd_eqOn_zero_of_iteratedDeriv_zeroH (isPreconnected_of_starH hUp_dom h0P) h0P
      (e.represents hUp_dom hrayP hgoodP).1.1 hderiv_zero
  have hminus_dens : Set.EqOn (e.residual (aPhiH φ)).density 0 Um :=
    analyticOnNhd_eqOn_zero_of_iteratedDeriv_zeroH (isPreconnected_of_starH hUm_dom h0M) h0M
      (e.represents hUm_dom hrayM hgoodM).1.1 hderiv_zero
  constructor
  · have hrep := (tendsto_coe_far hreP).eventually (e.represents hUp_dom hrayP hgoodP).2
    filter_upwards [hrep, he Up (dPlusH h) (aPhiH φ) hUp_dom hrayP hgoodP hreP] with u hu_rep hu_ev
    rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
    refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
    simp [damped, Minor.pull, hplus_dens (hrayP v hv.le)]
  · have hrep := (tendsto_coe_far hreM).eventually (e.represents hUm_dom hrayM hgoodM).2
    filter_upwards [hrep, he Um (dMinusH h) (aPhiH φ) hUm_dom hrayM hgoodM hreM] with u hu_rep hu_ev
    rw [← hu_ev, hu_rep, Minor.value, hatom, zero_add]
    refine setIntegral_eq_zero_of_forall_eq_zero fun v hv => ?_
    simp [damped, Minor.pull, hminus_dens (hrayM v hv.le)]

private lemma minor_value_hasAsympExpH (a : Minor) {U : Set ℂ} {d : ℂ}
    (hU : Domain U) (ray : ContainsRay U d) (ha : a.Good U d) (hd : 0 < d.re) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun t : ℝ => a.value d (t : ℂ))) (d_u^[j] a.toSeries) := by
  let ej : BorelExpr := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  obtain ⟨good_j, rep_j⟩ := ej.represents hU ray ha
  have hjet_eq := (BorelExpr.jetIter_eval_eq_iteratedDeriv a hU ray ha hd j).1
  have hser_j : (ej.residual a).toSeries = d_u^[j] a.toSeries := by
    have h0 : (0 : ℂ) ∈ U := by simpa using ray 0 le_rfl
    clear good_j rep_j hjet_eq
    induction j with
    | zero => rfl
    | succ k ih =>
      have hgk := ((Nat.iterate BorelExpr.jet k BorelExpr.leaf).represents hU ray ha).1.1 0 h0
      dsimp only [ej]
      rw [Function.iterate_succ_apply' BorelExpr.jet k BorelExpr.leaf,
        Function.iterate_succ_apply' d_u k a.toSeries]
      exact (Minor.toSeries_jet hgk).trans (congrArg d_u ih)
  intro M
  cases M with
  | zero =>
    obtain ⟨C, _, hC⟩ := Minor.value_asymptotic (ej.residual a) hU ray good_j hd 0
    refine ⟨C + ‖(ej.residual a).atom‖, ?_⟩
    filter_upwards [hC, hjet_eq, (tendsto_coe_far hd).eventually rep_j,
      eventually_ge_atTop (1 : ℝ)] with u hu hje hre hu1
    simp only [Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero, div_one]
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, zero_add, pow_one] at hu
    rw [← hje, hre]
    have h1 : ‖(ej.residual a).value d (u : ℂ)‖ ≤
        ‖(ej.residual a).value d (u : ℂ) - (ej.residual a).atom‖ + ‖(ej.residual a).atom‖ := by
      simpa [sub_add_cancel] using
        norm_add_le ((ej.residual a).value d (u : ℂ) - (ej.residual a).atom) (ej.residual a).atom
    have hC0 : 0 ≤ C := by
      have hnn := norm_nonneg ((ej.residual a).value d (u : ℂ) - (ej.residual a).atom)
      exact (div_nonneg_iff.mp (hnn.trans hu)).resolve_right (fun h => by linarith) |>.1
    have hCu : C / u ≤ C := by
      calc C / u ≤ C / 1 := div_le_div_of_nonneg_left hC0 zero_lt_one hu1
        _ = C := div_one C
    linarith
  | succ m =>
    obtain ⟨C, _, hC⟩ := Minor.value_asymptotic (ej.residual a) hU ray good_j hd m
    refine ⟨C, ?_⟩
    filter_upwards [hC, hjet_eq, (tendsto_coe_far hd).eventually rep_j] with u hu hje hre
    rw [← hje, hre]
    have hsum : ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (d_u^[j] a.toSeries) * ((u : ℂ)⁻¹ ^ k) =
        (ej.residual a).atom + ∑ k ∈ Finset.range m,
          iteratedDeriv k (ej.residual a).density 0 * ((u : ℂ)⁻¹ ^ (k + 1)) := by
      rw [← hser_j, Finset.sum_range_succ']
      simp only [Minor.toSeries, PowerSeries.coeff_mk, pow_zero, mul_one, add_comm]
    rw [hsum]
    exact hu

private lemma lateral_hasAsympExpH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ)))
      (d_u^[j] (formalSeries φ)) := by
  simpa [aPhiH_toSeries] using minor_value_hasAsympExpH (aPhiH φ)
    (wedgePlusH_domain h.α₀ (ε₀H_pos h)) (wedgePlusH_containsRay h) (aPhiH_good_plus h)
    (by rw [dPlusH_re h]; exact cos_pos_θH h) j

private lemma formalEvalConv_eq_zero_of_exp_smallH {r : ℕ} {S : PowerSeries ℂ} {g : ℝ → ℂ}
    (hg : ∀ j : ℕ, HasAsympExp (iteratedDeriv j g) (d_u^[j] S))
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) {δ C : ℝ} (hδ : 0 < δ)
    (hbd : ∀ᶠ u : ℝ in atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g u)
        (evalConvMvPoly Q (u : ℂ)⁻¹)‖ ≤ C * Real.exp (-δ * u)) :
    formalEvalConv S Q = 0 := by
  have hexp : HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g u)
        (evalConvMvPoly Q (u : ℂ)⁻¹))
      (formalEvalConv S Q) :=
    HasAsympExp.mvPolynomial_evalConv (fun j => hg j.val) Q
  refine hexp.eq_zero_of_flat fun M => ?_
  refine ⟨max C 0 * ((M.factorial : ℝ) / δ ^ M), ?_⟩
  filter_upwards [hbd, eventually_gt_atTop (0 : ℝ)] with u hu hu0
  have hpow := Real.pow_div_factorial_le_exp (δ * u) (mul_nonneg hδ.le hu0.le) M
  have hfac : 0 < (M.factorial : ℝ) := by positivity
  have hδM : 0 < δ ^ M := pow_pos hδ M
  have huM : 0 < u ^ M := pow_pos hu0 M
  have hexp_le : Real.exp (-δ * u) ≤ (M.factorial : ℝ) / (δ ^ M * u ^ M) := by
    rw [neg_mul, Real.exp_neg, le_div_iff₀ (mul_pos hδM huM), inv_mul_eq_div,
      div_le_iff₀ (Real.exp_pos _)]
    rw [mul_pow, div_le_iff₀ hfac] at hpow
    linarith
  calc ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g u)
          (evalConvMvPoly Q (u : ℂ)⁻¹)‖
      ≤ C * Real.exp (-δ * u) := hu
    _ ≤ max C 0 * Real.exp (-δ * u) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max C 0 * ((M.factorial : ℝ) / (δ ^ M * u ^ M)) :=
        mul_le_mul_of_nonneg_left hexp_le (le_max_right _ _)
    _ = (max C 0 * ((M.factorial : ℝ) / δ ^ M)) / u ^ M := by ring

/-! ### 2. Higher-Order Stokes Jump & Lowest-`w`-Order Vandermonde Descent over `ℂ{w}` -/

/-! #### 2A. Higher-Order Triangle Residue Formula & Stokes Jump Expansion (`θ₀ = 0`) -/

private def TriBdIntegrableH (F : ℂ → ℂ) (R m : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) volume 0 R ∧
  IntervalIntegrable (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) volume (-m * R) (m * R) ∧
  IntervalIntegrable (fun x : ℝ => (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) volume 0 R

private lemma triIntegral_addH {F G : ℂ → ℂ} {R m : ℝ}
    (hF : TriBdIntegrableH F R m) (hG : TriBdIntegrableH G R m) :
    triIntegral (fun z => F z + G z) R m = triIntegral F R m + triIntegral G R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (F ((x : ℂ) * (1 - I * (m : ℂ))) +
      G ((x : ℂ) * (1 - I * (m : ℂ))))) = fun x : ℝ =>
      (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ))) +
      (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))) := by funext x; ring
  have h2 : (fun x : ℝ => (1 + I * (m : ℂ)) * (F ((x : ℂ) * (1 + I * (m : ℂ))) +
      G ((x : ℂ) * (1 + I * (m : ℂ))))) = fun x : ℝ =>
      (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ))) +
      (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))) := by funext x; ring
  rw [h1, h2, intervalIntegral.integral_add hF.1 hG.1,
    intervalIntegral.integral_add hF.2.1 hG.2.1,
    intervalIntegral.integral_add hF.2.2 hG.2.2]
  ring

private lemma triIntegral_const_mulH (c : ℂ) (F : ℂ → ℂ) (R m : ℝ) :
    triIntegral (fun z => c * F z) R m = c * triIntegral F R m := by
  unfold triIntegral
  have h1 : (fun x : ℝ => (1 - I * (m : ℂ)) * (c * F ((x : ℂ) * (1 - I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) := by funext x; ring
  have h2 : (fun x : ℝ => (1 + I * (m : ℂ)) * (c * F ((x : ℂ) * (1 + I * (m : ℂ))))) =
      fun x : ℝ => c * ((1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) := by funext x; ring
  rw [h1, h2, intervalIntegral.integral_const_mul c, intervalIntegral.integral_const_mul c,
    intervalIntegral.integral_const_mul c]
  ring

private lemma triIntegral_sumH {ι : Type*} (s : Finset ι) (F : ι → ℂ → ℂ) (R m : ℝ)
    (hF : ∀ i ∈ s, TriBdIntegrableH (F i) R m) :
    triIntegral (fun z => ∑ i ∈ s, F i z) R m = ∑ i ∈ s, triIntegral (F i) R m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [triIntegral]
  | @insert i s hi ih =>
    have hFi : TriBdIntegrableH (F i) R m := hF i (Finset.mem_insert_self i s)
    have hFs : ∀ j ∈ s, TriBdIntegrableH (F j) R m := fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have hsum_int : TriBdIntegrableH (fun z => ∑ j ∈ s, F j z) R m := by
      refine ⟨?_, ?_, ?_⟩
      · have heq : (fun x : ℝ => (1 - I * (m : ℂ)) * ∑ j ∈ s, F j ((x : ℂ) * (1 - I * (m : ℂ)))) =
            ∑ j ∈ s, fun x : ℝ => (1 - I * (m : ℂ)) * F j ((x : ℂ) * (1 - I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).1
      · have heq : (fun y : ℝ => ∑ j ∈ s, F j ((R : ℂ) + (y : ℂ) * I)) =
            ∑ j ∈ s, fun y : ℝ => F j ((R : ℂ) + (y : ℂ) * I) := by
          funext y; rw [Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).2.1
      · have heq : (fun x : ℝ => (1 + I * (m : ℂ)) * ∑ j ∈ s, F j ((x : ℂ) * (1 + I * (m : ℂ)))) =
            ∑ j ∈ s, fun x : ℝ => (1 + I * (m : ℂ)) * F j ((x : ℂ) * (1 + I * (m : ℂ))) := by
          funext x; rw [Finset.mul_sum, Finset.sum_apply]
        rw [heq]; exact IntervalIntegrable.sum s fun j hj => (hFs j hj).2.2
    have hfn : (fun z => ∑ j ∈ insert i s, F j z) = fun z => F i z + ∑ j ∈ s, F j z := by
      funext z; rw [Finset.sum_insert hi]
    rw [hfn, triIntegral_addH hFi hsum_int, ih hFs, Finset.sum_insert hi]

private lemma triIntegral_congrH {F G : ℂ → ℂ} {R m : ℝ} (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 - I * (m : ℂ))) = G ((x : ℂ) * (1 - I * (m : ℂ))))
    (h2 : ∀ y ∈ Icc (-m * R) (m * R), F ((R : ℂ) + (y : ℂ) * I) = G ((R : ℂ) + (y : ℂ) * I))
    (h3 : ∀ x ∈ Icc (0 : ℝ) R, F ((x : ℂ) * (1 + I * (m : ℂ))) = G ((x : ℂ) * (1 + I * (m : ℂ)))) :
    triIntegral F R m = triIntegral G R m := by
  unfold triIntegral
  have hmR : -m * R ≤ m * R := by nlinarith
  have i1 : (∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * F ((x : ℂ) * (1 - I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 - I * (m : ℂ)) * G ((x : ℂ) * (1 - I * (m : ℂ))) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hR] at hx; rw [h1 x hx]
  have i2 : (∫ y : ℝ in (-m * R)..(m * R), F ((R : ℂ) + (y : ℂ) * I)) =
      ∫ y : ℝ in (-m * R)..(m * R), G ((R : ℂ) + (y : ℂ) * I) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hmR] at hy; rw [h2 y hy]
  have i3 : (∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * F ((x : ℂ) * (1 + I * (m : ℂ)))) =
      ∫ x : ℝ in (0 : ℝ)..R, (1 + I * (m : ℂ)) * G ((x : ℂ) * (1 + I * (m : ℂ))) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hR] at hx; rw [h3 x hx]
  rw [i1, i2, i3]

private lemma triBdIntegrable_of_continuousOnH {F : ℂ → ℂ} {R m : ℝ}
    (hR : 0 ≤ R) (hm : 0 ≤ m)
    (h1 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 - I * (m : ℂ)))) (Icc 0 R))
    (h2 : ContinuousOn (fun y : ℝ => F ((R : ℂ) + (y : ℂ) * I)) (Icc (-m * R) (m * R)))
    (h3 : ContinuousOn (fun x : ℝ => F ((x : ℂ) * (1 + I * (m : ℂ)))) (Icc 0 R)) :
    TriBdIntegrableH F R m :=
  ⟨(continuousOn_const.mul h1).intervalIntegrable_of_Icc hR,
   h2.intervalIntegrable_of_Icc (by nlinarith),
   (continuousOn_const.mul h3).intervalIntegrable_of_Icc hR⟩

private lemma mem_closedTri_mul_one_addH {R m x t : ℝ} (_hR : 0 ≤ R) (_hm : 0 ≤ m)
    (hx : x ∈ Icc 0 R) (ht : t ∈ Icc (-m) m) :
    (x : ℂ) * (1 + I * (t : ℂ)) ∈ closedTri R m := by
  have hre : ((x : ℂ) * (1 + I * (t : ℂ))).re = x := by simp [Complex.mul_re]
  have him : ((x : ℂ) * (1 + I * (t : ℂ))).im = x * t := by simp [Complex.mul_im]
  refine ⟨by rw [hre]; exact hx.1, by rw [hre]; exact hx.2, ?_⟩
  rw [hre, him, abs_mul, abs_of_nonneg hx.1, mul_comm m x]
  exact mul_le_mul_of_nonneg_left (abs_le.mpr ht) hx.1

private lemma triBd_avoid_pointH {c R m : ℝ} (hc : 0 < c) (hR : c < R) (hm : 0 < m) :
    (∀ x : ℝ, (x : ℂ) * (1 - I * (m : ℂ)) ≠ (c : ℂ)) ∧
    (∀ x : ℝ, (x : ℂ) * (1 + I * (m : ℂ)) ≠ (c : ℂ)) ∧
    (∀ y : ℝ, (R : ℂ) + (y : ℂ) * I ≠ (c : ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x h0
    have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, zero_sub, add_zero] at him
    have hx0 : x = 0 := by
      have : x * (-m) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right (neg_ne_zero.mpr hm.ne')
    subst hx0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
    linarith
  · intro x h0
    have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add] at him
    have hx0 : x = 0 := by
      have : x * m = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_right hm.ne'
    subst hx0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
    linarith
  · intro y h0
    have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, Complex.ofReal_im] at hre
    linarith

private lemma triIntegral_inv_sub_pow_ge_twoH {c R m : ℝ} (hc : 0 < c) (hR : c < R) (hm : 0 < m)
    (k : ℕ) :
    triIntegral (fun z : ℂ => ((z - (c : ℂ))⁻¹) ^ (k + 2)) R m = 0 := by
  have h_av := triBd_avoid_pointH hc hR hm
  let G (z : ℂ) : ℂ := -(((k + 1 : ℕ) : ℂ))⁻¹ * ((z - (c : ℂ))⁻¹) ^ (k + 1)
  have hG_deriv : ∀ z : ℂ, z ≠ (c : ℂ) →
      HasDerivAt G (((z - (c : ℂ))⁻¹) ^ (k + 2)) z := by
    intro z hzc
    have hsub : z - (c : ℂ) ≠ 0 := sub_ne_zero.mpr hzc
    have hinv : HasDerivAt (fun w : ℂ => (w - (c : ℂ))⁻¹) (-1 / (z - (c : ℂ)) ^ 2) z :=
      ((hasDerivAt_id z).sub_const (c : ℂ)).inv hsub
    have hpow := (hinv.pow (k + 1)).const_mul (-(((k + 1 : ℕ) : ℂ))⁻¹)
    simp only [Nat.add_sub_cancel, div_eq_mul_inv] at hpow
    refine hpow.congr_deriv ?_
    have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [inv_pow]
    field_simp [hk1, hsub]
    rw [← pow_add]
    ring_nf
  have h1 : ∫ x : ℝ in (0 : ℝ)..R,
      (1 - I * (m : ℂ)) * ((((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2)) =
      G ((R : ℂ) * (1 - I * (m : ℂ))) - G 0 := by
    have hd : ∀ x ∈ uIcc (0 : ℝ) R,
        HasDerivAt (fun t : ℝ => G ((t : ℂ) * (1 - I * (m : ℂ))))
          ((1 - I * (m : ℂ)) * ((((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2))) x := by
      intro x _
      have ha : HasDerivAt (fun t : ℝ => (t : ℂ) * (1 - I * (m : ℂ))) (1 - I * (m : ℂ)) x :=
        ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const (1 - I * (m : ℂ))).congr_deriv (one_mul _)
      exact ((hG_deriv _ (h_av.1 x)).comp x ha).congr_deriv (mul_comm _ _)
    have hc_int : Continuous (fun x : ℝ =>
        (1 - I * (m : ℂ)) * ((((x : ℂ) * (1 - I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2))) :=
      continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun x h0 =>
        h_av.1 x (sub_eq_zero.mp h0)).pow _)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc_int.intervalIntegrable 0 R)
    simpa only [Complex.ofReal_zero, zero_mul] using hftc
  have h2 : I * (∫ y : ℝ in (-m * R)..(m * R),
      ((((R : ℂ) + (y : ℂ) * I - (c : ℂ))⁻¹) ^ (k + 2))) =
      G ((R : ℂ) * (1 + I * (m : ℂ))) - G ((R : ℂ) * (1 - I * (m : ℂ))) := by
    have hd : ∀ y ∈ uIcc (-m * R) (m * R),
        HasDerivAt (fun s : ℝ => G ((R : ℂ) + (s : ℂ) * I))
          (I * ((((R : ℂ) + (y : ℂ) * I - (c : ℂ))⁻¹) ^ (k + 2))) y := by
      intro y _
      have ha : HasDerivAt (fun s : ℝ => (R : ℂ) + (s : ℂ) * I) I y :=
        (((Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I).congr_deriv (one_mul I)).const_add (R : ℂ)
      exact ((hG_deriv _ (h_av.2.2 y)).comp y ha).congr_deriv (mul_comm _ _)
    have hc_int : Continuous (fun y : ℝ =>
        I * ((((R : ℂ) + (y : ℂ) * I - (c : ℂ))⁻¹) ^ (k + 2))) :=
      continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun y h0 =>
        h_av.2.2 y (sub_eq_zero.mp h0)).pow _)
    have h_p : (R : ℂ) + ((m * R : ℝ) : ℂ) * I = (R : ℂ) * (1 + I * (m : ℂ)) := by push_cast; ring
    have h_m : (R : ℂ) + ((-m * R : ℝ) : ℂ) * I = (R : ℂ) * (1 - I * (m : ℂ)) := by push_cast; ring
    rw [← intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc_int.intervalIntegrable (-m * R) (m * R)),
      h_p, h_m]
  have h3 : ∫ x : ℝ in (0 : ℝ)..R,
      (1 + I * (m : ℂ)) * ((((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2)) =
      G ((R : ℂ) * (1 + I * (m : ℂ))) - G 0 := by
    have hd : ∀ x ∈ uIcc (0 : ℝ) R,
        HasDerivAt (fun t : ℝ => G ((t : ℂ) * (1 + I * (m : ℂ))))
          ((1 + I * (m : ℂ)) * ((((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2))) x := by
      intro x _
      have ha : HasDerivAt (fun t : ℝ => (t : ℂ) * (1 + I * (m : ℂ))) (1 + I * (m : ℂ)) x :=
        ((Complex.ofRealCLM.hasDerivAt (x := x)).mul_const (1 + I * (m : ℂ))).congr_deriv (one_mul _)
      exact ((hG_deriv _ (h_av.2.1 x)).comp x ha).congr_deriv (mul_comm _ _)
    have hc_int : Continuous (fun x : ℝ =>
        (1 + I * (m : ℂ)) * ((((x : ℂ) * (1 + I * (m : ℂ)) - (c : ℂ))⁻¹) ^ (k + 2))) :=
      continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun x h0 =>
        h_av.2.1 x (sub_eq_zero.mp h0)).pow _)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc_int.intervalIntegrable 0 R)
    simpa only [Complex.ofReal_zero, zero_mul] using hftc
  unfold triIntegral
  rw [h1, h2, h3]
  ring

private lemma dslopeIter_analyticOnH {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ)
    (c : ℂ) (k : ℕ) :
    AnalyticOnNhd ℂ ((Function.swap dslope c)^[k] F) univ := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hd : DifferentiableOn ℂ (dslope ((Function.swap dslope c)^[k] F) c) univ :=
      (Complex.differentiableOn_dslope (Filter.univ_mem : univ ∈ 𝓝 c)).mpr ih.differentiableOn
    exact hd.analyticOnNhd isOpen_univ

private lemma div_sub_pow_eq_dslopeIterH (F : ℂ → ℂ) (c : ℂ) (k : ℕ) {z : ℂ} (hz : z ≠ c) :
    F z / (z - c) ^ (k + 1) =
      ((Function.swap dslope c)^[k + 1] F) z +
        ∑ p ∈ Finset.range (k + 1), ((Function.swap dslope c)^[p] F c) * (z - c)⁻¹ ^ (k + 1 - p) := by
  have hsub : z - c ≠ 0 := sub_ne_zero.mpr hz
  induction k with
  | zero =>
    rw [zero_add, pow_one, Function.iterate_one, Finset.range_one, Finset.sum_singleton,
      Function.iterate_zero_apply, Nat.sub_zero, pow_one]
    have hsl := sub_smul_dslope F c z
    rw [smul_eq_mul] at hsl
    dsimp only [Function.swap]
    rw [← sub_add_cancel (F z) (F c), ← hsl, add_div, mul_div_cancel_left₀ _ hsub, div_eq_mul_inv,
      add_comm]
  | succ k ih =>
    rw [pow_succ, ← div_div, ih, add_div, Finset.sum_div]
    have hsplit : ((Function.swap dslope c)^[k + 1] F) z / (z - c) =
        ((Function.swap dslope c)^[k + 2] F) z +
          ((Function.swap dslope c)^[k + 1] F c) * (z - c)⁻¹ := by
      have hsl := sub_smul_dslope ((Function.swap dslope c)^[k + 1] F) c z
      rw [Function.iterate_succ_apply' (Function.swap dslope c) (k + 1) F]
      change _ = dslope ((Function.swap dslope c)^[k + 1] F) c z + _
      rw [smul_eq_mul] at hsl
      rw [← sub_add_cancel (((Function.swap dslope c)^[k + 1] F) z) (((Function.swap dslope c)^[k + 1] F) c),
        ← hsl, add_div, mul_div_cancel_left₀ _ hsub, div_eq_mul_inv]
    rw [hsplit, add_assoc]
    congr 1
    rw [Finset.sum_range_succ (fun p => ((Function.swap dslope c)^[p] F c) * (z - c)⁻¹ ^ (k + 1 + 1 - p))
      (k + 1), add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp_le : p ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      rw [show k + 1 + 1 - p = (k + 1 - p) + 1 by omega, pow_succ, div_eq_mul_inv]
      ring
    · simp

private lemma iterated_dslope_apply_selfH {F : ℂ → ℂ} {c : ℂ} (hF : AnalyticAt ℂ F c) (k : ℕ) :
    ((Function.swap dslope c)^[k] F) c = iteratedDeriv k F c / (k.factorial : ℂ) := by
  have hf_ps := hF.hasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope k
  rw [← hf_ps.coeff_zero 1, ← FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.coeff_iterate_fslope, zero_add,
    FormalMultilinearSeries.coeff_ofScalars]

private lemma triIntegral_mul_inv_sub_powH {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F univ)
    {c R m : ℝ} (hc : 0 < c) (hR : c < R) (hm : 0 < m) {s : ℕ} (hs : 1 ≤ s) :
    triIntegral (fun z : ℂ => F z / (z - (c : ℂ)) ^ s) R m =
      2 * (Real.pi : ℂ) * I * (iteratedDeriv (s - 1) F (c : ℂ) / ((s - 1).factorial : ℂ)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, s = k + 1 := ⟨s - 1, by omega⟩
  subst hk
  have h_av := triBd_avoid_pointH hc hR hm
  have hR_pos : 0 < R := lt_trans hc hR
  let G_rem : ℂ → ℂ := (Function.swap dslope (c : ℂ))^[k + 1] F
  have hG_an : AnalyticOnNhd ℂ G_rem univ := dslopeIter_analyticOnH hF (c : ℂ) (k + 1)
  have htri_rem : triIntegral G_rem R m = 0 :=
    triIntegral_eq_zero_of_analyticOn hR_pos.le hm.le isOpen_univ (subset_univ _) hG_an
  have hG_int : TriBdIntegrableH G_rem R m :=
    triBdIntegrable_of_continuousOnH hR_pos.le hm.le
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
      (hG_an.continuousOn.comp (by fun_prop) fun _ _ => mem_univ _)
  let termP (p : ℕ) (z : ℂ) : ℂ :=
    ((Function.swap dslope (c : ℂ))^[p] F (c : ℂ)) * ((z - (c : ℂ))⁻¹) ^ (k + 1 - p)
  have htermP_int : ∀ p ∈ Finset.range (k + 1), TriBdIntegrableH (termP p) R m := by
    intro p _
    refine triBdIntegrable_of_continuousOnH hR_pos.le hm.le
      (Continuous.continuousOn (continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun x h0 =>
        h_av.1 x (sub_eq_zero.mp h0)).pow _)))
      (Continuous.continuousOn (continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun y h0 =>
        h_av.2.2 y (sub_eq_zero.mp h0)).pow _)))
      (Continuous.continuousOn (continuous_const.mul ((Continuous.inv₀ (by fun_prop) fun x h0 =>
        h_av.2.1 x (sub_eq_zero.mp h0)).pow _)))
  have hsumP_int : TriBdIntegrableH (fun z => ∑ p ∈ Finset.range (k + 1), termP p z) R m := by
    refine ⟨?_, ?_, ?_⟩
    · have heq : (fun x : ℝ => (1 - I * (m : ℂ)) *
          ∑ p ∈ Finset.range (k + 1), termP p ((x : ℂ) * (1 - I * (m : ℂ)))) =
          ∑ p ∈ Finset.range (k + 1), fun x : ℝ =>
            (1 - I * (m : ℂ)) * termP p ((x : ℂ) * (1 - I * (m : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun p hp => (htermP_int p hp).1
    · have heq : (fun y : ℝ => ∑ p ∈ Finset.range (k + 1), termP p ((R : ℂ) + (y : ℂ) * I)) =
          ∑ p ∈ Finset.range (k + 1), fun y : ℝ => termP p ((R : ℂ) + (y : ℂ) * I) := by
        funext y; rw [Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun p hp => (htermP_int p hp).2.1
    · have heq : (fun x : ℝ => (1 + I * (m : ℂ)) *
          ∑ p ∈ Finset.range (k + 1), termP p ((x : ℂ) * (1 + I * (m : ℂ)))) =
          ∑ p ∈ Finset.range (k + 1), fun x : ℝ =>
            (1 + I * (m : ℂ)) * termP p ((x : ℂ) * (1 + I * (m : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun p hp => (htermP_int p hp).2.2
  have hcongr := triIntegral_congrH
    (F := fun z : ℂ => F z / (z - (c : ℂ)) ^ (k + 1))
    (G := fun z : ℂ => G_rem z + ∑ p ∈ Finset.range (k + 1), termP p z)
    hR_pos.le hm.le
    (fun x _ => div_sub_pow_eq_dslopeIterH F (c : ℂ) k (h_av.1 x))
    (fun y _ => div_sub_pow_eq_dslopeIterH F (c : ℂ) k (h_av.2.2 y))
    (fun x _ => div_sub_pow_eq_dslopeIterH F (c : ℂ) k (h_av.2.1 x))
  rw [hcongr, triIntegral_addH hG_int hsumP_int, htri_rem, zero_add,
    triIntegral_sumH _ _ R m htermP_int]
  have hterm_val : ∀ p ∈ Finset.range (k + 1),
      triIntegral (termP p) R m =
        if p = k then 2 * (Real.pi : ℂ) * I * (iteratedDeriv k F (c : ℂ) / (k.factorial : ℂ)) else 0 := by
    intro p hp
    have hp_le : p ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    dsimp only [termP]
    rw [triIntegral_const_mulH]
    by_cases hpk : p = k
    · subst hpk
      rw [ite_eq_left_iff.mpr fun hne => absurd rfl hne, show p + 1 - p = 1 by omega]
      simp only [pow_one]
      rw [triIntegral_inv_sub hc hR hm, iterated_dslope_apply_selfH (hF (c : ℂ) (mem_univ _)) p]
      ring
    · have hexp : k + 1 - p = (k - 1 - p) + 2 := by omega
      rw [ite_eq_right_iff.mpr fun heq => absurd heq hpk, hexp,
        triIntegral_inv_sub_pow_ge_twoH hc hR hm (k - 1 - p), mul_zero]
  rw [Finset.sum_congr rfl hterm_val, Finset.sum_ite_eq']
  simp

private lemma poly_finset_sum_coeffH {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (m : ℕ) :
    (∑ i ∈ s, f i).coeff m = ∑ i ∈ s, (f i).coeff m := by
  simpa only [Polynomial.lcoeff_apply] using map_sum (Polynomial.lcoeff ℂ m) f s

private lemma neg_X_powH (n : ℕ) :
    (-Polynomial.X : Polynomial ℂ) ^ n = Polynomial.C ((-1 : ℂ) ^ n) * Polynomial.X ^ n := by
  have hneg : ((-1 : Polynomial ℂ) ^ n) = Polynomial.C ((-1 : ℂ) ^ n) := by
    rw [← Polynomial.C_1, ← Polynomial.C_neg, ← Polynomial.C_pow]
  rw [← neg_one_mul (Polynomial.X : Polynomial ℂ), mul_pow, hneg]

/-- Higher-order Stokes amplitude polynomial `Q_m(u) = 2πi ∑_{s=1}^{ord m} (pp m s / (s-1)!) (-u)^{s-1}`. -/
@[expose] def polePolyH (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (m : ℕ) : Polynomial ℂ :=
  (2 * (Real.pi : ℂ) * I) •
    ∑ s ∈ Finset.Icc 1 (ord m),
      Polynomial.C (pp m s / ((s - 1).factorial : ℂ)) * (-Polynomial.X) ^ (s - 1)

private lemma polePolyH_coeff (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (m k : ℕ) :
    (polePolyH pp ord m).coeff k =
      if k < ord m then
        2 * (Real.pi : ℂ) * I * (pp m (k + 1) / (k.factorial : ℂ)) * (-1 : ℂ) ^ k
      else 0 := by
  unfold polePolyH
  rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul, poly_finset_sum_coeffH]
  have hterm : ∀ s ∈ Finset.Icc 1 (ord m),
      (Polynomial.C (pp m s / ((s - 1).factorial : ℂ)) * (-Polynomial.X) ^ (s - 1)).coeff k =
        if s = k + 1 then (pp m (k + 1) / (k.factorial : ℂ)) * (-1 : ℂ) ^ k else 0 := by
    intro s hhs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hhs).1
    rw [neg_X_powH, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
    by_cases hs : s = k + 1
    · subst hs; simp
    · have hne : k ≠ s - 1 := by omega
      simp [hs, hne]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  split_ifs with hmem hk
  · ring
  · rw [Finset.mem_Icc] at hmem; omega
  · rw [Finset.mem_Icc] at hmem; omega
  · simp

private lemma polePolyH_natDegree {pp : ℕ → ℕ → ℂ} {ord : ℕ → ℕ}
    (hord : ∀ m, 1 ≤ ord m) (hpp : ∀ m, pp m (ord m) ≠ 0) (m : ℕ) :
    (polePolyH pp ord m).natDegree = ord m - 1 := by
  have hm1 : 1 ≤ ord m := hord m
  have hcoeff_top : (polePolyH pp ord m).coeff (ord m - 1) ≠ 0 := by
    rw [polePolyH_coeff]
    have hlt : ord m - 1 < ord m := by omega
    rw [ite_eq_left_iff.mpr fun hnot => absurd hlt hnot, show ord m - 1 + 1 = ord m by omega]
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hfac : ((ord m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero)
      (div_ne_zero (hpp m) hfac)) (pow_ne_zero _ (by norm_num))
  refine le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero hcoeff_top)
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [polePolyH_coeff]
  have hnot : ¬ N < ord m := by omega
  rw [ite_eq_right_iff.mpr fun h => absurd h hnot]

private lemma polePolyH_leadingCoeff_ne_zero {pp : ℕ → ℕ → ℂ} {ord : ℕ → ℕ}
    (hord : ∀ m, 1 ≤ ord m) (hpp : ∀ m, pp m (ord m) ≠ 0) (m : ℕ) :
    (polePolyH pp ord m).leadingCoeff ≠ 0 := by
  have hm1 : 1 ≤ ord m := hord m
  refine Polynomial.leadingCoeff_ne_zero.mpr ?_
  intro h0
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff (ord m - 1)) h0
  rw [Polynomial.coeff_zero, polePolyH_coeff] at hc
  have hlt : ord m - 1 < ord m := by omega
  rw [ite_eq_left_iff.mpr fun hnot => absurd hlt hnot, show ord m - 1 + 1 = ord m by omega] at hc
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfac : ((ord m - 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hpi) Complex.I_ne_zero)
    (div_ne_zero (hpp m) hfac)) (pow_ne_zero _ (by norm_num)) hc

private lemma iteratedDeriv_neg_powH (j a : ℕ) (z : ℂ) :
    iteratedDeriv a (fun w : ℂ => (-w) ^ j) z =
      (-1 : ℂ) ^ a * ((j.descFactorial a : ℂ) * (-z) ^ (j - a)) := by
  induction a generalizing z with
  | zero => simp
  | succ a ih =>
    rw [iteratedDeriv_succ, show (iteratedDeriv a (fun w : ℂ => (-w) ^ j)) =
      fun w => (-1 : ℂ) ^ a * ((j.descFactorial a : ℂ) * (-w) ^ (j - a)) from funext ih]
    by_cases hja : j ≤ a
    · have hsub0 : j - a = 0 := by omega
      have hdesc0 : j.descFactorial (a + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp only [hsub0, pow_zero, mul_one, hdesc0, Nat.cast_zero, zero_mul, mul_zero]
      exact deriv_const z _
    · have haj : a < j := by omega
      have hd : HasDerivAt (fun w : ℂ => (-1 : ℂ) ^ a * ((j.descFactorial a : ℂ) * (-w) ^ (j - a)))
          ((-1 : ℂ) ^ (a + 1) * ((j.descFactorial (a + 1) : ℂ) * (-z) ^ (j - (a + 1)))) z := by
        have h1 : HasDerivAt (fun w : ℂ => (-w) ^ (j - a))
            (((j - a : ℕ) : ℂ) * (-z) ^ (j - a - 1) * (-1)) z :=
          (hasDerivAt_pow (j - a) (-z)).comp z (hasDerivAt_neg z)
        have h2 := h1.const_mul ((-1 : ℂ) ^ a * (j.descFactorial a : ℂ))
        have hfun : (fun w : ℂ => (-1 : ℂ) ^ a * ((j.descFactorial a : ℂ) * (-w) ^ (j - a))) =
            fun y : ℂ => (-1 : ℂ) ^ a * (j.descFactorial a : ℂ) * (-y) ^ (j - a) := by
          funext y; ring
        rw [hfun]
        refine h2.congr_deriv ?_
        rw [Nat.descFactorial_succ, show j - a - 1 = j - (a + 1) by omega, pow_succ]
        push_cast [haj.le]
        ring
      exact hd.deriv

private lemma iteratedDeriv_exp_neg_mulH (u : ℝ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (fun w : ℂ => Complex.exp (-w * (u : ℂ))) z =
      (-(u : ℂ)) ^ k * Complex.exp (-z * (u : ℂ)) := by
  induction k generalizing z with
  | zero => simp
  | succ k ih =>
    rw [iteratedDeriv_succ, show (iteratedDeriv k (fun w : ℂ => Complex.exp (-w * (u : ℂ)))) =
      fun w => (-(u : ℂ)) ^ k * Complex.exp (-w * (u : ℂ)) from funext ih]
    have hd : HasDerivAt (fun w : ℂ => (-(u : ℂ)) ^ k * Complex.exp (-w * (u : ℂ)))
        ((-(u : ℂ)) ^ (k + 1) * Complex.exp (-z * (u : ℂ))) z := by
      have h1 : HasDerivAt (fun w : ℂ => -w * (u : ℂ)) (-(u : ℂ)) z :=
        ((hasDerivAt_neg z).mul_const (u : ℂ)).congr_deriv (by ring)
      exact ((h1.cexp).const_mul ((-(u : ℂ)) ^ k)).congr_deriv (by rw [pow_succ]; ring)
    exact hd.deriv

private lemma iterate_deriv_C_mul_X_powH (c : ℂ) (p a : ℕ) :
    Polynomial.derivative^[a] (Polynomial.C c * Polynomial.X ^ p) =
      Polynomial.C (c * (p.descFactorial a : ℂ)) * Polynomial.X ^ (p - a) := by
  induction a generalizing c p with
  | zero => simp
  | succ a ih =>
    rw [Function.iterate_succ_apply', ih, Polynomial.derivative_C_mul_X_pow]
    cases hpa : p - a with
    | zero =>
      have hpa' : p ≤ a := Nat.sub_eq_zero_iff_le.mp hpa
      have hd0 : p.descFactorial (a + 1) = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      rw [hd0]
      simp
    | succ d =>
      have halt : a < p := by omega
      rw [Nat.descFactorial_succ, show p - (a + 1) = d by omega, Nat.add_sub_cancel]
      congr 2
      push_cast [hpa, halt.le]
      ring

private lemma iterate_deriv_neg_X_pow_evalH (p a : ℕ) (u : ℂ) :
    (Polynomial.derivative^[a] ((-Polynomial.X : Polynomial ℂ) ^ p)).eval u =
      (-1 : ℂ) ^ a * ((p.descFactorial a : ℂ) * (-u) ^ (p - a)) := by
  rw [neg_X_powH, iterate_deriv_C_mul_X_powH, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  by_cases hap : a ≤ p
  · have hneg : (-u) ^ (p - a) = (-1 : ℂ) ^ (p - a) * u ^ (p - a) := by
      rw [← neg_one_mul u, mul_pow]
    rw [hneg]
    calc (-1 : ℂ) ^ p * (p.descFactorial a : ℂ) * u ^ (p - a)
        = (-1 : ℂ) ^ (a + (p - a)) * (p.descFactorial a : ℂ) * u ^ (p - a) := by
          rw [Nat.add_sub_cancel' hap]
      _ = (-1 : ℂ) ^ a * ((p.descFactorial a : ℂ) * ((-1 : ℂ) ^ (p - a) * u ^ (p - a))) := by
          rw [pow_add]; ring
  · have hd0 : p.descFactorial a = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [hd0]

private lemma Q_jet_polePolyH_eval (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (ω : ℕ → ℝ) (m j : ℕ) (u : ℝ) :
    (Q_jet (polePolyH pp ord m) (ω m : ℂ) j).eval (u : ℂ) * Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
      ∑ s ∈ Finset.Icc 1 (ord m),
        2 * (Real.pi : ℂ) * I * pp m s *
          (iteratedDeriv (s - 1) (fun z : ℂ => (-z) ^ j * Complex.exp (-z * (u : ℂ))) (ω m : ℂ) /
            ((s - 1).factorial : ℂ)) := by
  have heval_Q : ∀ a : ℕ, (Polynomial.derivative^[a] (polePolyH pp ord m)).eval (u : ℂ) =
      (2 * (Real.pi : ℂ) * I) * ∑ s ∈ Finset.Icc 1 (ord m),
        (pp m s / ((s - 1).factorial : ℂ)) * (-1 : ℂ) ^ a *
          (((s - 1).descFactorial a : ℂ) * (-(u : ℂ)) ^ (s - 1 - a)) := by
    intro a
    have hsmul : ∀ (k : ℕ) (c : ℂ) (f : Polynomial ℂ),
        Polynomial.derivative^[k] (c • f) = c • Polynomial.derivative^[k] f := by
      intro k c f
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihk, Polynomial.derivative_smul]
    have hsum_d : ∀ (k : ℕ) (S : Finset ℕ) (g : ℕ → Polynomial ℂ),
        Polynomial.derivative^[k] (∑ i ∈ S, g i) = ∑ i ∈ S, Polynomial.derivative^[k] (g i) := by
      intro k S g
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [Function.iterate_succ_apply', ihk, Polynomial.derivative_sum]
        exact Finset.sum_congr rfl fun i _ => (Function.iterate_succ_apply' _ k (g i)).symm
    have hC_d : ∀ (k : ℕ) (c : ℂ) (f : Polynomial ℂ),
        Polynomial.derivative^[k] (Polynomial.C c * f) = Polynomial.C c * Polynomial.derivative^[k] f := by
      intro k c f
      induction k with
      | zero => simp
      | succ k ihk =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ihk, Polynomial.derivative_C_mul]
    unfold polePolyH
    rw [hsmul, hsum_d]
    change Polynomial.evalRingHom (u : ℂ) _ = _
    rw [Polynomial.coe_evalRingHom, Polynomial.eval_smul, smul_eq_mul,
      ← Polynomial.coe_evalRingHom, map_sum, Polynomial.coe_evalRingHom]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hC_d, Polynomial.eval_mul, Polynomial.eval_C, iterate_deriv_neg_X_pow_evalH]
    ring
  rw [Q_jet]
  change (Polynomial.evalRingHom (u : ℂ) _) * _ = _
  simp only [map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C]
  rw [Finset.sum_mul]
  trans ∑ a ∈ Finset.range (j + 1), ∑ s ∈ Finset.Icc 1 (ord m),
      ((Nat.choose j a : ℂ) * (-(ω m : ℂ)) ^ (j - a)) *
        ((2 * (Real.pi : ℂ) * I * pp m s / ((s - 1).factorial : ℂ)) * (-1 : ℂ) ^ a *
          (((s - 1).descFactorial a : ℂ) * (-(u : ℂ)) ^ (s - 1 - a)) *
          Complex.exp (-(ω m : ℂ) * (u : ℂ)))
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [heval_Q a, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => by ring
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
  have hit := iteratedDeriv_fun_mul (n := s - 1) (x := (ω m : ℂ))
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => (-z) ^ j) (ω m : ℂ)).contDiffAt
    (by fun_prop : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z * (u : ℂ))) (ω m : ℂ)).contDiffAt
  change iteratedDeriv (s - 1) (fun z : ℂ => (-z) ^ j * Complex.exp (-z * (u : ℂ))) (ω m : ℂ) = _ at hit
  rw [hit, Finset.sum_div, Finset.mul_sum]
  have hterm_eq : ∀ a ∈ Finset.range (j + 1),
      ((Nat.choose j a : ℂ) * (-(ω m : ℂ)) ^ (j - a)) *
        ((2 * (Real.pi : ℂ) * I * pp m s / ((s - 1).factorial : ℂ)) * (-1 : ℂ) ^ a *
          (((s - 1).descFactorial a : ℂ) * (-(u : ℂ)) ^ (s - 1 - a)) *
          Complex.exp (-(ω m : ℂ) * (u : ℂ))) =
      if a < s then
        2 * (Real.pi : ℂ) * I * pp m s *
          (((Nat.choose (s - 1) a : ℂ) * iteratedDeriv a (fun z : ℂ => (-z) ^ j) (ω m : ℂ) *
            iteratedDeriv (s - 1 - a) (fun z : ℂ => Complex.exp (-z * (u : ℂ))) (ω m : ℂ)) /
            ((s - 1).factorial : ℂ))
      else 0 := by
    intro a _
    by_cases has : a < s
    · rw [ite_eq_left_iff.mpr (fun h => absurd has h), iteratedDeriv_neg_powH j a,
        iteratedDeriv_exp_neg_mulH]
      have hchoose : ((s - 1).choose a : ℂ) / ((s - 1).factorial : ℂ) * (j.descFactorial a : ℂ) =
          ((s - 1).descFactorial a : ℂ) / ((s - 1).factorial : ℂ) * (j.choose a : ℂ) := by
        have hnat : (s - 1).choose a * j.descFactorial a = (s - 1).descFactorial a * j.choose a := by
          rw [Nat.descFactorial_eq_factorial_mul_choose j a,
            Nat.descFactorial_eq_factorial_mul_choose (s - 1) a]
          ring
        have hc : ((s - 1).choose a : ℂ) * (j.descFactorial a : ℂ) =
            ((s - 1).descFactorial a : ℂ) * (j.choose a : ℂ) := by exact_mod_cast hnat
        calc ((s - 1).choose a : ℂ) / ((s - 1).factorial : ℂ) * (j.descFactorial a : ℂ)
            = (((s - 1).choose a : ℂ) * (j.descFactorial a : ℂ)) / ((s - 1).factorial : ℂ) := by ring
          _ = (((s - 1).descFactorial a : ℂ) * (j.choose a : ℂ)) / ((s - 1).factorial : ℂ) := by rw [hc]
          _ = ((s - 1).descFactorial a : ℂ) / ((s - 1).factorial : ℂ) * (j.choose a : ℂ) := by ring
      calc ((Nat.choose j a : ℂ) * (-(ω m : ℂ)) ^ (j - a)) *
            ((2 * (Real.pi : ℂ) * I * pp m s / ((s - 1).factorial : ℂ)) * (-1 : ℂ) ^ a *
              (((s - 1).descFactorial a : ℂ) * (-(u : ℂ)) ^ (s - 1 - a)) *
              Complex.exp (-(ω m : ℂ) * (u : ℂ)))
          = 2 * (Real.pi : ℂ) * I * pp m s *
              (((s - 1).descFactorial a : ℂ) / ((s - 1).factorial : ℂ) * (j.choose a : ℂ)) *
              ((-1 : ℂ) ^ a * (-(ω m : ℂ)) ^ (j - a) * (-(u : ℂ)) ^ (s - 1 - a) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ))) := by ring
        _ = 2 * (Real.pi : ℂ) * I * pp m s *
              (((Nat.choose (s - 1) a : ℂ) / ((s - 1).factorial : ℂ) * (j.descFactorial a : ℂ))) *
              ((-1 : ℂ) ^ a * (-(ω m : ℂ)) ^ (j - a) * (-(u : ℂ)) ^ (s - 1 - a) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ))) := by rw [hchoose]
        _ = _ := by ring
    · have hdesc : (s - 1).descFactorial a = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
      simp [has, hdesc]
  rw [Finset.sum_congr rfl hterm_eq, show s - 1 + 1 = s by omega, ← Finset.sum_filter]
  have hfilt : (Finset.range (j + 1)).filter (· < s) = Finset.range (min (j + 1) s) := by
    ext a; simp only [Finset.mem_filter, Finset.mem_range, lt_min_iff]
  rw [hfilt]
  refine Finset.sum_subset (Finset.range_mono (min_le_right _ _)) fun a ha hnot => ?_
  rw [Finset.mem_range] at ha
  rw [Finset.mem_range, lt_min_iff] at hnot
  have hja : j < a := by omega
  have hdesc0 : j.descFactorial a = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr hja
  rw [iteratedDeriv_neg_powH j a]
  simp [hdesc0]

private def cutRH {φ ω ord pp} (_h : HigherOrderBorelData φ 0 ω ord pp) (n : ℕ) : ℝ :=
  (ω n + ω (n + 1)) / 2

private lemma cutRH_pos {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) (n : ℕ) :
    0 < cutRH h n := by
  have h1 : 0 < ω n := lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le n))
  have h2 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
  dsimp only [cutRH]; linarith

private lemma ω_lt_cutRH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) {m n : ℕ}
    (hm : m ≤ n) : ω m < cutRH h n := by
  have h1 : ω m ≤ ω n := h.ω_mono.monotone hm
  have h2 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
  dsimp only [cutRH]; linarith

private lemma cutRH_lt_ω {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) {m n : ℕ}
    (hm : n + 1 ≤ m) : cutRH h n < ω m := by
  have h1 : ω n < ω (n + 1) := h.ω_mono (Nat.lt_succ_self n)
  have h2 : ω (n + 1) ≤ ω m := h.ω_mono.monotone hm
  dsimp only [cutRH]; linarith

private lemma closedTri_subset_cutOpenH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp)
    (n : ℕ) :
    closedTri (cutRH h n) (Real.tan h.θ) ⊆
      borelWedge h.α₀ (ε₀H h) ∩ {z : ℂ | z.re < ω (n + 1)} := by
  intro z hz
  have hlt_next : z.re < ω (n + 1) := lt_of_le_of_lt hz.2.1 (cutRH_lt_ω h le_rfl)
  refine ⟨?_, hlt_next⟩
  rcases eq_or_lt_of_le hz.1 with hz0 | hzpos
  · left
    have him0 : z.im = 0 := abs_nonpos_iff.mp (by simpa [← hz0] using hz.2.2)
    have hz_eq : z = 0 := Complex.ext hz0.symm him0
    simpa [hz_eq, Metric.mem_ball, dist_zero_right] using ε₀H_pos h
  · right
    exact ⟨hzpos, lt_of_le_of_lt hz.2.2 (mul_lt_mul_of_pos_right (tan_lt_tanH h) hzpos)⟩

private lemma poleSub_analyticOn_cutOpenH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp)
    (n : ℕ) :
    let Sn (z : ℂ) : ℂ := ∑ m ∈ Finset.range (n + 1),
      ∑ s ∈ Finset.Icc 1 (ord m), pp m s / (z - (ω m : ℂ)) ^ s
    let Pset : Set ℂ := (fun m : ℕ => (ω m : ℂ)) '' (Finset.range (n + 1) : Set ℕ)
    let ψn (z : ℂ) : ℂ :=
      by classical exact if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => φ w - Sn w) else φ z - Sn z
    AnalyticOnNhd ℂ ψn (borelWedge h.α₀ (ε₀H h) ∩ {z : ℂ | z.re < ω (n + 1)}) := by
  classical
  intro Sn Pset ψn
  let Un : Set ℂ := borelWedge h.α₀ (ε₀H h) ∩ {z : ℂ | z.re < ω (n + 1)}
  have hUn_open : IsOpen Un :=
    (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im)
        (continuous_const.mul Complex.continuous_re)))).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hP_fin : Pset.Finite := (Finset.finite_toSet (Finset.range (n + 1))).image _
  have hP_closed : IsClosed Pset := hP_fin.isClosed
  have hUn_sub : Un \ Pset ⊆ rotatedPuncturedWedge 0 h.α₀ h.ε ω := by
    rw [rotatedPuncturedWedge_zero_eq]
    intro w ⟨hwU, hwP⟩
    refine ⟨?_, ?_⟩
    · rcases hwU.1 with hw_ball | hw_sec
      · left; exact Metric.ball_subset_ball (ε₀H_le_ε h) hw_ball
      · right; exact hw_sec
    · rintro ⟨m, rfl⟩
      have hm_lt : ω m < ω (n + 1) := by simpa using hwU.2
      exact hwP ⟨m, Finset.mem_coe.mpr (Finset.mem_range.mpr (h.ω_mono.lt_iff_lt.mp hm_lt)), rfl⟩
  have hSn_an : ∀ z ∈ Un \ Pset, AnalyticAt ℂ Sn z := by
    intro z hz
    refine Finset.analyticAt_fun_sum _ fun m hm => Finset.analyticAt_fun_sum _ fun s _ => ?_
    refine analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow s) ?_
    intro h0
    apply hz.2
    exact ⟨m, Finset.mem_coe.mpr hm, (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)).symm⟩
  intro z hzU
  by_cases hzP : z ∈ Pset
  · obtain ⟨k, hk_mem, rfl⟩ := hzP
    let Qk : Set ℂ := Pset \ {(ω k : ℂ)}
    have hQk_closed : IsClosed Qk := (hP_fin.subset Set.sdiff_subset).isClosed
    let Vk : Set ℂ := Un \ Qk
    have hVk_open : IsOpen Vk := hUn_open.sdiff hQk_closed
    have hwk_Vk : (ω k : ℂ) ∈ Vk := ⟨hzU, fun hmem => hmem.2 rfl⟩
    have hmem_punc : Vk \ {(ω k : ℂ)} ∈ 𝓝[≠] (ω k : ℂ) := by
      rw [Set.sdiff_eq, inter_comm]
      exact inter_mem_nhdsWithin _ (hVk_open.mem_nhds hwk_Vk)
    have hsub_open : Vk \ {(ω k : ℂ)} ⊆ Un \ Pset := fun ζ hζ =>
      ⟨hζ.1.1, fun hP => hζ.2 (by by_contra hne; exact hζ.1.2 ⟨hP, hne⟩)⟩
    have hψ_diff_punc : ∀ᶠ w in 𝓝[≠] (ω k : ℂ), DifferentiableAt ℂ ψn w := by
      filter_upwards [hmem_punc] with w hw
      have hdiff_sub : DifferentiableAt ℂ (fun ζ => φ ζ - Sn ζ) w :=
        ((h.analyticOn w (hUn_sub (hsub_open hw))).sub (hSn_an w (hsub_open hw))).differentiableAt
      have heq : ψn =ᶠ[𝓝 w] fun ζ => φ ζ - Sn ζ := by
        filter_upwards [(hUn_open.sdiff hP_closed).mem_nhds (hsub_open hw)] with ζ hζ
        dsimp only [ψn]
        exact ite_eq_right_iff.mpr fun hmem => absurd hmem hζ.2
      exact hdiff_sub.congr_of_eventuallyEq heq
    let PP_k (w : ℂ) : ℂ := ∑ s ∈ Finset.Icc 1 (ord k), pp k s / (w - (ω k : ℂ)) ^ s
    let Sn_rest (w : ℂ) : ℂ := ∑ m ∈ (Finset.range (n + 1)).erase k,
      ∑ s ∈ Finset.Icc 1 (ord m), pp m s / (w - (ω m : ℂ)) ^ s
    have hSn_split : ∀ w : ℂ, φ w - Sn w = (φ w - PP_k w) - Sn_rest w := fun w => by
      dsimp only [Sn, PP_k, Sn_rest]
      rw [← Finset.add_sum_erase (Finset.range (n + 1))
        (fun m => ∑ s ∈ Finset.Icc 1 (ord m), pp m s / (w - (ω m : ℂ)) ^ s) hk_mem]
      ring
    have hrest_an : AnalyticAt ℂ Sn_rest (ω k : ℂ) := by
      refine Finset.analyticAt_fun_sum _ fun m hm => Finset.analyticAt_fun_sum _ fun s _ => ?_
      have hmk : m ≠ k := (Finset.mem_erase.mp hm).1
      refine analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow s) ?_
      intro h0
      exact h.ω_mono.injective.ne hmk.symm (by exact_mod_cast sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0))
    obtain ⟨L, hL⟩ := h.pole_principalPart k
    have hL' : Tendsto (fun w => φ w - PP_k w) (𝓝[≠] (ω k : ℂ)) (𝓝 L) := by simpa [PP_k] using hL
    have h_tend : Tendsto (fun w => φ w - Sn w) (𝓝[≠] (ω k : ℂ)) (𝓝 (L - Sn_rest (ω k : ℂ))) := by
      simp_rw [hSn_split]
      exact hL'.sub hrest_an.continuousAt.continuousWithinAt.tendsto
    have hlim_eq : Filter.limUnder (𝓝[≠] (ω k : ℂ)) (fun w => φ w - Sn w) = L - Sn_rest (ω k : ℂ) :=
      h_tend.limUnder_eq
    have hψ_tend : Tendsto ψn (𝓝[≠] (ω k : ℂ)) (𝓝 (L - Sn_rest (ω k : ℂ))) := by
      refine h_tend.congr' ?_
      filter_upwards [hmem_punc] with w hw
      dsimp only [ψn]
      rw [ite_eq_right_iff.mpr fun hmem => absurd hmem (hsub_open hw).2]
    have hψ_at : ψn (ω k : ℂ) = L - Sn_rest (ω k : ℂ) := by
      have hmemP : (ω k : ℂ) ∈ Pset := ⟨k, Finset.mem_coe.mpr hk_mem, rfl⟩
      dsimp only [ψn]
      rw [ite_eq_left_iff.mpr fun hnot => absurd hmemP hnot, hlim_eq]
    have hψ_cont : ContinuousAt ψn (ω k : ℂ) :=
      continuousAt_iff_punctured_nhds.mpr (by simpa [hψ_at] using hψ_tend)
    exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hψ_diff_punc hψ_cont
  · have hopen : IsOpen (Un \ Pset) := hUn_open.sdiff hP_closed
    have hdiff_an : AnalyticAt ℂ (fun w => φ w - Sn w) z :=
      (h.analyticOn z (hUn_sub ⟨hzU, hzP⟩)).sub (hSn_an z ⟨hzU, hzP⟩)
    have heq : ψn =ᶠ[𝓝 z] fun w => φ w - Sn w := by
      filter_upwards [hopen.mem_nhds ⟨hzU, hzP⟩] with w hw
      dsimp only [ψn]
      exact ite_eq_right_iff.mpr fun hmemP => absurd hmemP hw.2
    exact hdiff_an.congr heq.symm

private lemma triBd_avoid_polesH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp) (n : ℕ) :
    (∀ x : ℝ, ∀ m : ℕ, (x : ℂ) * (1 - I * (Real.tan h.θ : ℂ)) ≠ (ω m : ℂ)) ∧
    (∀ x : ℝ, ∀ m : ℕ, (x : ℂ) * (1 + I * (Real.tan h.θ : ℂ)) ≠ (ω m : ℂ)) ∧
    (∀ y : ℝ, ∀ m : ℕ, (cutRH h n : ℂ) + (y : ℂ) * I ≠ (ω m : ℂ)) := by
  have hm_pos : 0 < Real.tan h.θ := tan_pos_of_memH h.hθ_pos (h.hθ_lt.trans h.hα₀_lt)
  refine ⟨?_, ?_, ?_⟩
  · intro x m h0
    have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, zero_sub, add_zero] at him
    have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * (-Real.tan h.θ) = 0)).resolve_right
      (neg_ne_zero.mpr hm_pos.ne')
    subst hx0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
    linarith [lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))]
  · intro x m h0
    have him := congrArg Complex.im h0
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
      Complex.one_im, Complex.I_im, mul_zero, zero_mul, add_zero, zero_add] at him
    have hx0 : x = 0 := (mul_eq_zero.mp (by linarith : x * Real.tan h.θ = 0)).resolve_right hm_pos.ne'
    subst hx0
    have hre := congrArg Complex.re h0
    simp only [Complex.ofReal_zero, zero_mul, Complex.zero_re, Complex.ofReal_re] at hre
    linarith [lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))]
  · intro y m h0
    have hre := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, Complex.ofReal_im] at hre
    have hre' : cutRH h n = ω m := by simpa using hre
    rcases le_or_gt m n with hmn | hnm
    · exact (ω_lt_cutRH h hmn).ne hre'.symm
    · exact (cutRH_lt_ω h hnm).ne hre'

private lemma triIntegral_φ_kernelH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp)
    (n j : ℕ) (u : ℝ) :
    triIntegral (fun z => (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z) (cutRH h n) (Real.tan h.θ) =
      ∑ m ∈ Finset.range (n + 1),
        (Q_jet (polePolyH pp ord m) (ω m : ℂ) j).eval (u : ℂ) * Complex.exp (-(ω m : ℂ) * (u : ℂ)) := by
  classical
  let R : ℝ := cutRH h n
  let mθ : ℝ := Real.tan h.θ
  have hR_pos : 0 < R := cutRH_pos h n
  have hm_pos : 0 < mθ := tan_pos_of_memH h.hθ_pos (h.hθ_lt.trans h.hα₀_lt)
  let Sn (z : ℂ) : ℂ := ∑ m ∈ Finset.range (n + 1),
    ∑ s ∈ Finset.Icc 1 (ord m), pp m s / (z - (ω m : ℂ)) ^ s
  let Pset : Set ℂ := (fun m : ℕ => (ω m : ℂ)) '' (Finset.range (n + 1) : Set ℕ)
  let ψn (z : ℂ) : ℂ :=
    if z ∈ Pset then Filter.limUnder (𝓝[≠] z) (fun w => φ w - Sn w) else φ z - Sn z
  let Un : Set ℂ := borelWedge h.α₀ (ε₀H h) ∩ {z : ℂ | z.re < ω (n + 1)}
  have hUn_open : IsOpen Un :=
    (Metric.isOpen_ball.union ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im)
        (continuous_const.mul Complex.continuous_re)))).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hψ_an : AnalyticOnNhd ℂ ψn Un := poleSub_analyticOn_cutOpenH h n
  let Fψ (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * ψn z
  have hFψ_an : AnalyticOnNhd ℂ Fψ Un :=
    ((analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)).mul hψ_an
  have htri_ψ : triIntegral Fψ R mθ = 0 :=
    triIntegral_eq_zero_of_analyticOn hR_pos.le hm_pos.le hUn_open
      (closedTri_subset_cutOpenH h n) hFψ_an
  have h_avoid := triBd_avoid_polesH h n
  let termMS (m s : ℕ) (z : ℂ) : ℂ :=
    (-z) ^ j * Complex.exp (-z * (u : ℂ)) * (pp m s / (z - (ω m : ℂ)) ^ s)
  let termM (m : ℕ) (z : ℂ) : ℂ := ∑ s ∈ Finset.Icc 1 (ord m), termMS m s z
  have htermMS_int : ∀ m ∈ Finset.range (n + 1), ∀ s ∈ Finset.Icc 1 (ord m),
      TriBdIntegrableH (termMS m s) R mθ := fun m _ s _ =>
    triBdIntegrable_of_continuousOnH hR_pos.le hm_pos.le
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div ((by fun_prop : Continuous fun x : ℝ =>
          ((x : ℂ) * (1 - I * (mθ : ℂ)) - (ω m : ℂ)) ^ s)) fun x h0 =>
          h_avoid.1 x m (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)))))
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div ((by fun_prop : Continuous fun y : ℝ =>
          ((R : ℂ) + (y : ℂ) * I - (ω m : ℂ)) ^ s)) fun y h0 =>
          h_avoid.2.2 y m (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)))))
      ((Continuous.continuousOn (by fun_prop)).mul (Continuous.continuousOn
        (continuous_const.div ((by fun_prop : Continuous fun x : ℝ =>
          ((x : ℂ) * (1 + I * (mθ : ℂ)) - (ω m : ℂ)) ^ s)) fun x h0 =>
          h_avoid.2.1 x m (sub_eq_zero.mp (eq_zero_of_pow_eq_zero h0)))))
  have htermM_int : ∀ m ∈ Finset.range (n + 1), TriBdIntegrableH (termM m) R mθ := fun m hm => by
    refine ⟨?_, ?_, ?_⟩
    · have heq : (fun x : ℝ => (1 - I * (mθ : ℂ)) *
          ∑ s ∈ Finset.Icc 1 (ord m), termMS m s ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
          ∑ s ∈ Finset.Icc 1 (ord m), fun x : ℝ =>
            (1 - I * (mθ : ℂ)) * termMS m s ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun s hs => (htermMS_int m hm s hs).1
    · have heq : (fun y : ℝ => ∑ s ∈ Finset.Icc 1 (ord m), termMS m s ((R : ℂ) + (y : ℂ) * I)) =
          ∑ s ∈ Finset.Icc 1 (ord m), fun y : ℝ => termMS m s ((R : ℂ) + (y : ℂ) * I) := by
        funext y; rw [Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun s hs => (htermMS_int m hm s hs).2.1
    · have heq : (fun x : ℝ => (1 + I * (mθ : ℂ)) *
          ∑ s ∈ Finset.Icc 1 (ord m), termMS m s ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
          ∑ s ∈ Finset.Icc 1 (ord m), fun x : ℝ =>
            (1 + I * (mθ : ℂ)) * termMS m s ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun s hs => (htermMS_int m hm s hs).2.2
  have h_pole_term : ∀ m ∈ Finset.range (n + 1),
      triIntegral (termM m) R mθ =
        (Q_jet (polePolyH pp ord m) (ω m : ℂ) j).eval (u : ℂ) * Complex.exp (-(ω m : ℂ) * (u : ℂ)) := by
    intro m hm
    rw [Q_jet_polePolyH_eval pp ord ω m j u]
    dsimp only [termM]
    rw [triIntegral_sumH _ _ R mθ fun s hs => htermMS_int m hm s hs]
    refine Finset.sum_congr rfl fun s hs => ?_
    have h_eq : termMS m s = fun z : ℂ =>
        pp m s * (((-z) ^ j * Complex.exp (-z * (u : ℂ))) / (z - (ω m : ℂ)) ^ s) := by
      funext z; dsimp only [termMS]; ring
    rw [h_eq, triIntegral_const_mulH]
    have hFn : AnalyticOnNhd ℂ (fun z : ℂ => (-z) ^ j * Complex.exp (-z * (u : ℂ))) univ :=
      (analyticOnNhd_id.neg.pow j).mul ((analyticOnNhd_id.neg.mul analyticOnNhd_const).cexp)
    rw [triIntegral_mul_inv_sub_powH hFn
      (lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m)))
      (ω_lt_cutRH h (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)))
      hm_pos (Finset.mem_Icc.mp hs).1]
    ring
  have h_Fψ_int : TriBdIntegrableH Fψ R mθ :=
    triBdIntegrable_of_continuousOnH hR_pos.le hm_pos.le
      (hFψ_an.continuousOn.comp (by fun_prop) fun x hx => by
        refine closedTri_subset_cutOpenH h n ?_
        have heq : (x : ℂ) * (1 - I * (mθ : ℂ)) = (x : ℂ) * (1 + I * ((-mθ : ℝ) : ℂ)) := by
          push_cast; ring
        rw [heq]; exact mem_closedTri_mul_one_addH hR_pos.le hm_pos.le hx ⟨le_rfl, by linarith⟩)
      (hFψ_an.continuousOn.comp (by fun_prop) fun y hy => by
        refine closedTri_subset_cutOpenH h n ⟨by simp [hR_pos.le], by simp [R], ?_⟩
        rw [show -mθ * R = -(mθ * R) by ring] at hy
        simpa [R, mθ] using abs_le.mpr hy)
      (hFψ_an.continuousOn.comp (by fun_prop) fun x hx =>
        closedTri_subset_cutOpenH h n (mem_closedTri_mul_one_addH hR_pos.le hm_pos.le hx ⟨by linarith, le_rfl⟩))
  have h_sum_int : TriBdIntegrableH (fun z => ∑ m ∈ Finset.range (n + 1), termM m z) R mθ := by
    refine ⟨?_, ?_, ?_⟩
    · have heq : (fun x : ℝ => (1 - I * (mθ : ℂ)) *
          ∑ m ∈ Finset.range (n + 1), termM m ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
          ∑ m ∈ Finset.range (n + 1), fun x : ℝ =>
            (1 - I * (mθ : ℂ)) * termM m ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).1
    · have heq : (fun y : ℝ => ∑ m ∈ Finset.range (n + 1), termM m ((R : ℂ) + (y : ℂ) * I)) =
          ∑ m ∈ Finset.range (n + 1), fun y : ℝ => termM m ((R : ℂ) + (y : ℂ) * I) := by
        funext y; rw [Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).2.1
    · have heq : (fun x : ℝ => (1 + I * (mθ : ℂ)) *
          ∑ m ∈ Finset.range (n + 1), termM m ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
          ∑ m ∈ Finset.range (n + 1), fun x : ℝ =>
            (1 + I * (mθ : ℂ)) * termM m ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
        funext x; rw [Finset.mul_sum, Finset.sum_apply]
      rw [heq]; exact IntervalIntegrable.sum _ fun m hm => (htermM_int m hm).2.2
  have h_pt_eq : ∀ z : ℂ, z ∉ Pset →
      (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z =
        Fψ z + ∑ m ∈ Finset.range (n + 1), termM m z := fun z hz => by
    dsimp only [Fψ, ψn, termM, termMS, Sn]
    rw [ite_eq_right_iff.mpr (fun hmem => absurd hmem hz)]
    simp only [mul_sub, Finset.mul_sum]
    ring
  have h_main_congr := triIntegral_congrH
    (F := fun z => (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z)
    (G := fun z => Fψ z + ∑ m ∈ Finset.range (n + 1), termM m z)
    hR_pos.le hm_pos.le
    (fun x _ => h_pt_eq _ (by rintro ⟨m, _, hm_eq⟩; exact h_avoid.1 x m hm_eq.symm))
    (fun y _ => h_pt_eq _ (by rintro ⟨m, _, hm_eq⟩; exact h_avoid.2.2 y m hm_eq.symm))
    (fun x _ => h_pt_eq _ (by rintro ⟨m, _, hm_eq⟩; exact h_avoid.2.1 x m hm_eq.symm))
  rw [h_main_congr, triIntegral_addH h_Fψ_int h_sum_int, htri_ψ, zero_add,
    triIntegral_sumH _ _ R mθ htermM_int]
  exact Finset.sum_congr rfl h_pole_term

private lemma jet_residual_densityH (φ : ℂ → ℂ) (j : ℕ) (z : ℂ) :
    ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhiH φ)).density z =
      (-z) ^ j * φ z := by
  induction j with
  | zero => simp [aPhiH, BorelExpr.residual]
  | succ j ih =>
    rw [Function.iterate_succ_apply', BorelExpr.residual, Minor.jet]
    dsimp only; rw [ih, pow_succ']; ring

private lemma jet_residual_atomH (φ : ℂ → ℂ) (j : ℕ) :
    ((Nat.iterate BorelExpr.jet j BorelExpr.leaf).residual (aPhiH φ)).atom = 0 := by
  cases j with
  | zero => rfl
  | succ j => rw [Function.iterate_succ_apply', BorelExpr.residual, Minor.jet]

private lemma iteratedDeriv_lateral_eq_laplaceH {φ ω ord pp}
    (_h : HigherOrderBorelData φ 0 ω ord pp)
    {U : Set ℂ} {d : ℂ} (hU : Domain U) (ray : ContainsRay U d)
    (ha : (aPhiH φ).Good U d) (hd : 0 < d.re) (j : ℕ) :
    ∀ᶠ u : ℝ in atTop,
      iteratedDeriv j (fun t : ℝ => (aPhiH φ).value d (t : ℂ)) u =
        ∫ v in Ioi (0 : ℝ), d * ((-(d * (v : ℂ))) ^ j *
          Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ))) := by
  let e := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have he_rep := (tendsto_coe_far hd).eventually (e.represents hU ray ha).2
  have he_deriv := (BorelExpr.jetIter_eval_eq_iteratedDeriv (aPhiH φ) hU ray ha hd j).1
  filter_upwards [he_rep, he_deriv] with u hurep hud
  rw [← hud, hurep, Minor.value, jet_residual_atomH φ j, zero_add]
  unfold complexLaplace
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  rw [damped, Minor.pull, jet_residual_densityH φ j]
  have hexp : -((u : ℂ) * d) * (v : ℂ) = -(d * (v : ℂ)) * (u : ℂ) := by ring
  rw [hexp]; ring

private lemma exp_tail_boundH {φ ω ord pp} (h : HigherOrderBorelData φ 0 ω ord pp)
    {U : Set ℂ} {d : ℂ} (hd_norm : ‖d‖ = 1) (hd_re : d.re = Real.cos h.θ)
    (hExp : ExpType (Minor.pull d φ))
    (hGood : (aPhiH φ).Good U d) (hRay : ContainsRay U d) (hDom : Domain U)
    (n j : ℕ) :
    ∃ K : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖∫ v in Ioi (cutRH h n / Real.cos h.θ), d * ((-(d * (v : ℂ))) ^ j *
        Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ)))‖ ≤
        K * Real.exp (-cutRH h n * u) := by
  obtain ⟨Cexp, Dexp, hCexp, _, hexp_bd⟩ := hExp
  have hcos : 0 < Real.cos h.θ := cos_pos_θH h
  let v₀ : ℝ := cutRH h n / Real.cos h.θ
  have hv₀_pos : 0 < v₀ := div_pos (cutRH_pos h n) hcos
  have h_base_int : IntegrableOn (fun v : ℝ => v ^ j * Real.exp (-(1 / 2 : ℝ) * v)) (Ioi 0) := by
    refine ((integrableOn_exp_mul_Ioi (show -(1 / 4 : ℝ) < 0 by norm_num) 0).const_mul
      ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j)).mono'
      ((by fun_prop : Continuous fun v : ℝ => v ^ j * Real.exp (-(1 / 2 : ℝ) * v)).aestronglyMeasurable.restrict) ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with v hv
    change 0 < v at hv
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le)]
    have hpow := Real.pow_div_factorial_le_exp ((1 / 4 : ℝ) * v) (by positivity) j
    have h1 : 0 < (1 / 4 : ℝ) ^ j := by positivity
    have h2 : 0 < (j.factorial : ℝ) := by positivity
    rw [mul_pow, div_le_iff₀ h2] at hpow
    have hvj : v ^ j ≤ ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp ((1 / 4 : ℝ) * v) := by
      calc v ^ j ≤ (Real.exp ((1 / 4 : ℝ) * v) * j.factorial) / (1 / 4 : ℝ) ^ j :=
            (le_div_iff₀ h1).mpr (by linarith)
        _ = _ := by ring
    calc v ^ j * Real.exp (-(1 / 2 : ℝ) * v)
        ≤ (((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp ((1 / 4 : ℝ) * v)) *
            Real.exp (-(1 / 2 : ℝ) * v) := mul_le_mul_of_nonneg_right hvj (Real.exp_pos _).le
      _ = ((j.factorial : ℝ) / (1 / 4 : ℝ) ^ j) * Real.exp (-(1 / 4 : ℝ) * v) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  let Ij : ℝ := ∫ v in Ioi (0 : ℝ), v ^ j * Real.exp (-(1 / 2 : ℝ) * v)
  let K : ℝ := Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Ij
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have hej_good : (ej.residual (aPhiH φ)).Good _ d := (ej.represents hDom hRay hGood).1
  have hej_int := (tendsto_coe_far (by rw [hd_re]; exact hcos)).eventually (hej_good.integrable hRay)
  refine ⟨K, ?_⟩
  filter_upwards [hej_int, eventually_ge_atTop ((Dexp + 1) / Real.cos h.θ)] with u hu_int hu_ge
  have hu_re : Dexp + 1 ≤ u * Real.cos h.θ := (div_le_iff₀ hcos).mp hu_ge
  let Ftail (v : ℝ) : ℂ := d * ((-(d * (v : ℂ))) ^ j *
    Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) * φ (d * (v : ℂ)))
  have h_eq_damped : ∀ v : ℝ,
      damped ((u : ℂ) * d) (Minor.pull d (ej.residual (aPhiH φ)).density) v = Ftail v := fun v => by
    rw [damped, Minor.pull, jet_residual_densityH φ j]
    have hexp : -((u : ℂ) * d) * (v : ℂ) = -(d * (v : ℂ)) * (u : ℂ) := by ring
    rw [hexp]; dsimp only [Ftail]; ring
  have hF_int_tail : IntegrableOn Ftail (Ioi v₀) :=
    (hu_int.congr_fun (fun v _ => h_eq_damped v) measurableSet_Ioi).mono_set (Ioi_subset_Ioi hv₀_pos.le)
  let bnd (v : ℝ) : ℝ :=
    (Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutRH h n * u)) *
      (v ^ j * Real.exp (-(1 / 2 : ℝ) * v))
  have hbnd_int : IntegrableOn bnd (Ioi 0) :=
    h_base_int.const_mul (Cexp * Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutRH h n * u))
  have h_pt_le : ∀ v ∈ Ioi v₀, ‖Ftail v‖ ≤ bnd v := by
    intro v hv
    change v₀ < v at hv
    have hv0 : 0 ≤ v := le_trans hv₀_pos.le hv.le
    have hF_rew : Ftail v = (-(d * (v : ℂ))) ^ j * Complex.exp (-(d * (v : ℂ)) * (u : ℂ)) *
        Minor.pull d φ v := by dsimp only [Ftail, Minor.pull]; ring
    rw [hF_rew, norm_mul, norm_mul, norm_pow, norm_neg, norm_mul, hd_norm, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0]
    have hexp_re : (-(d * (v : ℂ)) * (u : ℂ)).re = -(u * Real.cos h.θ) * v := by
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, hd_re]; ring
    rw [Complex.norm_exp, hexp_re]
    have hpull := hexp_bd v hv0
    have h_exp_split : Real.exp (-(u * Real.cos h.θ) * v) * (Cexp * Real.exp (Dexp * v)) =
        Cexp * Real.exp (-(u * Real.cos h.θ - Dexp) * v) := by
      rw [mul_left_comm _ Cexp, ← Real.exp_add]; congr 2; ring
    have h_exp_le : Real.exp (-(u * Real.cos h.θ - Dexp) * v) ≤
        Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutRH h n * u) * Real.exp (-(1 / 2 : ℝ) * v) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have h_v0_mul : (u * Real.cos h.θ - Dexp - 1 / 2) * v₀ ≤
          (u * Real.cos h.θ - Dexp - 1 / 2) * v :=
        mul_le_mul_of_nonneg_left hv.le (by linarith)
      have hv₀_eq : Real.cos h.θ * v₀ = cutRH h n := by
        dsimp only [v₀]; field_simp [hcos.ne']
      nlinarith [hv₀_eq]
    calc v ^ j * Real.exp (-(u * Real.cos h.θ) * v) * ‖Minor.pull d φ v‖
        ≤ v ^ j * Real.exp (-(u * Real.cos h.θ) * v) * (Cexp * Real.exp (Dexp * v)) :=
          mul_le_mul_of_nonneg_left hpull (by positivity)
      _ = Cexp * (v ^ j * Real.exp (-(u * Real.cos h.θ - Dexp) * v)) := by
          rw [mul_assoc, h_exp_split]; ring
      _ ≤ Cexp * (v ^ j * (Real.exp ((Dexp + 1 / 2) * v₀) * Real.exp (-cutRH h n * u) *
            Real.exp (-(1 / 2 : ℝ) * v))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h_exp_le (pow_nonneg hv0 _)) hCexp
      _ = bnd v := by dsimp only [bnd]; ring
  calc ‖∫ v in Ioi v₀, Ftail v‖
      ≤ ∫ v in Ioi v₀, ‖Ftail v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v in Ioi v₀, bnd v :=
        setIntegral_mono_on hF_int_tail.norm (hbnd_int.mono_set (Ioi_subset_Ioi hv₀_pos.le))
          measurableSet_Ioi h_pt_le
    _ ≤ ∫ v in Ioi 0, bnd v :=
        setIntegral_mono_set hbnd_int
          ((ae_restrict_mem measurableSet_Ioi).mono fun v (hv : 0 < v) =>
            mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hv.le _) (Real.exp_pos _).le))
          (Eventually.of_forall fun _ hx => Ioi_subset_Ioi hv₀_pos.le hx)
    _ = K * Real.exp (-cutRH h n * u) := by
        dsimp only [bnd, K, Ij]; rw [integral_const_mul]; ring

private lemma stokes_jump_expansion_higher_orderH {φ ω ord pp}
    (h : HigherOrderBorelData φ 0 ω ord pp) (n j : ℕ) :
    ∃ C : ℝ, ∀ᶠ u : ℝ in atTop,
      ‖iteratedDeriv j (fun t : ℝ => (aPhiH φ).value (dMinusH h) (t : ℂ)) u -
          iteratedDeriv j (fun t : ℝ => (aPhiH φ).value (dPlusH h) (t : ℂ)) u -
        ∑ m ∈ Finset.range (n + 1),
          (Q_jet (polePolyH pp ord m) (ω m : ℂ) j).eval (u : ℂ) * Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
        C * Real.exp (-cutRH h n * u) := by
  let R : ℝ := cutRH h n
  let mθ : ℝ := Real.tan h.θ
  let v₀ : ℝ := R / Real.cos h.θ
  have hR_pos : 0 < R := cutRH_pos h n
  have hcos : 0 < Real.cos h.θ := cos_pos_θH h
  have hm_pos : 0 < mθ := tan_pos_of_memH h.hθ_pos (h.hθ_lt.trans h.hα₀_lt)
  have hv₀_pos : 0 < v₀ := div_pos hR_pos hcos
  have hreP : 0 < (dPlusH h).re := by rw [dPlusH_re h]; exact hcos
  have hreM : 0 < (dMinusH h).re := by rw [dMinusH_re h]; exact hcos
  let Up := wedgePlusH h.α₀ (ε₀H h)
  let Um := wedgeMinusH h.α₀ (ε₀H h)
  have hUp_dom := wedgePlusH_domain h.α₀ (ε₀H_pos h)
  have hUm_dom := wedgeMinusH_domain h.α₀ (ε₀H_pos h)
  have hrayP := wedgePlusH_containsRay h
  have hrayM := wedgeMinusH_containsRay h
  have hgoodP := aPhiH_good_plus h
  have hgoodM := aPhiH_good_minus h
  have h_lapP := iteratedDeriv_lateral_eq_laplaceH h hUp_dom hrayP hgoodP hreP j
  have h_lapM := iteratedDeriv_lateral_eq_laplaceH h hUm_dom hrayM hgoodM hreM j
  let ej := Nat.iterate BorelExpr.jet j BorelExpr.leaf
  have h_intP := (tendsto_coe_far hreP).eventually
    ((ej.represents hUp_dom hrayP hgoodP).1.integrable hrayP)
  have h_intM := (tendsto_coe_far hreM).eventually
    ((ej.represents hUm_dom hrayM hgoodM).1.integrable hrayM)
  have hexp_m : ExpType (Minor.pull (dMinusH h) φ) := by simpa [dMinusH] using h.expType_minus
  have hexp_p : ExpType (Minor.pull (dPlusH h) φ) := by simpa [dPlusH] using h.expType_plus
  obtain ⟨Km, hKm⟩ := exp_tail_boundH h (norm_dMinusH h) (dMinusH_re h) hexp_m
    hgoodM hrayM hUm_dom n j
  obtain ⟨Kp, hKp⟩ := exp_tail_boundH h (norm_dPlusH h) (dPlusH_re h) hexp_p
    hgoodP hrayP hUp_dom n j
  have h_vert_sub : ∀ y ∈ Icc (-mθ * R) (mθ * R),
      (R : ℂ) + (y : ℂ) * I ∈ rotatedPuncturedWedge 0 h.α₀ h.ε ω := by
    rw [rotatedPuncturedWedge_zero_eq]
    intro y hy
    refine ⟨Or.inr ?_, fun ⟨m, hm_eq⟩ => (triBd_avoid_polesH h n).2.2 y m hm_eq.symm⟩
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
      mul_one, zero_add]
    rw [show -mθ * R = -(mθ * R) by ring] at hy
    exact ⟨hR_pos, lt_of_le_of_lt (abs_le.mpr hy) (mul_lt_mul_of_pos_right (tan_lt_tanH h) hR_pos)⟩
  have hφ_vert_cont : ContinuousOn (fun y : ℝ => φ ((R : ℂ) + (y : ℂ) * I)) (Icc (-mθ * R) (mθ * R)) :=
    h.analyticOn.continuousOn.comp (by fun_prop) h_vert_sub
  obtain ⟨Mφ, hMφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ_vert_cont
  let Kv : ℝ := (2 * mθ * R) * ((R / Real.cos h.θ) ^ j * max Mφ 0)
  have h_vert_bd : ∀ u : ℝ,
      ‖I * (∫ y : ℝ in (-mθ * R)..(mθ * R),
        (-((R : ℂ) + (y : ℂ) * I)) ^ j * Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ)) *
          φ ((R : ℂ) + (y : ℂ) * I))‖ ≤ Kv * Real.exp (-R * u) := by
    intro u
    rw [norm_mul, Complex.norm_I, one_mul]
    have hpt : ∀ y ∈ uIoc (-mθ * R) (mθ * R),
        ‖(-((R : ℂ) + (y : ℂ) * I)) ^ j * Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ)) *
          φ ((R : ℂ) + (y : ℂ) * I)‖ ≤
          ((R / Real.cos h.θ) ^ j * max Mφ 0) * Real.exp (-R * u) := by
      intro y hy
      rw [uIoc_of_le (by nlinarith : -mθ * R ≤ mθ * R)] at hy
      have hy_cc : y ∈ Icc (-mθ * R) (mθ * R) := ⟨hy.1.le, hy.2⟩
      have hnorm_z : ‖-((R : ℂ) + (y : ℂ) * I)‖ ≤ R / Real.cos h.θ := by
        rw [norm_neg, Complex.norm_def]
        have hy_sq : y ^ 2 ≤ mθ ^ 2 * R ^ 2 := by
          have hy_cc' : y ∈ Icc (-(mθ * R)) (mθ * R) := by simpa [neg_mul] using hy_cc
          have : |y| ≤ mθ * R := abs_le.mpr hy_cc'
          rw [← sq_abs y]
          calc |y| ^ 2 ≤ (mθ * R) ^ 2 := sq_le_sq' (by linarith [abs_nonneg y]) this
            _ = mθ ^ 2 * R ^ 2 := by ring
        have hnsq : Complex.normSq ((R : ℂ) + (y : ℂ) * I) ≤ (R / Real.cos h.θ) ^ 2 := by
          rw [Complex.normSq_apply]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            mul_zero, Complex.ofReal_im, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
            mul_one, zero_add]
          have hsec : 1 + mθ ^ 2 = (Real.cos h.θ) ^ (-2 : ℤ) := by
            dsimp only [mθ]
            rw [Real.tan_eq_sin_div_cos, _root_.zpow_neg, zpow_two]
            have hid := Real.sin_sq_add_cos_sq h.θ
            field_simp [hcos.ne']; linarith
          calc R * R + y * y = R ^ 2 + y ^ 2 := by ring
            _ ≤ R ^ 2 + mθ ^ 2 * R ^ 2 := by linarith
            _ = R ^ 2 * (1 + mθ ^ 2) := by ring
            _ = R ^ 2 * (Real.cos h.θ) ^ (-2 : ℤ) := by rw [hsec]
            _ = (R / Real.cos h.θ) ^ 2 := by rw [_root_.zpow_neg, zpow_two, div_pow]; ring
        exact Real.sqrt_le_iff.mpr ⟨div_nonneg hR_pos.le hcos.le, hnsq⟩
      have hexp_norm : ‖Complex.exp (-((R : ℂ) + (y : ℂ) * I) * (u : ℂ))‖ = Real.exp (-R * u) := by
        rw [Complex.norm_exp]; simp [Complex.mul_re]
      have hφ_le : ‖φ ((R : ℂ) + (y : ℂ) * I)‖ ≤ max Mφ 0 := (hMφ y hy_cc).trans (le_max_left _ _)
      rw [norm_mul, norm_mul, norm_pow, hexp_norm]
      calc ‖-((R : ℂ) + (y : ℂ) * I)‖ ^ j * Real.exp (-R * u) * ‖φ ((R : ℂ) + (y : ℂ) * I)‖
          ≤ (R / Real.cos h.θ) ^ j * Real.exp (-R * u) * max Mφ 0 := by gcongr
        _ = ((R / Real.cos h.θ) ^ j * max Mφ 0) * Real.exp (-R * u) := by ring
    have hle := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    calc ‖∫ y : ℝ in (-mθ * R)..(mθ * R), _‖
        ≤ ((R / Real.cos h.θ) ^ j * max Mφ 0) * Real.exp (-R * u) * |mθ * R - -mθ * R| := hle
      _ = Kv * Real.exp (-R * u) := by
          have habs : |mθ * R - -mθ * R| = 2 * mθ * R := by
            rw [show mθ * R - -mθ * R = 2 * mθ * R by ring, abs_of_pos (by positivity)]
          rw [habs]; dsimp only [Kv]; ring
  refine ⟨Kv + Km + Kp, ?_⟩
  filter_upwards [h_lapP, h_lapM, h_intP, h_intM, hKm, hKp] with u hlp hlm hip him hkm_bd hkp_bd
  rw [hlp, hlm]
  let Fkern (z : ℂ) : ℂ := (-z) ^ j * Complex.exp (-z * (u : ℂ)) * φ z
  have hFP_int : IntegrableOn (fun v : ℝ => dPlusH h * Fkern (dPlusH h * (v : ℂ))) (Ioi 0) :=
    hip.congr_fun (fun v _ => by
      rw [damped, Minor.pull, jet_residual_densityH φ j]
      have hexp : -((u : ℂ) * dPlusH h) * (v : ℂ) = -(dPlusH h * (v : ℂ)) * (u : ℂ) := by ring
      rw [hexp]; dsimp only [Fkern]; ring) measurableSet_Ioi
  have hFM_int : IntegrableOn (fun v : ℝ => dMinusH h * Fkern (dMinusH h * (v : ℂ))) (Ioi 0) :=
    him.congr_fun (fun v _ => by
      rw [damped, Minor.pull, jet_residual_densityH φ j]
      have hexp : -((u : ℂ) * dMinusH h) * (v : ℂ) = -(dMinusH h * (v : ℂ)) * (u : ℂ) := by ring
      rw [hexp]; dsimp only [Fkern]; ring) measurableSet_Ioi
  have hsplitP : (∫ v in (0 : ℝ)..v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ))) +
      (∫ v in Ioi v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ))) =
      ∫ v in Ioi (0 : ℝ), dPlusH h * Fkern (dPlusH h * (v : ℂ)) :=
    intervalIntegral.integral_interval_add_Ioi hFP_int (hFP_int.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hsplitM : (∫ v in (0 : ℝ)..v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))) +
      (∫ v in Ioi v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))) =
      ∫ v in Ioi (0 : ℝ), dMinusH h * Fkern (dMinusH h * (v : ℂ)) :=
    intervalIntegral.integral_interval_add_Ioi hFM_int (hFM_int.mono_set (Ioi_subset_Ioi hv₀_pos.le))
  have hdP_mul : (1 + I * (mθ : ℂ)) = ((Real.cos h.θ)⁻¹ : ℂ) * dPlusH h := by
    have hdP : dPlusH h = (Real.cos h.θ : ℂ) + (Real.sin h.θ : ℂ) * I := by
      unfold dPlusH; rw [show I * (h.θ : ℂ) = (h.θ : ℂ) * I by ring, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]
    rw [hdP]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    have hc : (Real.cos h.θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
    field_simp [hc]
  have hdM_mul : (1 - I * (mθ : ℂ)) = ((Real.cos h.θ)⁻¹ : ℂ) * dMinusH h := by
    have hdM : dMinusH h = (Real.cos h.θ : ℂ) - (Real.sin h.θ : ℂ) * I := by
      unfold dMinusH; rw [show I * ((-h.θ : ℝ) : ℂ) = ((-h.θ : ℝ) : ℂ) * I by ring, Complex.exp_mul_I]
      simp [Complex.ofReal_cos, Complex.ofReal_sin]; ring
    rw [hdM]; dsimp only [mθ]; rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
    have hc : (Real.cos h.θ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcos.ne'
    field_simp [hc]
  have hcovP : ∫ v in (0 : ℝ)..v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 + I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 + I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun v : ℝ => dPlusH h * Fkern (dPlusH h * (v : ℂ))) hcos.ne' (a := 0) (b := R)
    have heq : (fun x : ℝ => (1 + I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 + I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos h.θ)⁻¹ • (dPlusH h * Fkern (dPlusH h * ((x / Real.cos h.θ : ℝ) : ℂ))) := by
      funext x
      have harg : (x : ℂ) * (1 + I * (mθ : ℂ)) = dPlusH h * ((x / Real.cos h.θ : ℝ) : ℂ) := by
        rw [hdP_mul]; push_cast; ring
      rw [harg, Complex.real_smul, hdP_mul]; push_cast; ring
    rw [heq, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne', one_smul, zero_div]
  have hcovM : ∫ v in (0 : ℝ)..v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ)) =
      ∫ x in (0 : ℝ)..R, (1 - I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 - I * (mθ : ℂ))) := by
    have hcomp := intervalIntegral.integral_comp_div
      (fun v : ℝ => dMinusH h * Fkern (dMinusH h * (v : ℂ))) hcos.ne' (a := 0) (b := R)
    have heq : (fun x : ℝ => (1 - I * (mθ : ℂ)) * Fkern ((x : ℂ) * (1 - I * (mθ : ℂ)))) =
        fun x : ℝ => (Real.cos h.θ)⁻¹ • (dMinusH h * Fkern (dMinusH h * ((x / Real.cos h.θ : ℝ) : ℂ))) := by
      funext x
      have harg : (x : ℂ) * (1 - I * (mθ : ℂ)) = dMinusH h * ((x / Real.cos h.θ : ℝ) : ℂ) := by
        rw [hdM_mul]; push_cast; ring
      rw [harg, Complex.real_smul, hdM_mul]; push_cast; ring
    rw [heq, intervalIntegral.integral_smul, hcomp, smul_smul, inv_mul_cancel₀ hcos.ne', one_smul, zero_div]
  have hdiff : (∫ v in Ioi (0 : ℝ), dMinusH h * Fkern (dMinusH h * (v : ℂ))) -
      (∫ v in Ioi (0 : ℝ), dPlusH h * Fkern (dPlusH h * (v : ℂ))) -
      ∑ m ∈ Finset.range (n + 1),
        (Q_jet (polePolyH pp ord m) (ω m : ℂ) j).eval (u : ℂ) * Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
      (∫ v in Ioi v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))) -
      (∫ v in Ioi v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ))) -
      I * (∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I)) := by
    rw [← triIntegral_φ_kernelH h n j u, ← hsplitM, ← hsplitP, hcovM, hcovP]
    unfold triIntegral; ring
  change ‖(∫ v in Ioi (0 : ℝ), dMinusH h * Fkern (dMinusH h * (v : ℂ))) -
      (∫ v in Ioi (0 : ℝ), dPlusH h * Fkern (dPlusH h * (v : ℂ))) - _‖ ≤ _
  rw [hdiff]
  have htri : ‖(∫ v in Ioi v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))) -
        (∫ v in Ioi v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ))) -
        I * (∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I))‖ ≤
      ‖∫ v in Ioi v₀, dMinusH h * Fkern (dMinusH h * (v : ℂ))‖ +
      ‖∫ v in Ioi v₀, dPlusH h * Fkern (dPlusH h * (v : ℂ))‖ +
      ‖I * (∫ y : ℝ in (-mθ * R)..(mθ * R), Fkern ((R : ℂ) + (y : ℂ) * I))‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  have hv := h_vert_bd u
  dsimp only [R] at hv hkm_bd hkp_bd ⊢
  linarith

/-! #### 2B. Reversed Higher-Order Jet Polynomials `P_higher` & Operator `L_higher_conv` -/

/-- Reversed polynomial `w^N p(1/w)` in `w = 1/u`. -/
@[expose] def revPolyH (N : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k)

private lemma revPolyH_eval_inv {N : ℕ} (p : Polynomial ℂ) (hp : p.natDegree ≤ N)
    {u : ℂ} (hu : u ≠ 0) :
    (revPolyH N p).eval u⁻¹ = u⁻¹ ^ N * p.eval u := by
  have hsum : p = ∑ k ∈ Finset.range (N + 1), Polynomial.C (p.coeff k) * Polynomial.X ^ k :=
    Polynomial.as_sum_range_C_mul_X_pow' p (Nat.lt_succ_of_le hp)
  conv_rhs => rw [hsum]
  change Polynomial.evalRingHom u⁻¹ (revPolyH N p) = u⁻¹ ^ N * Polynomial.evalRingHom u _
  simp only [revPolyH, map_sum, map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C,
    map_pow, Polynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have heq : u⁻¹ ^ (N - k) = u⁻¹ ^ N * u ^ k := by
    calc u⁻¹ ^ (N - k) = u⁻¹ ^ (N - k) * (u⁻¹ ^ k * u ^ k) := by
          rw [← mul_pow, inv_mul_cancel₀ hu, one_pow, mul_one]
      _ = (u⁻¹ ^ (N - k) * u⁻¹ ^ k) * u ^ k := by ring
      _ = u⁻¹ ^ N * u ^ k := by rw [← pow_add, Nat.sub_add_cancel hk_le]
  rw [heq]; ring

private lemma revPolyH_coeff_zero (N : ℕ) (p : Polynomial ℂ) :
    (revPolyH N p).coeff 0 = p.coeff N := by
  rw [revPolyH, poly_finset_sum_coeffH]
  have hterm : ∀ k ∈ Finset.range (N + 1),
      (Polynomial.C (p.coeff k) * Polynomial.X ^ (N - k)).coeff 0 =
        if k = N then p.coeff N else 0 := fun k hk => by
    have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Polynomial.coeff_C_mul_X_pow]
    by_cases hkN : k = N
    · subst hkN; simp
    · have hne : (0 : ℕ) ≠ N - k := by omega
      simp [hkN, hne]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp

private lemma revPolyH_natDegree_le (N : ℕ) (p : Polynomial ℂ) :
    (revPolyH N p).natDegree ≤ N := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  rw [revPolyH, poly_finset_sum_coeffH]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk_le : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Polynomial.coeff_C_mul_X_pow]
  have hne : m ≠ N - k := by omega
  simp [hne]

private lemma iterate_derivative_natDegree_le (p : Polynomial ℂ) (a : ℕ) :
    (Polynomial.derivative^[a] p).natDegree ≤ p.natDegree := by
  induction a with
  | zero => exact le_rfl
  | succ a ih =>
    rw [Function.iterate_succ_apply']
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    rw [Polynomial.coeff_derivative, Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt ih (by omega)),
      zero_mul]

private lemma Q_jet_natDegree_le (q : Polynomial ℂ) (Ω : ℂ) (j : ℕ) :
    (Q_jet q Ω j).natDegree ≤ q.natDegree := by
  unfold Q_jet
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun a _ => ?_
  exact (Polynomial.natDegree_C_mul_le _ _).trans (iterate_derivative_natDegree_le q a)

private lemma Q_jet_coeff_natDegree (q : Polynomial ℂ) (Ω : ℂ) (j : ℕ) :
    (Q_jet q Ω j).coeff q.natDegree = q.leadingCoeff * (-Ω) ^ j := by
  unfold Q_jet
  rw [poly_finset_sum_coeffH]
  have hterm : ∀ a ∈ Finset.range (j + 1),
      (Polynomial.C ((j.choose a : ℂ) * (-Ω) ^ (j - a)) * Polynomial.derivative^[a] q).coeff q.natDegree =
        if a = 0 then q.leadingCoeff * (-Ω) ^ j else 0 := fun a _ => by
    cases a with
    | zero =>
      simp only [↓reduceIte, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_mul,
        Function.iterate_zero_apply, Polynomial.coeff_C_mul, Polynomial.leadingCoeff]
      ring
    | succ b =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, Polynomial.coeff_C_mul, Function.iterate_succ_apply',
        Polynomial.coeff_derivative]
      have hdeg : (Polynomial.derivative^[b] q).natDegree < q.natDegree + 1 :=
        Nat.lt_succ_of_le (iterate_derivative_natDegree_le q b)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hdeg, zero_mul, mul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
  simp

/-- Reversed higher-order Stokes jet polynomial in `w = 1/u` at the `m`-th pole of order `ord m`. -/
@[expose] def P_higher (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (ω : ℕ → ℝ) (m j : ℕ) : Polynomial ℂ :=
  revPolyH (ord m - 1) (Q_jet (polePolyH pp ord m) (ω m : ℂ) j)

private lemma P_higher_eval_inv {pp : ℕ → ℕ → ℂ} {ord : ℕ → ℕ}
    (hord : ∀ m, 1 ≤ ord m) (hpp : ∀ m, pp m (ord m) ≠ 0) (ω : ℕ → ℝ) (m j : ℕ)
    {u : ℂ} (hu : u ≠ 0) :
    (P_higher pp ord ω m j).eval u⁻¹ =
      u⁻¹ ^ (ord m - 1) * (Q_jet (polePolyH pp ord m) (ω m : ℂ) j).eval u := by
  have hdeg : (Q_jet (polePolyH pp ord m) (ω m : ℂ) j).natDegree ≤ ord m - 1 := by
    rw [← polePolyH_natDegree hord hpp m]
    exact Q_jet_natDegree_le _ _ _
  exact revPolyH_eval_inv _ hdeg hu

private lemma P_higher_coeff_zero {pp : ℕ → ℕ → ℂ} {ord : ℕ → ℕ}
    (hord : ∀ m, 1 ≤ ord m) (hpp : ∀ m, pp m (ord m) ≠ 0) (ω : ℕ → ℝ) (m j : ℕ) :
    (P_higher pp ord ω m j).coeff 0 = (polePolyH pp ord m).leadingCoeff * (-(ω m : ℂ)) ^ j := by
  unfold P_higher
  rw [revPolyH_coeff_zero, ← polePolyH_natDegree hord hpp m, Q_jet_coeff_natDegree]

private lemma P_higher_eval_inv_bdd (pp : ℕ → ℕ → ℂ) {ord : ℕ → ℕ} (hord : ∀ m, 1 ≤ ord m)
    (ω : ℕ → ℝ) (m j : ℕ) {u : ℝ} (hu : 1 ≤ u) :
    ‖(P_higher pp ord ω m j).eval (u : ℂ)⁻¹‖ ≤
      ∑ k ∈ Finset.range (ord m), ‖(P_higher pp ord ω m j).coeff k‖ := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hle := revPolyH_natDegree_le (ord m - 1) (Q_jet (polePolyH pp ord m) (ω m : ℂ) j)
  have hdeg : (P_higher pp ord ω m j).natDegree < ord m := by
    have := hord m
    change (P_higher pp ord ω m j).natDegree ≤ ord m - 1 at hle
    omega
  rw [Polynomial.eval_eq_sum_range' hdeg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_of_nonneg hu0.le]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (inv_nonneg.mpr hu0.le) (inv_le_one_of_one_le₀ hu))

/-- `ℂ{w}`-linear higher-order Stokes differential operator at the `m`-th pole:
`L_higher_conv pp ord ω r m Q = ∑ j, polyToConv (P_higher pp ord ω m j) • ∂_j Q`. -/
@[expose] def L_higher_conv (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (ω : ℕ → ℝ) (r m : ℕ) :
    MvPolynomial (Fin (r + 1)) ConvergentPowerSeries →ₗ[ConvergentPowerSeries]
      MvPolynomial (Fin (r + 1)) ConvergentPowerSeries where
  toFun Q := ∑ j : Fin (r + 1), polyToConv (P_higher pp ord ω m j.val) • MvPolynomial.pderiv j Q
  map_add' P Q := by simp only [map_add, smul_add, Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(MvPolynomial.pderiv j).map_smul, smul_comm]

private lemma degree_pderiv_conv_ltH {ι : Type*} (i : ι) (Q : MvPolynomial ι ConvergentPowerSeries)
    (h : 0 < Q.totalDegree) : (MvPolynomial.pderiv i Q).totalDegree < Q.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree_eq]
  apply lt_of_le_of_lt (Finset.sup_le fun m hm => ?_) (Nat.pred_lt h.ne')
  have hn := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hn
  have hs := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn))
  change ((m + Finsupp.single i 1).sum fun _ => id) ≤ _ at hs
  rw [← Finsupp.card_toMultiset, Finsupp.toMultiset_add, Finsupp.toMultiset_single] at hs
  simp at hs
  rw [Finsupp.card_toMultiset, Nat.pred_eq_sub_one]
  omega

private lemma totalDegree_conv_sum_ltH {ι σ : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → MvPolynomial σ ConvergentPowerSeries) {d : ℕ} (hd : 0 < d)
    (hf : ∀ i ∈ s, (f i).totalDegree < d) :
    (∑ i ∈ s, f i).totalDegree < d := by
  induction s using Finset.induction_on with
  | empty => simpa using hd
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine (MvPolynomial.totalDegree_add _ _).trans_lt ?_
    exact max_lt (hf i (Finset.mem_insert_self i s))
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Strict `Y`-total-degree drop under `L_higher_conv`. -/
theorem degree_L_higher_conv_lt (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (ω : ℕ → ℝ) {r : ℕ} (m : ℕ)
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) (h : 0 < Q.totalDegree) :
    (L_higher_conv pp ord ω r m Q).totalDegree < Q.totalDegree := by
  unfold L_higher_conv
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  refine totalDegree_conv_sum_ltH Finset.univ _ h fun j _ => ?_
  exact (MvPolynomial.totalDegree_smul_le _ _).trans_lt (degree_pderiv_conv_ltH j Q h)

private lemma evalConvMvPoly_finset_sum_eventuallyH {ι : Type*} {r : ℕ} (s : Finset ι)
    (f : ι → MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop,
      evalConvMvPoly (∑ i ∈ s, f i) (u : ℂ)⁻¹ = ∑ i ∈ s, evalConvMvPoly (f i) (u : ℂ)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Filter.Eventually.of_forall fun u => by simp [evalConvMvPoly_zero]
  | @insert a s ha ih =>
    filter_upwards [ih, evalConvMvPoly_add_eventually (f a) (∑ i ∈ s, f i)] with u hu hadd
    rw [Finset.sum_insert ha, hadd, hu, Finset.sum_insert ha]

lemma evalConvMvPoly_L_higher_conv_eventually (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (ω : ℕ → ℝ)
    {r : ℕ} (m : ℕ) (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) :
    ∀ᶠ u : ℝ in atTop,
      evalConvMvPoly (L_higher_conv pp ord ω r m Q) (u : ℂ)⁻¹ =
        ∑ j : Fin (r + 1), (P_higher pp ord ω m j.val).eval (u : ℂ)⁻¹ •
          MvPolynomial.pderiv j (evalConvMvPoly Q (u : ℂ)⁻¹) := by
  unfold L_higher_conv
  dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
  have hsum := evalConvMvPoly_finset_sum_eventuallyH (Finset.univ : Finset (Fin (r + 1)))
    (fun j => polyToConv (P_higher pp ord ω m j.val) • MvPolynomial.pderiv j Q)
  have hsmul : ∀ᶠ u : ℝ in atTop, ∀ j : Fin (r + 1),
      evalConvMvPoly (polyToConv (P_higher pp ord ω m j.val) • MvPolynomial.pderiv j Q) (u : ℂ)⁻¹ =
        (P_higher pp ord ω m j.val).eval (u : ℂ)⁻¹ • MvPolynomial.pderiv j (evalConvMvPoly Q (u : ℂ)⁻¹) := by
    refine Filter.eventually_all.mpr fun j => ?_
    filter_upwards [evalConvMvPoly_smul_eventually (polyToConv (P_higher pp ord ω m j.val)) (MvPolynomial.pderiv j Q)]
      with u hu
    rw [hu, evalConv_poly, evalConvMvPoly_pderiv]
  filter_upwards [hsum, hsmul] with u hus hsm
  rw [hus]
  exact Finset.sum_congr rfl fun j _ => hsm j

/-- Exact shift invariance: if `L_higher_conv pp ord ω r k Q = 0` for all `k < n`, then
`evalConvMvPoly Q u⁻¹` is identically invariant under all linear combinations of the higher-order
Stokes jet vectors for `k < n`. -/
theorem eval_shift_of_L_higher_conv_eq_zero (pp : ℕ → ℕ → ℂ) (ord : ℕ → ℕ) (ω : ℕ → ℝ)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) (n : ℕ)
    (hL : ∀ k < n, L_higher_conv pp ord ω r k Q = 0) :
    ∀ᶠ u : ℝ in atTop, ∀ (lam : ℕ → ℂ) (x : Fin (r + 1) → ℂ),
      MvPolynomial.eval
        (fun j : Fin (r + 1) =>
          x j + ∑ k ∈ Finset.range n, lam k * (P_higher pp ord ω k j.val).eval (u : ℂ)⁻¹)
        (evalConvMvPoly Q (u : ℂ)⁻¹) =
      MvPolynomial.eval x (evalConvMvPoly Q (u : ℂ)⁻¹) := by
  have hall : ∀ᶠ u : ℝ in atTop, ∀ k ∈ Finset.range n,
      ∑ j : Fin (r + 1), (P_higher pp ord ω k j.val).eval (u : ℂ)⁻¹ •
        MvPolynomial.pderiv j (evalConvMvPoly Q (u : ℂ)⁻¹) = 0 := by
    refine (Filter.eventually_all_finset (Finset.range n)).mpr fun k hk => ?_
    filter_upwards [evalConvMvPoly_L_higher_conv_eventually pp ord ω k Q] with u hu
    rw [← hu, hL k (Finset.mem_range.mp hk), evalConvMvPoly_zero]
  filter_upwards [hall] with u hu lam x
  suffices hsub : ∀ m ≤ n,
      MvPolynomial.eval
        (fun j : Fin (r + 1) =>
          x j + ∑ k ∈ Finset.range m, lam k * (P_higher pp ord ω k j.val).eval (u : ℂ)⁻¹)
        (evalConvMvPoly Q (u : ℂ)⁻¹) =
      MvPolynomial.eval x (evalConvMvPoly Q (u : ℂ)⁻¹) from hsub n le_rfl
  intro m hm
  induction m with
  | zero => simp
  | succ m ih =>
    have hlt : m < n := Nat.lt_of_succ_le hm
    have hsplit : (fun j : Fin (r + 1) =>
        x j + ∑ k ∈ Finset.range (m + 1), lam k * (P_higher pp ord ω k j.val).eval (u : ℂ)⁻¹) =
        fun j : Fin (r + 1) =>
          (x j + ∑ k ∈ Finset.range m, lam k * (P_higher pp ord ω k j.val).eval (u : ℂ)⁻¹) +
            lam m * (P_higher pp ord ω m j.val).eval (u : ℂ)⁻¹ := by
      funext j; rw [Finset.sum_range_succ, add_assoc]
    rw [hsplit, shift_invariant_of_pderiv_sum_eq_zero _ _ (hu m (Finset.mem_range.mpr hlt)),
      ih (Nat.le_of_lt hlt)]

private lemma nonConst_support_nonemptyH {r : ℕ}
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) (hpos : 0 < Q.totalDegree) :
    (Q.support.erase 0).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hle : Q.totalDegree ≤ 0 := by
    rw [MvPolynomial.totalDegree_eq]
    refine Finset.sup_le fun m hm => ?_
    by_cases hm0 : m = 0
    · subst hm0; simp
    · have : m ∈ Q.support.erase 0 := Finset.mem_erase.mpr ⟨hm0, hm⟩
      rw [hempty] at this; exact absurd this (Finset.notMem_empty m)
  omega

private lemma coeffW_coeffH {r : ℕ} (k : ℕ) (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (m : Fin (r + 1) →₀ ℕ) :
    (coeffW k Q).coeff m = if m = 0 then 0 else PowerSeries.coeff k (Q.coeff m).val := by
  classical
  unfold coeffW
  rw [MvPolynomial.coeff_sum]
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hm0 : m = 0
  · subst hm0
    simp only [↓reduceIte]
    refine Finset.sum_eq_zero fun b hb => by simp [(Finset.mem_erase.mp hb).1]
  · simp only [hm0, ↓reduceIte]
    by_cases hmem : m ∈ Q.support.erase 0
    · rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hbm; simp [hbm]
      · intro hnot; exact absurd hmem hnot
    · have hnot : m ∉ Q.support := fun h => hmem (Finset.mem_erase.mpr ⟨hm0, h⟩)
      rw [MvPolynomial.notMem_support_iff.mp hnot, Subring.coe_zero, map_zero, Finset.sum_eq_zero]
      intro b hb
      rw [ite_eq_right_iff]
      intro hbm; subst hbm; exact absurd hb hmem

/-- Lowest-`w`-order extraction: `L_higher_conv pp ord ω r m Q = 0` forces
`D_freq r (ω m) (coeffW (minNonConstWOrd Q) Q) = 0`. -/
theorem D_freq_coeffW_of_L_higher_conv_eq_zero {pp : ℕ → ℕ → ℂ} {ord : ℕ → ℕ}
    (hord : ∀ m, 1 ≤ ord m) (hpp : ∀ m, pp m (ord m) ≠ 0) (ω : ℕ → ℝ)
    {r : ℕ} (m : ℕ) (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hpos : 0 < Q.totalDegree)
    (hL : L_higher_conv pp ord ω r m Q = 0) :
    D_freq r (ω m : ℂ) (coeffW (minNonConstWOrd Q) Q) = 0 := by
  classical
  have hne := nonConst_support_nonemptyH Q hpos
  let k₀ : ℕ := minNonConstWOrd Q
  have hk₀_le : ∀ α : Fin (r + 1) →₀ ℕ, α ≠ 0 → ∀ k < k₀, PowerSeries.coeff k (Q.coeff α).val = 0 := by
    intro α hα0 k hk
    by_cases hmem : α ∈ Q.support
    · have hmem' : α ∈ Q.support.erase 0 := Finset.mem_erase.mpr ⟨hα0, hmem⟩
      have hle : k₀ ≤ psOrder (Q.coeff α) := by
        dsimp only [k₀]; unfold minNonConstWOrd
        simp only [hne, ↓reduceDIte]; exact Finset.inf'_le _ hmem'
      exact psOrder_coeff_eq_zero_of_lt (lt_of_lt_of_le hk hle)
    · rw [MvPolynomial.notMem_support_iff.mp hmem, Subring.coe_zero, map_zero]
  have hlead_ne : (polePolyH pp ord m).leadingCoeff ≠ 0 := polePolyH_leadingCoeff_ne_zero hord hpp m
  ext α
  change (D_freq r (ω m : ℂ) (coeffW k₀ Q)).coeff α = 0
  have hL_coeff : PowerSeries.coeff k₀ ((L_higher_conv pp ord ω r m Q).coeff α).val = 0 := by
    rw [hL]; simp
  have h_expand : PowerSeries.coeff k₀ ((L_higher_conv pp ord ω r m Q).coeff α).val =
      (polePolyH pp ord m).leadingCoeff * (D_freq r (ω m : ℂ) (coeffW k₀ Q)).coeff α := by
    unfold L_higher_conv D_freq
    dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_sum, Finset.mul_sum]
    have hsum_val : (∑ j : Fin (r + 1), (polyToConv (P_higher pp ord ω m j.val) • MvPolynomial.pderiv j Q).coeff α).val =
        ∑ j : Fin (r + 1), ((polyToConv (P_higher pp ord ω m j.val) • MvPolynomial.pderiv j Q).coeff α).val :=
      map_sum toPS _ _
    rw [hsum_val, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_smul, smul_eq_mul, smul_eq_mul,
      MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv]
    let α' : Fin (r + 1) →₀ ℕ := α + Finsupp.single j 1
    have hα'_ne : α' ≠ 0 := by
      intro h0; have h1 : α' j = 0 := by rw [h0]; simp
      simp [α'] at h1
    have hval_mul : (polyToConv (P_higher pp ord ω m j.val) * (Q.coeff α' * ((α j : ConvergentPowerSeries) + 1))).val =
        ((P_higher pp ord ω m j.val : PowerSeries ℂ) * (Q.coeff α').val) * PowerSeries.C (((α j : ℂ) + 1)) := by
      change (P_higher pp ord ω m j.val : PowerSeries ℂ) *
          ((Q.coeff α').val * ((α j : PowerSeries ℂ) + 1)) = _
      have hcast : ((α j : PowerSeries ℂ) + 1) = PowerSeries.C ((α j : ℂ) + 1) := by
        simp [map_add, map_natCast, map_one]
      rw [hcast, mul_assoc]
    rw [hval_mul, PowerSeries.coeff_mul_C, PowerSeries.coeff_mul]
    rw [Finset.sum_eq_single (0, k₀)]
    · rw [Polynomial.coeff_coe, P_higher_coeff_zero hord hpp ω m j.val, coeffW_coeffH,
        ite_eq_right_iff.mpr (fun h => absurd h hα'_ne)]
      ring
    · intro ab hab hne_ab
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      have hlt : ab.2 < k₀ := by
        by_contra hge
        push Not at hge
        exact hne_ab (Prod.ext (by omega) (by omega))
      rw [hk₀_le α' hα'_ne ab.2 hlt, mul_zero]
    · intro hnot
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal (a := (0, k₀)).mpr (zero_add k₀)) hnot
  rw [h_expand] at hL_coeff
  exact (mul_eq_zero.mp hL_coeff).resolve_left hlead_ne

/-- Complex Vandermonde contradiction over `ℂ{w}` for `L_higher_conv`. -/
theorem L_higher_conv_vandermonde_contradiction {pp : ℕ → ℕ → ℂ} {ord : ℕ → ℕ}
    (hord : ∀ m, 1 ≤ ord m) (hpp : ∀ m, pp m (ord m) ≠ 0)
    (ω : ℕ → ℝ) (hω_mono : StrictMono ω)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hpos : 0 < Q.totalDegree)
    (hL : ∀ n : Fin (r + 1), L_higher_conv pp ord ω r n.val Q = 0) : False := by
  let P : MvPolynomial (Fin (r + 1)) ℂ := coeffW (minNonConstWOrd Q) Q
  have hP_pos : 0 < P.totalDegree := coeffW_minNonConstWOrd_pos_deg Q hpos
  have hD : ∀ n : Fin (r + 1), D_freq r (ω n.val : ℂ) P = 0 := fun n =>
    D_freq_coeffW_of_L_higher_conv_eq_zero hord hpp ω n.val Q hpos (hL n)
  let V : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.vandermonde (fun n : Fin (r + 1) => -(ω n.val : ℂ))
  have hV_det : V.det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    exact Fin.ext (hω_mono.injective (Complex.ofReal_injective (neg_inj.mp hab)))
  have hpart : ∀ j : Fin (r + 1), MvPolynomial.pderiv j P = 0 := by
    intro j
    ext α
    change (MvPolynomial.pderiv j P).coeff α = 0
    let x : Fin (r + 1) → ℂ := fun k => (MvPolynomial.pderiv k P).coeff α
    have hVx : V.mulVec x = 0 := by
      ext n
      simp only [Matrix.mulVec, dotProduct, V, Matrix.vandermonde_apply, Pi.zero_apply, x]
      have h0 : (D_freq r (ω n.val : ℂ) P).coeff α = 0 := by rw [hD n]; rfl
      unfold D_freq at h0
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk] at h0
      rw [MvPolynomial.coeff_sum] at h0
      simpa only [MvPolynomial.coeff_smul, smul_eq_mul] using h0
    have hx0 : x = 0 := by
      have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V (isUnit_iff_ne_zero.mpr hV_det)
      calc x = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ).mulVec x := (Matrix.one_mulVec x).symm
        _ = (V⁻¹ * V).mulVec x := by rw [hinv]
        _ = V⁻¹.mulVec (V.mulVec x) := (Matrix.mulVec_mulVec x V⁻¹ V).symm
        _ = V⁻¹.mulVec 0 := by rw [hVx]
        _ = 0 := Matrix.mulVec_zero _
    exact congr_fun hx0 j
  have hPC : P = MvPolynomial.C (P.coeff 0) := by
    ext α
    rw [MvPolynomial.coeff_C]
    by_cases hα : α = 0
    · subst hα; simp
    · simp only [Ne.symm hα, ↓reduceIte]
      have hex : ∃ j : Fin (r + 1), α j ≠ 0 := by
        by_contra h; push Not at h; exact hα (Finsupp.ext h)
      obtain ⟨j, hj⟩ := hex
      let α' : Fin (r + 1) →₀ ℕ := α - Finsupp.single j 1
      have hpj := congr_arg (fun q : MvPolynomial (Fin (r + 1)) ℂ => q.coeff α') (hpart j)
      rw [MvPolynomial.coeff_pderiv] at hpj
      have h0 : (0 : MvPolynomial (Fin (r + 1)) ℂ).coeff α' = 0 := by simp
      rw [h0] at hpj
      have hsub : α' + Finsupp.single j 1 = α := by
        ext k; dsimp only [α']
        by_cases hk : j = k
        · subst hk; simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_eq_same]; omega
        · simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, hk, ↓reduceIte,
            Nat.sub_zero, add_zero]
      rw [hsub] at hpj
      have hcast : ((α' j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (α' j)
      exact (mul_eq_zero.mp hpj).resolve_right hcast
  have hP0 : P.totalDegree = 0 := by rw [hPC]; exact MvPolynomial.totalDegree_C _
  omega

/-! #### 2C. Unrotated & Rotated Convergent-Germ Higher-Order Stokes–Vandermonde Theorems -/

private lemma pow_mul_exp_neg_le_oneH (K : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ u : ℝ in atTop, u ^ K * Real.exp (-δ * u) ≤ 1 := by
  let U₀ : ℝ := max 1 (((K + 1).factorial : ℝ) / δ ^ (K + 1))
  filter_upwards [eventually_ge_atTop U₀] with u hu
  have hu1 : 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hU_ge : ((K + 1).factorial : ℝ) / δ ^ (K + 1) ≤ u := le_trans (le_max_right _ _) hu
  have harg := Real.pow_div_factorial_le_exp (δ * u) (by positivity) (K + 1)
  have hfac : 0 < ((K + 1).factorial : ℝ) := by positivity
  have hpow : 0 < (δ * u) ^ (K + 1) := pow_pos (by positivity) (K + 1)
  have hexp : Real.exp (-δ * u) ≤ ((K + 1).factorial : ℝ) / (δ ^ (K + 1) * u ^ (K + 1)) := by
    calc Real.exp (-δ * u) = (Real.exp (δ * u))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
      _ ≤ ((δ * u) ^ (K + 1) / ((K + 1).factorial : ℝ))⁻¹ := inv_anti₀ (div_pos hpow hfac) harg
      _ = ((K + 1).factorial : ℝ) / (δ ^ (K + 1) * u ^ (K + 1)) := by rw [inv_div, mul_pow]
  have hδ_pos : 0 < δ ^ (K + 1) := pow_pos hδ (K + 1)
  calc u ^ K * Real.exp (-δ * u)
      ≤ u ^ K * (((K + 1).factorial : ℝ) / (δ ^ (K + 1) * u ^ (K + 1))) :=
        mul_le_mul_of_nonneg_left hexp (pow_nonneg hu_pos.le K)
    _ = (((K + 1).factorial : ℝ) / δ ^ (K + 1)) / u := by
        rw [pow_succ u K]; field_simp [hu_pos.ne', hδ_pos.ne']
    _ ≤ u / u := div_le_div_of_nonneg_right hU_ge hu_pos.le
    _ = 1 := div_self hu_pos.ne'

private lemma HasAsympExp.eventually_bddH {f : ℝ → ℂ} {S : PowerSeries ℂ}
    (hf : HasAsympExp f S) : ∃ B : ℝ, ∀ᶠ u : ℝ in atTop, ‖f u‖ ≤ B := by
  obtain ⟨C, hC⟩ := hf 0
  refine ⟨C, ?_⟩
  filter_upwards [hC] with u hu
  simpa using hu

/-- **Unrotated Convergent-Germ Higher-Order Stokes–Vandermonde Theorem (`θ₀ = 0`, `ℂ{w}`)**:
For any `h : HigherOrderBorelData φ 0 ω ord pp`, `formalSeries φ` satisfies NO nonzero
algebraic differential equation with coefficients in `ConvergentPowerSeries` (`ℂ{w}`). -/
theorem no_conv_ade_of_higher_order_borel_zero
    {φ : ℂ → ℂ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ 0 ω ord pp)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries φ) Q = 0) : Q = 0 := by
  classical
  by_contra hQ_ne
  have hex : ∃ d : ℕ, ∃ R : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries,
      R.totalDegree = d ∧ R ≠ 0 ∧ formalEvalConv (formalSeries φ) R = 0 :=
    ⟨Q.totalDegree, Q, rfl, hQ_ne, hQ⟩
  let Qmin := Classical.choose (Nat.find_spec hex)
  have hQmin_spec := Classical.choose_spec (Nat.find_spec hex)
  have hQmin_deg : Qmin.totalDegree = Nat.find hex := hQmin_spec.1
  have hQmin_ne : Qmin ≠ 0 := hQmin_spec.2.1
  have hQmin_zero : formalEvalConv (formalSeries φ) Qmin = 0 := hQmin_spec.2.2
  have hQmin_min : ∀ R : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries,
      R ≠ 0 → R.totalDegree < Qmin.totalDegree → ¬ formalEvalConv (formalSeries φ) R = 0 := by
    intro R hR_ne hR_deg hR_zero
    rw [hQmin_deg] at hR_deg
    exact Nat.find_min hex hR_deg ⟨R, rfl, hR_ne, hR_zero⟩
  have hQmin_pos_deg : 0 < Qmin.totalDegree := by
    by_contra! hle
    have h0 : Qmin.totalDegree = 0 := Nat.eq_zero_of_le_zero hle
    have hC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
    have hev0 : formalEvalConv (formalSeries φ)
        (MvPolynomial.C (Qmin.coeff 0) : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries) = 0 := by
      rw [← hC]; exact hQmin_zero
    have hc0 : toPS (Qmin.coeff 0) = 0 := by simpa [formalEvalConv] using hev0
    have hcoeff0 : Qmin.coeff 0 = 0 := toPS_injective (hc0.trans (map_zero _).symm)
    exact hQmin_ne (hC.trans (by rw [hcoeff0, map_zero]))
  let g_pos : ℝ → ℂ := fun t => (aPhiH φ).value (dPlusH h) (t : ℂ)
  let g_neg : ℝ → ℂ := fun t => (aPhiH φ).value (dMinusH h) (t : ℂ)
  obtain ⟨hQ_pos, hQ_neg⟩ := higherOrder_conv_borel_transfer h Qmin hQmin_zero
  have hω_pos : ∀ m : ℕ, 0 < ω m := fun m => lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))
  have hL_zero : ∀ n : ℕ, n < r + 1 → L_higher_conv pp ord ω r n Qmin = 0 := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      have h_prev : ∀ m < n, L_higher_conv pp ord ω r m Qmin = 0 := fun m hm =>
        ih m hm (lt_trans hm hn)
      have h_shift_ev := eval_shift_of_L_higher_conv_eq_zero pp ord ω Qmin n h_prev
      have hL_eval_ev := evalConvMvPoly_L_higher_conv_eventually pp ord ω n Qmin
      choose Bg hBg using fun j : Fin (r + 1) => HasAsympExp.eventually_bddH (lateral_hasAsympExpH h j.val)
      have h_all_bg : ∀ᶠ u in atTop, ∀ j : Fin (r + 1), ‖iteratedDeriv j.val g_pos u‖ ≤ Bg j :=
        Filter.eventually_all.mpr hBg
      let M_p : ℝ := ∑ j : Fin (r + 1), ∑ k ∈ Finset.range (ord n),
        ‖(P_higher pp ord ω n j.val).coeff k‖
      have hM_p_nonneg : 0 ≤ M_p := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      let M : ℝ := 2 + (∑ j : Fin (r + 1), |Bg j|) + M_p
      have hM_nonneg : 0 ≤ M := by
        have h1 : 0 ≤ ∑ j : Fin (r + 1), |Bg j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        dsimp only [M]; linarith
      have hBg_le : ∀ j : Fin (r + 1), |Bg j| + 2 ≤ M := fun j => by
        have hs : |Bg j| ≤ ∑ i : Fin (r + 1), |Bg i| :=
          Finset.single_le_sum (fun i _ => abs_nonneg (Bg i)) (Finset.mem_univ j)
        dsimp only [M]; linarith
      have hv_bdd : ∀ u : ℝ, 1 ≤ u → ∀ j : Fin (r + 1),
          ‖(P_higher pp ord ω n j.val).eval (u : ℂ)⁻¹‖ ≤ M := fun u hu j => by
        have h1 := P_higher_eval_inv_bdd pp h.ord_pos ω n j.val hu
        have h2 : ∑ k ∈ Finset.range (ord n), ‖(P_higher pp ord ω n j.val).coeff k‖ ≤ M_p :=
          Finset.single_le_sum
            (f := fun j' : Fin (r + 1) => ∑ k ∈ Finset.range (ord n),
              ‖(P_higher pp ord ω n j'.val).coeff k‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
        have h3 : 0 ≤ ∑ i : Fin (r + 1), |Bg i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
        dsimp only [M]; linarith
      choose C_j h_jump_j using fun j : Fin (r + 1) => stokes_jump_expansion_higher_orderH h n j.val
      let R' : ℝ := cutRH h n
      have hR'_gt : ω n < R' := ω_lt_cutRH h le_rfl
      have hR'_pos : 0 < R' := cutRH_pos h n
      let C_rem : ℝ := ∑ j : Fin (r + 1), max (C_j j) 0
      have hC_rem_nonneg : 0 ≤ C_rem := Finset.sum_nonneg fun _ _ => le_max_right _ _
      have h_all_jump : ∀ᶠ u in atTop, ∀ j : Fin (r + 1),
          ‖iteratedDeriv j.val g_neg u - iteratedDeriv j.val g_pos u -
            ∑ m ∈ Finset.range (n + 1),
              (Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤
            C_rem * Real.exp (-R' * u) := by
        filter_upwards [Filter.eventually_all.mpr h_jump_j] with u hu j
        refine (hu j).trans ?_
        calc C_j j * Real.exp (-R' * u)
            ≤ max (C_j j) 0 * Real.exp (-R' * u) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
          _ ≤ C_rem * Real.exp (-R' * u) :=
              mul_le_mul_of_nonneg_right
                (Finset.single_le_sum (fun i _ => le_max_right _ _) (Finset.mem_univ j))
                (Real.exp_pos _).le
      -- Bound finite Stokes sum ≤ 1 eventually
      have hS_le1 : ∀ᶠ u : ℝ in atTop, ∀ j : Fin (r + 1),
          ‖∑ m ∈ Finset.range (n + 1),
            (Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
              Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤ 1 := by
        have hterm : ∀ j : Fin (r + 1), ∀ m ∈ Finset.range (n + 1),
            ∀ᶠ u : ℝ in atTop,
              ‖(Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ))‖ ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
          intro j m _
          let Bp : ℝ := ∑ k ∈ Finset.range (ord m), ‖(P_higher pp ord ω m j.val).coeff k‖
          let K : ℝ := (Bp + 1) * ((n + 1 : ℕ) : ℝ)
          filter_upwards [pow_mul_exp_neg_le_oneH (ord m) (hω_pos m),
            eventually_ge_atTop (max K 1)] with u hpe huK
          have hu1 : 1 ≤ u := (le_max_right K 1).trans huK
          have huK' : K ≤ u := (le_max_left K 1).trans huK
          have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
          have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
          have hrew : (Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
              Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
              ((u : ℂ) ^ (ord m - 1) * Complex.exp (-(ω m : ℂ) * (u : ℂ))) *
                (P_higher pp ord ω m j.val).eval (u : ℂ)⁻¹ := by
            rw [P_higher_eval_inv h.ord_pos h.pp_lead_ne_zero ω m j.val hu_ne]
            have hcancel : (u : ℂ) ^ (ord m - 1) * (u : ℂ)⁻¹ ^ (ord m - 1) = 1 := by
              rw [← mul_pow, mul_inv_cancel₀ hu_ne, one_pow]
            calc (Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
                  Complex.exp (-(ω m : ℂ) * (u : ℂ))
                = ((u : ℂ) ^ (ord m - 1) * (u : ℂ)⁻¹ ^ (ord m - 1)) *
                    ((Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
                      Complex.exp (-(ω m : ℂ) * (u : ℂ))) := by rw [hcancel, one_mul]
              _ = _ := by ring
          rw [hrew, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu_pos.le,
            Complex.norm_exp, (show (-(ω m : ℂ) * (u : ℂ)).re = -ω m * u by simp [Complex.mul_re])]
          have hp_bd := P_higher_eval_inv_bdd pp h.ord_pos ω m j.val hu1
          have hBp_nn : 0 ≤ Bp := Finset.sum_nonneg fun _ _ => norm_nonneg _
          have h1 : u ^ (ord m - 1) * Real.exp (-ω m * u) *
              ‖(P_higher pp ord ω m j.val).eval (u : ℂ)⁻¹‖ ≤
              (Bp + 1) * (u ^ (ord m - 1) * Real.exp (-ω m * u)) := by
            calc u ^ (ord m - 1) * Real.exp (-ω m * u) *
                  ‖(P_higher pp ord ω m j.val).eval (u : ℂ)⁻¹‖
                ≤ u ^ (ord m - 1) * Real.exp (-ω m * u) * Bp :=
                  mul_le_mul_of_nonneg_left hp_bd (by positivity)
              _ = Bp * (u ^ (ord m - 1) * Real.exp (-ω m * u)) := by ring
              _ ≤ (Bp + 1) * (u ^ (ord m - 1) * Real.exp (-ω m * u)) :=
                  mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          refine h1.trans ?_
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ))]
          have h2 : (Bp + 1) * (u ^ (ord m - 1) * Real.exp (-ω m * u)) * ((n + 1 : ℕ) : ℝ) =
              K * (u ^ (ord m - 1) * Real.exp (-ω m * u)) := by dsimp only [K]; ring
          rw [h2]
          have hm1 : ord m - 1 + 1 = ord m := Nat.sub_add_cancel (h.ord_pos m)
          have hupow : u * u ^ (ord m - 1) = u ^ ord m := by rw [← pow_succ', hm1]
          calc K * (u ^ (ord m - 1) * Real.exp (-ω m * u))
              ≤ u * (u ^ (ord m - 1) * Real.exp (-ω m * u)) :=
                mul_le_mul_of_nonneg_right huK' (by positivity)
            _ = u ^ ord m * Real.exp (-ω m * u) := by rw [← mul_assoc, hupow]
            _ ≤ 1 := hpe
        have hall := Filter.eventually_all.mpr fun j : Fin (r + 1) =>
          (Filter.eventually_all_finset (Finset.range (n + 1))).mpr fun m hm => hterm j m hm
        filter_upwards [hall] with u hu j
        refine (norm_sum_le _ _).trans ?_
        calc ∑ m ∈ Finset.range (n + 1),
              ‖(Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ))‖
            ≤ ∑ _m ∈ Finset.range (n + 1), (1 / ((n + 1 : ℕ) : ℝ)) :=
              Finset.sum_le_sum fun m hm => hu j m hm
          _ = 1 := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, one_div,
                mul_inv_cancel₀ (by positivity)]
      choose Bc hBc_nn hBc_ev using fun β : Fin (r + 1) →₀ ℕ => evalConv_eventually_bdd (Qmin.coeff β)
      have h_all_bc : ∀ᶠ u : ℝ in atTop, ∀ β ∈ Qmin.support, ‖evalConv (Qmin.coeff β) (u : ℂ)⁻¹‖ ≤ Bc β :=
        (Filter.eventually_all_finset Qmin.support).mpr fun β _ => hBc_ev β
      choose C_lip_β hC_lip_β h_lip_β using fun β : Fin (r + 1) →₀ ℕ =>
        eval_lipschitz_of_bounded (MvPolynomial.monomial β (1 : ℂ)) hM_nonneg
      choose C_tay_β hC_tay_β h_tay_β using fun β : Fin (r + 1) →₀ ℕ =>
        eval_shift_taylor_bound (MvPolynomial.monomial β (1 : ℂ)) hM_nonneg
      let C_L : ℝ := ∑ β ∈ Qmin.support, Bc β * C_lip_β β
      let C_T : ℝ := ∑ β ∈ Qmin.support, Bc β * C_tay_β β
      have hC_L_nn : 0 ≤ C_L := Finset.sum_nonneg fun β _ => mul_nonneg (hBc_nn β) (hC_lip_β β)
      have hC_T_nn : 0 ≤ C_T := Finset.sum_nonneg fun β _ => mul_nonneg (hBc_nn β) (hC_tay_β β)
      let δ₀ : ℝ := min (ω n) (R' - ω n)
      have hδ₀_pos : 0 < δ₀ := lt_min (hω_pos n) (sub_pos.mpr hR'_gt)
      have ha_small : ∀ᶠ u : ℝ in atTop, u ^ (ord n - 1) * Real.exp (-ω n * u) ≤ 1 :=
        pow_mul_exp_neg_le_oneH (ord n - 1) (hω_pos n)
      have hrem_small : ∀ᶠ u : ℝ in atTop, C_rem * Real.exp (-R' * u) ≤ 1 := by
        filter_upwards [pow_mul_exp_neg_le_oneH 1 hR'_pos,
          eventually_ge_atTop (max C_rem 1)] with u hpe huK
        have huC : C_rem ≤ u := (le_max_left _ _).trans huK
        calc C_rem * Real.exp (-R' * u) ≤ u ^ 1 * Real.exp (-R' * u) := by
              rw [pow_one]; exact mul_le_mul_of_nonneg_right huC (Real.exp_pos _).le
          _ ≤ 1 := hpe
      have hu_poly_exp : ∀ᶠ u : ℝ in atTop,
          u ^ (ord n - 1) * Real.exp (-(δ₀ / 2) * u) ≤ 1 :=
        pow_mul_exp_neg_le_oneH (ord n - 1) (half_pos hδ₀_pos)
      let C_fin : ℝ := C_L * C_rem + C_T
      have h_bridge_bound : ∀ᶠ u : ℝ in atTop,
          ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val g_pos u)
            (evalConvMvPoly (L_higher_conv pp ord ω r n Qmin) (u : ℂ)⁻¹)‖ ≤
            C_fin * Real.exp (-(δ₀ / 2) * u) := by
        filter_upwards [h_all_bg, h_all_jump, hQ_pos, hQ_neg, hS_le1, ha_small, hrem_small,
          hu_poly_exp, h_shift_ev, hL_eval_ev, h_all_bc, eventually_ge_atTop (1 : ℝ)]
          with u hbg hjump hpos hneg hS1 ha1 hrem1 hpoly_u hshift hLev hbc hu1
        have hu_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu1
        have hu_ne : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu_pos.ne'
        let x : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val g_pos u
        let Svec : Fin (r + 1) → ℂ := fun j => ∑ m ∈ Finset.range (n + 1),
          (Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
            Complex.exp (-(ω m : ℂ) * (u : ℂ))
        let y : Fin (r + 1) → ℂ := fun j => x j + Svec j
        let z : Fin (r + 1) → ℂ := fun j => iteratedDeriv j.val g_neg u
        let a : ℂ := (u : ℂ) ^ (ord n - 1) * Complex.exp (-(ω n : ℂ) * (u : ℂ))
        let v : Fin (r + 1) → ℂ := fun j => (P_higher pp ord ω n j.val).eval (u : ℂ)⁻¹
        have hx_le : ∀ j, ‖x j‖ ≤ M := fun j =>
          (hbg j).trans ((le_abs_self _).trans (by linarith [hBg_le j]))
        have hy_le : ∀ j, ‖y j‖ ≤ M := fun j => by
          calc ‖y j‖ ≤ ‖x j‖ + ‖Svec j‖ := norm_add_le _ _
            _ ≤ |Bg j| + 1 := add_le_add ((hbg j).trans (le_abs_self _)) (hS1 j)
            _ ≤ M := by linarith [hBg_le j]
        have hzy_le : ∀ j, ‖z j - y j‖ ≤ C_rem * Real.exp (-R' * u) := fun j => by
          have hsub_eq : z j - y j = iteratedDeriv j.val g_neg u - iteratedDeriv j.val g_pos u - Svec j := by
            simp only [y, x, z]; ring
          rw [hsub_eq]; exact hjump j
        have hz_le : ∀ j, ‖z j‖ ≤ M := fun j => by
          have hid : z j = y j + (z j - y j) := by ring
          rw [hid]
          calc ‖y j + (z j - y j)‖ ≤ ‖y j‖ + ‖z j - y j‖ := norm_add_le _ _
            _ ≤ (|Bg j| + 1) + 1 :=
                add_le_add ((norm_add_le _ _).trans
                  (add_le_add ((hbg j).trans (le_abs_self _)) (hS1 j)))
                  ((hzy_le j).trans hrem1)
            _ ≤ M := by linarith [hBg_le j]
        have ha_norm : ‖a‖ = u ^ (ord n - 1) * Real.exp (-ω n * u) := by
          simp only [a, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu_pos.le,
            Complex.norm_exp, (show (-(ω n : ℂ) * (u : ℂ)).re = -ω n * u by simp [Complex.mul_re])]
        have ha_le1 : ‖a‖ ≤ 1 := by rw [ha_norm]; exact ha1
        have ha_pos : 0 < ‖a‖ := by
          rw [ha_norm]; exact mul_pos (pow_pos hu_pos _) (Real.exp_pos _)
        have hQmin_decomp : evalConvMvPoly Qmin (u : ℂ)⁻¹ =
            ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ • MvPolynomial.monomial β (1 : ℂ) := by
          unfold evalConvMvPoly
          refine Finset.sum_congr rfl fun β _ => by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
        have h_lip_y : ‖MvPolynomial.eval y (evalConvMvPoly Qmin (u : ℂ)⁻¹)‖ ≤
            (C_L * C_rem) * Real.exp (-R' * u) := by
          have hyz : MvPolynomial.eval y (evalConvMvPoly Qmin (u : ℂ)⁻¹) =
              ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                (MvPolynomial.eval y (MvPolynomial.monomial β (1 : ℂ)) -
                  MvPolynomial.eval z (MvPolynomial.monomial β (1 : ℂ))) := by
            have hneg' : MvPolynomial.eval z (evalConvMvPoly Qmin (u : ℂ)⁻¹) = 0 := hneg
            rw [← sub_zero (MvPolynomial.eval y (evalConvMvPoly Qmin (u : ℂ)⁻¹)), ← hneg',
              hQmin_decomp]
            simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
              ← Finset.sum_sub_distrib, ← mul_sub]
          rw [hyz]
          calc ‖∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                  (MvPolynomial.eval y (MvPolynomial.monomial β 1) -
                    MvPolynomial.eval z (MvPolynomial.monomial β 1))‖
              ≤ ∑ β ∈ Qmin.support,
                  ‖evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                    (MvPolynomial.eval y (MvPolynomial.monomial β 1) -
                      MvPolynomial.eval z (MvPolynomial.monomial β 1))‖ := norm_sum_le _ _
            _ ≤ ∑ β ∈ Qmin.support, Bc β * (C_lip_β β * (C_rem * Real.exp (-R' * u))) := by
                refine Finset.sum_le_sum fun β hβ => ?_
                rw [norm_mul]
                have hlk := h_lip_β β z y (C_rem * Real.exp (-R' * u))
                  (mul_nonneg hC_rem_nonneg (Real.exp_pos _).le) hz_le hy_le hzy_le
                rw [norm_sub_rev] at hlk
                exact mul_le_mul (hbc β hβ) hlk (norm_nonneg _) (hBc_nn β)
            _ = (C_L * C_rem) * Real.exp (-R' * u) := by
                have h1 : ∀ β ∈ Qmin.support,
                    Bc β * (C_lip_β β * (C_rem * Real.exp (-R' * u))) =
                    (Bc β * C_lip_β β) * (C_rem * Real.exp (-R' * u)) := fun β _ => (mul_assoc _ _ _).symm
                rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← mul_assoc]
        have hmode_rew : ∀ (m : ℕ) (j : Fin (r + 1)),
            (Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
              Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
            ((u : ℂ) ^ (ord m - 1) * Complex.exp (-(ω m : ℂ) * (u : ℂ))) *
              (P_higher pp ord ω m j.val).eval (u : ℂ)⁻¹ := fun m j => by
          rw [P_higher_eval_inv h.ord_pos h.pp_lead_ne_zero ω m j.val hu_ne]
          have hcancel : (u : ℂ) ^ (ord m - 1) * (u : ℂ)⁻¹ ^ (ord m - 1) = 1 := by
            rw [← mul_pow, mul_inv_cancel₀ hu_ne, one_pow]
          calc (Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
                Complex.exp (-(ω m : ℂ) * (u : ℂ))
              = ((u : ℂ) ^ (ord m - 1) * (u : ℂ)⁻¹ ^ (ord m - 1)) *
                  ((Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
                    Complex.exp (-(ω m : ℂ) * (u : ℂ))) := by rw [hcancel, one_mul]
            _ = _ := by ring
        have h_shift_y : MvPolynomial.eval y (evalConvMvPoly Qmin (u : ℂ)⁻¹) =
            MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) := by
          have hy_split : y = fun j : Fin (r + 1) =>
              (x j + a * v j) + ∑ m ∈ Finset.range n,
                ((u : ℂ) ^ (ord m - 1) * Complex.exp (-(ω m : ℂ) * (u : ℂ))) *
                  (P_higher pp ord ω m j.val).eval (u : ℂ)⁻¹ := by
            funext j
            simp only [y, Svec, a, v]
            rw [Finset.sum_range_succ, hmode_rew n j]
            have hinner : ∑ m ∈ Finset.range n,
                (Q_jet (polePolyH pp ord m) (ω m : ℂ) j.val).eval (u : ℂ) *
                  Complex.exp (-(ω m : ℂ) * (u : ℂ)) =
                ∑ m ∈ Finset.range n,
                  ((u : ℂ) ^ (ord m - 1) * Complex.exp (-(ω m : ℂ) * (u : ℂ))) *
                    (P_higher pp ord ω m j.val).eval (u : ℂ)⁻¹ :=
              Finset.sum_congr rfl fun m _ => hmode_rew m j
            rw [hinner]; ring
          rw [hy_split]
          exact hshift (fun m => (u : ℂ) ^ (ord m - 1) * Complex.exp (-(ω m : ℂ) * (u : ℂ)))
            (fun j => x j + a * v j)
        have h_lin_eq : ∑ j : Fin (r + 1),
            MvPolynomial.eval x (MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹)) * v j =
            MvPolynomial.eval x (evalConvMvPoly (L_higher_conv pp ord ω r n Qmin) (u : ℂ)⁻¹) := by
          rw [hLev, map_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
          dsimp only [v]; ring
        have h_tay_y : ‖MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
            a * MvPolynomial.eval x (evalConvMvPoly (L_higher_conv pp ord ω r n Qmin) (u : ℂ)⁻¹)‖ ≤
            C_T * ‖a‖ ^ 2 := by
          have hpos' : MvPolynomial.eval x (evalConvMvPoly Qmin (u : ℂ)⁻¹) = 0 := hpos
          rw [← h_lin_eq]
          have hdecomp : MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
              a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹)) * v j =
              ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                (MvPolynomial.eval (fun j => x j + a * v j) (MvPolynomial.monomial β 1) -
                  MvPolynomial.eval x (MvPolynomial.monomial β 1) -
                  a * ∑ j : Fin (r + 1),
                    MvPolynomial.eval x (MvPolynomial.pderiv j (MvPolynomial.monomial β 1)) * v j) := by
            have h1 : MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
                MvPolynomial.eval x (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
                a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹)) * v j =
                MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
                  a * ∑ j : Fin (r + 1), MvPolynomial.eval x (MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹)) * v j := by
              rw [hpos', sub_zero]
            rw [← h1]
            have hpd : ∀ j : Fin (r + 1),
                MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹) =
                ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ •
                  MvPolynomial.pderiv j (MvPolynomial.monomial β (1 : ℂ)) := fun j => by
              rw [hQmin_decomp, map_sum]
              refine Finset.sum_congr rfl fun β _ => by rw [Derivation.map_smul_of_tower]
            have hsum_3 : a * ∑ j : Fin (r + 1),
                MvPolynomial.eval x (MvPolynomial.pderiv j (evalConvMvPoly Qmin (u : ℂ)⁻¹)) * v j =
                ∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                  (a * ∑ j : Fin (r + 1),
                    MvPolynomial.eval x (MvPolynomial.pderiv j (MvPolynomial.monomial β 1)) * v j) := by
              simp_rw [hpd, map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
                Finset.sum_mul]
              rw [Finset.mul_sum]
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun j _ => by ring
            rw [hsum_3, hQmin_decomp]
            simp only [map_sum, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
              ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun β _ => by ring
          rw [hdecomp]
          calc ‖∑ β ∈ Qmin.support, evalConv (Qmin.coeff β) (u : ℂ)⁻¹ *
                  (MvPolynomial.eval (fun j => x j + a * v j) (MvPolynomial.monomial β 1) -
                    MvPolynomial.eval x (MvPolynomial.monomial β 1) -
                    a * ∑ j : Fin (r + 1),
                      MvPolynomial.eval x (MvPolynomial.pderiv j (MvPolynomial.monomial β 1)) * v j)‖
              ≤ ∑ β ∈ Qmin.support, ‖evalConv (Qmin.coeff β) (u : ℂ)⁻¹ * _‖ := norm_sum_le _ _
            _ ≤ ∑ β ∈ Qmin.support, Bc β * (C_tay_β β * ‖a‖ ^ 2) := by
                refine Finset.sum_le_sum fun β hβ => ?_
                rw [norm_mul]
                exact mul_le_mul (hbc β hβ) (h_tay_β β x v a hx_le (hv_bdd u hu1) ha_le1)
                  (norm_nonneg _) (hBc_nn β)
            _ = C_T * ‖a‖ ^ 2 := by
                dsimp only [C_T]; rw [Finset.sum_mul]
                refine Finset.sum_congr rfl fun β _ => by ring
        have h_comb : ‖a‖ *
            ‖MvPolynomial.eval x (evalConvMvPoly (L_higher_conv pp ord ω r n Qmin) (u : ℂ)⁻¹)‖ ≤
            (C_L * C_rem) * Real.exp (-R' * u) + C_T * ‖a‖ ^ 2 := by
          rw [← norm_mul]
          have htri : ‖a * MvPolynomial.eval x (evalConvMvPoly (L_higher_conv pp ord ω r n Qmin) (u : ℂ)⁻¹)‖ ≤
              ‖MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹)‖ +
              ‖MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
                a * MvPolynomial.eval x (evalConvMvPoly (L_higher_conv pp ord ω r n Qmin) (u : ℂ)⁻¹)‖ := by
            simpa [sub_sub_cancel] using norm_sub_le
              (MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹))
              (MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹) -
                a * MvPolynomial.eval x (evalConvMvPoly (L_higher_conv pp ord ω r n Qmin) (u : ℂ)⁻¹))
          have h_lip_av : ‖MvPolynomial.eval (fun j => x j + a * v j) (evalConvMvPoly Qmin (u : ℂ)⁻¹)‖ ≤
              (C_L * C_rem) * Real.exp (-R' * u) := by rwa [← h_shift_y]
          exact htri.trans (add_le_add h_lip_av h_tay_y)
        have h_div : ‖MvPolynomial.eval x (evalConvMvPoly (L_higher_conv pp ord ω r n Qmin) (u : ℂ)⁻¹)‖ ≤
            ((C_L * C_rem) * Real.exp (-R' * u)) / ‖a‖ + C_T * ‖a‖ := by
          have hstep := (le_div_iff₀' ha_pos).mpr h_comb
          refine hstep.trans_eq ?_
          field_simp [ha_pos.ne']
        refine h_div.trans ?_
        have hterm1 : ((C_L * C_rem) * Real.exp (-R' * u)) / ‖a‖ ≤
            (C_L * C_rem) * Real.exp (-(δ₀ / 2) * u) := by
          rw [ha_norm]
          have hupow_ge : (1 : ℝ) ≤ u ^ (ord n - 1) := one_le_pow₀ hu1
          have hden_ge : Real.exp (-ω n * u) ≤ u ^ (ord n - 1) * Real.exp (-ω n * u) :=
            le_mul_of_one_le_left (Real.exp_pos _).le hupow_ge
          have hdiv_le : ((C_L * C_rem) * Real.exp (-R' * u)) /
              (u ^ (ord n - 1) * Real.exp (-ω n * u)) ≤
              ((C_L * C_rem) * Real.exp (-R' * u)) / Real.exp (-ω n * u) :=
            div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hden_ge
          refine hdiv_le.trans ?_
          have hquot : ((C_L * C_rem) * Real.exp (-R' * u)) / Real.exp (-ω n * u) =
              (C_L * C_rem) * Real.exp (-(R' - ω n) * u) := by
            rw [mul_div_assoc, ← Real.exp_sub]; congr 2; ring
          rw [hquot]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_nonneg hC_L_nn hC_rem_nonneg)
          have hδle : δ₀ ≤ R' - ω n := min_le_right _ _
          nlinarith
        have hterm2 : C_T * ‖a‖ ≤ C_T * Real.exp (-(δ₀ / 2) * u) := by
          rw [ha_norm]
          refine mul_le_mul_of_nonneg_left ?_ hC_T_nn
          have hexp_le : Real.exp (-ω n * u) ≤ Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u) := by
            rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
            have hδle : δ₀ ≤ ω n := min_le_left _ _
            nlinarith
          calc u ^ (ord n - 1) * Real.exp (-ω n * u)
              ≤ u ^ (ord n - 1) * (Real.exp (-(δ₀ / 2) * u) * Real.exp (-(δ₀ / 2) * u)) :=
                mul_le_mul_of_nonneg_left hexp_le (pow_nonneg hu_pos.le _)
            _ = (u ^ (ord n - 1) * Real.exp (-(δ₀ / 2) * u)) * Real.exp (-(δ₀ / 2) * u) := by ring
            _ ≤ 1 * Real.exp (-(δ₀ / 2) * u) := mul_le_mul_of_nonneg_right hpoly_u (Real.exp_pos _).le
            _ = Real.exp (-(δ₀ / 2) * u) := one_mul _
        dsimp only [C_fin]
        linarith
      have hL_formal : formalEvalConv (formalSeries φ) (L_higher_conv pp ord ω r n Qmin) = 0 :=
        formalEvalConv_eq_zero_of_exp_smallH (lateral_hasAsympExpH h)
          (L_higher_conv pp ord ω r n Qmin) (half_pos hδ₀_pos) h_bridge_bound
      by_contra hL_ne
      exact hQmin_min (L_higher_conv pp ord ω r n Qmin) hL_ne
        (degree_L_higher_conv_lt pp ord ω n Qmin hQmin_pos_deg) hL_formal
  exact L_higher_conv_vandermonde_contradiction h.ord_pos h.pp_lead_ne_zero ω h.ω_mono
    Qmin hQmin_pos_deg (fun n => hL_zero n.val n.isLt)

/-! #### 2D. Rotation Reduction (`θ₀ → 0`) over `ℂ{w}` & General `HigherOrderBorelData` Lift -/

/-- Rescaling ring endomorphism `a(w) ↦ a(μ * w)` on `ConvergentPowerSeries`. -/
@[expose] def rescaleConv (μ : ℂ) : ConvergentPowerSeries →+* ConvergentPowerSeries where
  toFun a := ⟨PowerSeries.rescale μ a.val, isConvergentPS_rescale μ a.property⟩
  map_one' := Subtype.ext (map_one (PowerSeries.rescale μ))
  map_mul' a b := Subtype.ext (map_mul (PowerSeries.rescale μ) a.val b.val)
  map_zero' := Subtype.ext (map_zero (PowerSeries.rescale μ))
  map_add' a b := Subtype.ext (map_add (PowerSeries.rescale μ) a.val b.val)

private lemma rescaleConv_injective {μ : ℂ} (hμ : μ ≠ 0) : Function.Injective (rescaleConv μ) := by
  intro a b h
  apply Subtype.ext
  ext n
  have hv := congrArg (fun x : ConvergentPowerSeries => PowerSeries.coeff n x.val) h
  simp only [rescaleConv, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    PowerSeries.coeff_rescale] at hv
  exact mul_left_cancel₀ (pow_ne_zero n hμ) hv

private lemma d_u_C_mulH (c : ℂ) (S : PowerSeries ℂ) :
    d_u (PowerSeries.C c * S) = PowerSeries.C c * d_u S := by
  ext n
  cases n with
  | zero => simp [d_u]
  | succ n =>
    cases n with
    | zero => simp [d_u, PowerSeries.coeff_X_pow_mul']
    | succ m =>
      simp only [d_u, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
      split_ifs with h
      · simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul]; ring
      · simp

private lemma d_u_rescaleH {μ : ℂ} (hμ : μ ≠ 0) (S : PowerSeries ℂ) :
    d_u (PowerSeries.rescale μ S) = PowerSeries.C μ⁻¹ * PowerSeries.rescale μ (d_u S) := by
  ext n
  cases n with
  | zero =>
    change -(PowerSeries.coeff 0 (PowerSeries.X ^ 2 * PowerSeries.derivative (PowerSeries.rescale μ S))) =
      PowerSeries.coeff 0 (PowerSeries.C μ⁻¹ * PowerSeries.rescale μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_neg,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
    simp
  | succ n =>
    cases n with
    | zero =>
      change -(PowerSeries.coeff 1 (PowerSeries.X ^ 2 * PowerSeries.derivative (PowerSeries.rescale μ S))) =
        PowerSeries.coeff 1 (PowerSeries.C μ⁻¹ * PowerSeries.rescale μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_neg,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
      simp
    | succ m =>
      change -(PowerSeries.coeff (m + 2) (PowerSeries.X ^ 2 * PowerSeries.derivative (PowerSeries.rescale μ S))) =
        PowerSeries.coeff (m + 2) (PowerSeries.C μ⁻¹ * PowerSeries.rescale μ (-(PowerSeries.X ^ 2 * PowerSeries.derivative S)))
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, map_neg,
        PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
      split_ifs with hle2
      · simp only [Nat.add_sub_cancel, PowerSeries.coeff_derivative, PowerSeries.coeff_rescale]
        rw [show m + 2 = (m + 1) + 1 by omega, pow_succ']
        field_simp [hμ]; ring
      · omega

private lemma iteratedDeriv_comp_const_mul_zeroH {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    (μ : ℂ) (k : ℕ) :
    iteratedDeriv k (fun z => φ (μ * z)) 0 = μ ^ k * iteratedDeriv k φ 0 := by
  have hloc : ∀ m : ℕ, ∀ᶠ z in 𝓝 (0 : ℂ),
      iteratedDeriv m (fun w => φ (μ * w)) z = μ ^ m * iteratedDeriv m φ (μ * z) := fun m => by
    induction m with
    | zero => exact Filter.Eventually.of_forall fun _ => by simp
    | succ m ih =>
      have hdm_anal : AnalyticAt ℂ (iteratedDeriv m φ) 0 := by
        clear ih
        induction m generalizing φ with
        | zero => simpa using hφ
        | succ j ihj => rw [iteratedDeriv_succ']; exact ihj hφ.deriv
      have hcont : ContinuousAt (fun z : ℂ => μ * z) 0 := continuousAt_const.mul continuousAt_id
      have hdm_diff : ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (iteratedDeriv m φ) (μ * z) := by
        have this' := hdm_anal.eventually_analyticAt
        rw [show (0 : ℂ) = μ * 0 by ring] at this'
        exact (hcont.tendsto.eventually this').mono fun z hz => hz.differentiableAt
      filter_upwards [ih.eventually_nhds, hdm_diff] with z hzeq hzdiff
      rw [iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq hzeq]
      have hchain : HasDerivAt (fun w => μ ^ m * iteratedDeriv m φ (μ * w))
          (μ ^ m * (deriv (iteratedDeriv m φ) (μ * z) * μ)) z :=
        (hzdiff.hasDerivAt.comp z (((hasDerivAt_id z).const_mul μ).congr_deriv (mul_one μ))).const_mul (μ ^ m)
      rw [hchain.deriv, iteratedDeriv_succ]; ring
  simpa using (hloc k).self_of_nhds

private lemma d_u_iter_formalSeries_rotH {φ : ℂ → ℂ} (hφ : AnalyticAt ℂ φ 0)
    {μ : ℂ} (hμ : μ ≠ 0) (j : ℕ) :
    d_u^[j] (formalSeries (fun z => φ (μ * z))) =
      PowerSeries.C (μ⁻¹ ^ (j + 1)) * PowerSeries.rescale μ (d_u^[j] (formalSeries φ)) := by
  have h0 : formalSeries (fun z => φ (μ * z)) =
      PowerSeries.C μ⁻¹ * PowerSeries.rescale μ (formalSeries φ) := by
    ext n
    cases n with
    | zero => simp [formalSeries]
    | succ k =>
      simp only [formalSeries, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
      rw [iteratedDeriv_comp_const_mul_zeroH hφ μ k, pow_succ']
      field_simp [hμ]
  induction j with
  | zero => simpa using h0
  | succ j ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      d_u_C_mulH, d_u_rescaleH hμ, ← mul_assoc, ← map_mul, ← pow_succ]

/-- **Universal Higher-Order Convergent-Germ Theorem (Arbitrary Ray `θ₀`, Arbitrary Orders `ord m ≥ 1`)**:
For ANY `h : HigherOrderBorelData φ θ₀ ω ord pp`, the formal Laplace series `formalSeries φ`
satisfies NO nonzero algebraic differential equation with coefficients in `ConvergentPowerSeries` (`ℂ{w}`). -/
theorem no_conv_ade_of_higher_order_borel
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv (formalSeries φ) Q = 0) : Q = 0 := by
  let μ : ℂ := Complex.exp (I * (θ₀ : ℂ))
  have hμ_ne : μ ≠ 0 := Complex.exp_ne_zero _
  have hμ_inv : μ⁻¹ = Complex.exp (-I * (θ₀ : ℂ)) := by
    rw [← Complex.exp_neg]; congr 1; ring
  let φ_rot : ℂ → ℂ := fun z => φ (μ * z)
  let pp_rot : ℕ → ℕ → ℂ := fun m s => μ⁻¹ ^ s * pp m s
  have hmem0 : (0 : ℂ) ∈ rotatedPuncturedWedge θ₀ h.α₀ h.ε ω := by
    refine ⟨Or.inl (by simp [h.hε_pos]), ?_⟩
    rintro ⟨m, hm⟩
    have hm_re := congrArg Complex.re hm
    simp only [mul_zero, Complex.zero_re, Complex.ofReal_re] at hm_re
    linarith [lt_of_lt_of_le h.ω_pos (h.ω_mono.monotone (Nat.zero_le m))]
  have hφ0 : AnalyticAt ℂ φ 0 := h.analyticOn 0 hmem0
  have h_rot : HigherOrderBorelData φ_rot 0 ω ord pp_rot :=
    { α₀ := h.α₀
      θ := h.θ
      ε := h.ε
      hθ_pos := h.hθ_pos
      hθ_lt := h.hθ_lt
      hα₀_lt := h.hα₀_lt
      hε_pos := h.hε_pos
      ω_pos := h.ω_pos
      ω_mono := h.ω_mono
      ord_pos := h.ord_pos
      pp_lead_ne_zero := fun m => mul_ne_zero (pow_ne_zero _ (inv_ne_zero hμ_ne)) (h.pp_lead_ne_zero m)
      analyticOn := fun z hz => by
        have hz_rot : μ * z ∈ rotatedPuncturedWedge θ₀ h.α₀ h.ε ω := by
          rw [rotatedPuncturedWedge_zero_eq] at hz
          change Complex.exp (-I * (θ₀ : ℂ)) * (μ * z) ∈ puncturedWedge h.α₀ h.ε ω
          rw [← mul_assoc, ← hμ_inv, inv_mul_cancel₀ hμ_ne, one_mul]; exact hz
        exact (h.analyticOn (μ * z) hz_rot).comp (analyticAt_const.mul analyticAt_id)
      pole_principalPart := fun m => by
        obtain ⟨L, hL⟩ := h.pole_principalPart m
        refine ⟨L, ?_⟩
        have htend_mul : Tendsto (fun z : ℂ => μ * z) (𝓝[≠] (ω m : ℂ)) (𝓝[≠] (μ * (ω m : ℂ))) := by
          rw [tendsto_nhdsWithin_iff]
          exact ⟨(continuous_const.mul continuous_id).continuousAt.continuousWithinAt,
            eventually_nhdsWithin_of_forall fun z hz heq => hz (mul_left_cancel₀ hμ_ne heq)⟩
        have hcomp := hL.comp htend_mul
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
        refine hcomp.congr' (eventually_nhdsWithin_of_forall fun z _ => ?_)
        simp only [Function.comp_def, φ_rot]
        congr 1
        refine Finset.sum_congr rfl fun s _ => ?_
        dsimp only [pp_rot]
        rw [← mul_sub, mul_pow, inv_pow]
        field_simp [hμ_ne]
      expType_plus := by
        obtain ⟨C, D, hC, hD, hbd⟩ := h.expType_plus
        refine ⟨C, D, hC, hD, fun v hv => ?_⟩
        have h_exp : μ * Complex.exp (I * (h.θ : ℂ)) = Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ)) := by
          dsimp only [μ]; rw [← Complex.exp_add]; congr 1; push_cast; ring
        have h_eq : Minor.pull (Complex.exp (I * ((0 + h.θ : ℝ) : ℂ))) φ_rot v =
            μ⁻¹ * Minor.pull (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ))) φ v := by
          simp only [Minor.pull, φ_rot, zero_add]
          rw [← mul_assoc (μ : ℂ), h_exp]
          calc Complex.exp (I * (h.θ : ℂ)) * φ (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ)) * (v : ℂ))
              = (μ⁻¹ * (μ * Complex.exp (I * (h.θ : ℂ)))) *
                  φ (Complex.exp (I * ((θ₀ + h.θ : ℝ) : ℂ)) * (v : ℂ)) := by
                rw [← mul_assoc, inv_mul_cancel₀ hμ_ne, one_mul]
            _ = _ := by rw [h_exp, mul_assoc]
        have hnorm_inv : ‖μ⁻¹‖ = 1 := by
          rw [hμ_inv, show -I * (θ₀ : ℂ) = ((-θ₀ : ℝ) : ℂ) * I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I (-θ₀)
        rw [h_eq, norm_mul, hnorm_inv, one_mul]; exact hbd v hv
      expType_minus := by
        obtain ⟨C, D, hC, hD, hbd⟩ := h.expType_minus
        refine ⟨C, D, hC, hD, fun v hv => ?_⟩
        have h_exp : μ * Complex.exp (I * ((-h.θ : ℝ) : ℂ)) =
            Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ)) := by
          dsimp only [μ]; rw [← Complex.exp_add]; congr 1; push_cast; ring
        have h_eq : Minor.pull (Complex.exp (I * ((0 - h.θ : ℝ) : ℂ))) φ_rot v =
            μ⁻¹ * Minor.pull (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ))) φ v := by
          simp only [Minor.pull, φ_rot, zero_sub]
          rw [← mul_assoc (μ : ℂ), h_exp]
          calc Complex.exp (I * ((-h.θ : ℝ) : ℂ)) *
                  φ (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ)) * (v : ℂ))
              = (μ⁻¹ * (μ * Complex.exp (I * ((-h.θ : ℝ) : ℂ)))) *
                  φ (Complex.exp (I * ((θ₀ - h.θ : ℝ) : ℂ)) * (v : ℂ)) := by
                rw [← mul_assoc, inv_mul_cancel₀ hμ_ne, one_mul]
            _ = _ := by rw [h_exp, mul_assoc]
        have hnorm_inv : ‖μ⁻¹‖ = 1 := by
          rw [hμ_inv, show -I * (θ₀ : ℂ) = ((-θ₀ : ℝ) : ℂ) * I by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I (-θ₀)
        rw [h_eq, norm_mul, hnorm_inv, one_mul]; exact hbd v hv }
  let g_rot : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ConvergentPowerSeries := fun j =>
    MvPolynomial.C (convC (μ ^ (j.val + 1))) * MvPolynomial.X j
  let Q_rot : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries :=
    MvPolynomial.aeval g_rot (MvPolynomial.map (rescaleConv μ) Q)
  have hQ_rot_eval : ∀ R : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries,
      formalEvalConv (formalSeries φ_rot)
        (MvPolynomial.aeval g_rot (MvPolynomial.map (rescaleConv μ) R)) =
      PowerSeries.rescale μ (formalEvalConv (formalSeries φ) R) := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C a =>
      simp only [MvPolynomial.map_C, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
        formalEvalConv, MvPolynomial.eval₂_C]
      rfl
    | add A B hA hB =>
      simp only [map_add, formalEvalConv, MvPolynomial.eval₂_add] at hA hB ⊢
      rw [hA, hB]
    | mul_X A j hA =>
      simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, formalEvalConv,
        MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at hA ⊢
      rw [hA]
      congr 1
      dsimp only [g_rot, φ_rot]
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
        toPS_convC, d_u_iter_formalSeries_rotH hφ0 hμ_ne j.val, ← mul_assoc, ← map_mul,
        ← mul_pow, mul_inv_cancel₀ hμ_ne, one_pow, map_one, one_mul]
  have hQrot0 : formalEvalConv (formalSeries φ_rot) Q_rot = 0 := by
    rw [hQ_rot_eval Q, hQ, map_zero]
  have hrot_eq0 : Q_rot = 0 := no_conv_ade_of_higher_order_borel_zero h_rot Q_rot hQrot0
  have hu : ∀ j : Fin (r + 1), IsUnit (convC (μ ^ (j.val + 1))) := fun j =>
    isUnit_iff_exists_inv.mpr ⟨convC (μ⁻¹ ^ (j.val + 1)), by
      rw [← map_mul, ← mul_pow, mul_inv_cancel₀ hμ_ne, one_pow, map_one]⟩
  have hmap0 : MvPolynomial.map (rescaleConv μ) Q = 0 :=
    triangular_aeval_injective g_rot (fun j => convC (μ ^ (j.val + 1))) hu (fun _ => 0)
      (fun j => by simp [g_rot]) (fun _ _ hk => by simp at hk) (hrot_eq0.trans (map_zero _).symm)
  exact MvPolynomial.map_injective (rescaleConv μ) (rescaleConv_injective hμ_ne)
    (hmap0.trans (map_zero _).symm)

/-- **Asymptotic-Transfer Strong `ℂ{1/u}` Theorem**:
Any function `f : ℝ → ℂ` sharing the all-orders `1/u` asymptotic expansion `d_u^[j] (formalSeries φ)`
of ANY `HigherOrderBorelData φ θ₀ ω ord pp` satisfies NO nonzero algebraic differential equation
with convergent-germ coefficients `Q ∈ ℂ{1/u}[Y_0, ..., Y_r]` eventually as `u → +∞`. -/
theorem no_conv_ade_of_higher_order_borel_asymp
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp)
    {f : ℝ → ℂ}
    (hf_asymp : ∀ j : ℕ, HasAsympExp (iteratedDeriv j f) (d_u^[j] (formalSeries φ)))
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) :
    Q = 0 := by
  have hexp : HasAsympExp
      (fun u : ℝ => MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u)
        (evalConvMvPoly Q (u : ℂ)⁻¹))
      (formalEvalConv (formalSeries φ) Q) :=
    HasAsympExp.mvPolynomial_evalConv (fun j => hf_asymp j.val) Q
  have hflat : ∀ M : ℕ, ∃ C : ℝ, ∀ᶠ u : ℝ in Filter.atTop,
      ‖MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val f u)
        (evalConvMvPoly Q (u : ℂ)⁻¹)‖ ≤ C / u ^ M := fun M => by
    refine ⟨0, ?_⟩
    filter_upwards [hQ] with u hu
    simp [hu]
  exact no_conv_ade_of_higher_order_borel h Q (hexp.eq_zero_of_flat hflat)

/-! ### 3. Invertible Triangular `ℂ{t}` Transfers & Immediate Strong `ℂ({t})` Flagship Corollaries -/

/-! #### 3A. Triangular `X * F → F` Transfer & `ℂ{t}` Shift / Multiplication Closure -/

private lemma d_u_mulH (A B : PowerSeries ℂ) : d_u (A * B) = d_u A * B + A * d_u B := by
  simp only [d_u, Derivation.leibniz, smul_eq_mul]; ring

private lemma d_u_X_powH (m : ℕ) :
    d_u (PowerSeries.X ^ m : PowerSeries ℂ) = -(PowerSeries.C (m : ℂ) * PowerSeries.X ^ (m + 1)) := by
  cases m with
  | zero => simp [d_u]
  | succ m =>
    rw [d_u, PowerSeries.derivative_pow, PowerSeries.derivative_X, mul_one, Nat.succ_sub_one]
    have hm : ((m + 1 : ℕ) : PowerSeries ℂ) = PowerSeries.C ((m + 1 : ℕ) : ℂ) := by
      rw [← map_natCast PowerSeries.C]
    rw [hm]; ring

private def backCoeffH : ℕ → ℕ → ℂ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | j + 1, 0 => -((j + 1 : ℕ) : ℂ) * backCoeffH j 0
  | j + 1, k + 1 => -((j + k + 2 : ℕ) : ℂ) * backCoeffH j (k + 1) - backCoeffH j k

private lemma backCoeffH_gt {j k : ℕ} (hk : j < k) : backCoeffH j k = 0 := by
  induction j generalizing k with
  | zero => cases k with | zero => omega | succ m => rfl
  | succ j ih =>
    cases k with
    | zero => omega
    | succ m => simp [backCoeffH, ih (by omega : j < m + 1), ih (by omega : j < m)]

private lemma backCoeffH_diag (j : ℕ) : backCoeffH j j = (-1 : ℂ) ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [backCoeffH, backCoeffH_gt (Nat.lt_succ_self j), mul_zero, zero_sub, ih, pow_succ]; ring

private lemma X_pow_mul_seriesJetH (F : PowerSeries ℂ) (j : ℕ) :
    PowerSeries.X ^ (2 * j + 1) * seriesJet F j =
      ∑ k ∈ Finset.range (j + 1),
        PowerSeries.C (backCoeffH j k) * PowerSeries.X ^ (j - k) * d_u^[k] (PowerSeries.X * F) := by
  let S : PowerSeries ℂ := PowerSeries.X * F
  induction j with
  | zero => simp [seriesJet, backCoeffH]
  | succ j ih =>
    have hdu_lhs :
        d_u (PowerSeries.X ^ (2 * j + 1) * seriesJet F j) =
          -(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * PowerSeries.X ^ (2 * j + 2) * seriesJet F j) -
            PowerSeries.X ^ (2 * (j + 1) + 1) * seriesJet F (j + 1) := by
      rw [d_u_mulH, d_u_X_powH]
      have hdu_jet : d_u (seriesJet F j) = -(PowerSeries.X ^ 2 * seriesJet F (j + 1)) := by
        rw [d_u, seriesJet, seriesJet, Function.iterate_succ_apply']
      rw [hdu_jet, show (2 * j + 1) + 1 = 2 * j + 2 by omega,
        show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega, pow_add]
      ring
    have hstep_lhs :
        PowerSeries.X ^ (2 * (j + 1) + 1) * seriesJet F (j + 1) =
          -(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * PowerSeries.X) *
              (PowerSeries.X ^ (2 * j + 1) * seriesJet F j) -
            d_u (PowerSeries.X ^ (2 * j + 1) * seriesJet F j) := by
      rw [hdu_lhs, show 2 * j + 2 = 1 + (2 * j + 1) by omega, pow_add, pow_one]; ring
    rw [hstep_lhs, ih]
    have h_first :
        -(PowerSeries.C ((2 * j + 1 : ℕ) : ℂ) * PowerSeries.X) *
            ∑ k ∈ Finset.range (j + 1),
              PowerSeries.C (backCoeffH j k) * PowerSeries.X ^ (j - k) * d_u^[k] S =
          ∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeffH j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show j + 1 - k = 1 + (j - k) by omega, pow_add, pow_one, map_mul, map_neg]; ring
    have h_du_sum :
        d_u (∑ k ∈ Finset.range (j + 1),
              PowerSeries.C (backCoeffH j k) * PowerSeries.X ^ (j - k) * d_u^[k] S) =
          ∑ k ∈ Finset.range (j + 1),
            (PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeffH j k) *
                PowerSeries.X ^ (j + 1 - k) * d_u^[k] S +
              PowerSeries.C (backCoeffH j k) * PowerSeries.X ^ (j + 1 - (k + 1)) *
                d_u^[k + 1] S) := by
      have h_lin : ∀ (s : Finset ℕ) (f : ℕ → PowerSeries ℂ), d_u (∑ k ∈ s, f k) = ∑ k ∈ s, d_u (f k) := by
        intro s f; simp only [d_u, map_sum, Finset.mul_sum, Finset.sum_neg_distrib]
      rw [h_lin]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [mul_assoc (PowerSeries.C (backCoeffH j k)), d_u_C_mulH, d_u_mulH, d_u_X_powH,
        ← Function.iterate_succ_apply' d_u k S,
        show j + 1 - k = (j - k) + 1 by omega, show j + 1 - (k + 1) = j - k by omega]
      simp only [map_mul, map_neg]; ring
    rw [h_first, h_du_sum, Finset.sum_add_distrib]
    let A (k : ℕ) : PowerSeries ℂ :=
      PowerSeries.C (-((j + k + 1 : ℕ) : ℂ) * backCoeffH j k) * PowerSeries.X ^ (j + 1 - k) * d_u^[k] S
    let B (k : ℕ) : PowerSeries ℂ :=
      PowerSeries.C (backCoeffH j k) * PowerSeries.X ^ (j + 1 - (k + 1)) * d_u^[k + 1] S
    have h_comb_A :
        ∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeffH j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S -
          ∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeffH j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S =
          ∑ k ∈ Finset.range (j + 1), A k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hcast : ((j - k : ℕ) : ℂ) = (j : ℂ) - (k : ℂ) := by rw [Nat.cast_sub hk_le]
      have hcoeff :
          (-((2 * j + 1 : ℕ) : ℂ) * backCoeffH j k) - (-((j - k : ℕ) : ℂ) * backCoeffH j k) =
            -((j + k + 1 : ℕ) : ℂ) * backCoeffH j k := by rw [hcast]; push_cast; ring
      dsimp only [A]; rw [← hcoeff, map_sub, sub_mul, sub_mul]
    have h_sub_all :
        (∑ k ∈ Finset.range (j + 1), A k) - (∑ k ∈ Finset.range (j + 1), B k) =
          ∑ k ∈ Finset.range (j + 2),
            PowerSeries.C (backCoeffH (j + 1) k) * PowerSeries.X ^ (j + 1 - k) * d_u^[k] S := by
      have hA_ext : ∑ k ∈ Finset.range (j + 1), A k = ∑ k ∈ Finset.range (j + 2), A k := by
        rw [Finset.sum_range_succ (n := j + 1) A]
        have hA_end : A (j + 1) = 0 := by simp [A, backCoeffH_gt (Nat.lt_succ_self j)]
        rw [hA_end, add_zero]
      have hB_ext :
          ∑ k ∈ Finset.range (j + 1), B k =
            ∑ k ∈ Finset.range (j + 2), (if k = 0 then (0 : PowerSeries ℂ) else B (k - 1)) := by
        rw [Finset.sum_range_succ' (n := j + 1) (fun k => if k = 0 then 0 else B (k - 1))]; simp
      rw [hA_ext, hB_ext, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      cases k with
      | zero => simp [A, backCoeffH]
      | succ k =>
        simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, A, B, backCoeffH]
        have hcoeff :
            (-((j + (k + 1) + 1 : ℕ) : ℂ) * backCoeffH j (k + 1)) - backCoeffH j k =
              -((j + k + 2 : ℕ) : ℂ) * backCoeffH j (k + 1) - backCoeffH j k := by push_cast; ring
        rw [← hcoeff, map_sub, sub_mul, sub_mul]
    calc
      (∑ k ∈ Finset.range (j + 1),
          PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeffH j k) *
            PowerSeries.X ^ (j + 1 - k) * d_u^[k] S) -
        ((∑ k ∈ Finset.range (j + 1),
            PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeffH j k) *
              PowerSeries.X ^ (j + 1 - k) * d_u^[k] S) +
          ∑ k ∈ Finset.range (j + 1), B k)
          = ((∑ k ∈ Finset.range (j + 1),
              PowerSeries.C (-((2 * j + 1 : ℕ) : ℂ) * backCoeffH j k) *
                PowerSeries.X ^ (j + 1 - k) * d_u^[k] S) -
              (∑ k ∈ Finset.range (j + 1),
                PowerSeries.C (-((j - k : ℕ) : ℂ) * backCoeffH j k) *
                  PowerSeries.X ^ (j + 1 - k) * d_u^[k] S)) -
            ∑ k ∈ Finset.range (j + 1), B k := by ring
      _ = (∑ k ∈ Finset.range (j + 1), A k) - ∑ k ∈ Finset.range (j + 1), B k := by rw [h_comb_A]
      _ = _ := h_sub_all

/-- **Pure-Algebra `ℂ{t}` Transfer (`X * F → F`)**:
If `X * F` satisfies no nonzero `d_u`-ADE over `ConvergentPowerSeries`, then `F` satisfies
no nonzero `d/dX`-ADE over `ConvergentPowerSeries` (`StronglyDTransOverConvergent F`). -/
theorem stronglyDTransOverConvergent_of_X_mul_no_conv_ade {F : PowerSeries ℂ}
    (hno : ∀ {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries),
      formalEvalConv (PowerSeries.X * F) Q = 0 → Q = 0) :
    StronglyDTransOverConvergent F := by
  classical
  intro r P hP
  let S : PowerSeries ℂ := PowerSeries.X * F
  let M : ℕ := (2 * r + 1) * P.totalDegree
  let jetConv (j : Fin (r + 1)) : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries :=
    ∑ k ∈ Finset.univ.filter (fun k : Fin (r + 1) => k.val ≤ j.val),
      MvPolynomial.C (convC (backCoeffH j.val k.val) * convX ^ (j.val - k.val)) * MvPolynomial.X k
  have hjet_eval : ∀ j : Fin (r + 1),
      formalEvalConv S (jetConv j) = PowerSeries.X ^ (2 * j.val + 1) * seriesJet F j.val := by
    intro j
    rw [X_pow_mul_seriesJetH F j.val]
    dsimp only [formalEvalConv, jetConv]
    rw [MvPolynomial.eval₂_sum]
    simp_rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, map_mul,
      map_pow, toPS_convC, toPS_convX]
    refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
    · intro k hk
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hk).2)
    · intro k₁ _ k₂ _ he; exact Fin.ext he
    · intro k hk
      have hkj : k ≤ j.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      refine ⟨⟨k, lt_of_le_of_lt hkj j.isLt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkj⟩, rfl⟩
    · intro _ _; rfl
  let wt (m : Fin (r + 1) →₀ ℕ) : ℕ := m.sum fun j e => (2 * j.val + 1) * e
  have hwt_le : ∀ m ∈ P.support, wt m ≤ M := fun m hm => by
    have hdeg : (m.sum fun _ e => e) ≤ P.totalDegree := MvPolynomial.le_totalDegree hm
    have hterm : ∀ j ∈ m.support, (2 * j.val + 1) * m j ≤ (2 * r + 1) * m j := fun j _ =>
      Nat.mul_le_mul_right (m j) (by have := j.isLt; omega)
    calc wt m = ∑ j ∈ m.support, (2 * j.val + 1) * m j := rfl
      _ ≤ ∑ j ∈ m.support, (2 * r + 1) * m j := Finset.sum_le_sum hterm
      _ = (2 * r + 1) * ∑ j ∈ m.support, m j := (Finset.mul_sum _ _ _).symm
      _ ≤ (2 * r + 1) * P.totalDegree := Nat.mul_le_mul_left _ hdeg
  let P_S : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries :=
    ∑ m ∈ P.support, MvPolynomial.C (P.coeff m * convX ^ (M - wt m)) *
      m.prod fun j e => jetConv j ^ e
  have hPS_eval : formalEvalConv S P_S = 0 := by
    have heq : formalEvalConv S P_S =
        PowerSeries.X ^ M * MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet F j.val) P := by
      dsimp only [P_S, formalEvalConv]
      rw [MvPolynomial.eval₂_sum]
      conv_rhs => rw [MvPolynomial.eval₂_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, map_mul, map_pow, toPS_convX]
      have hprod : MvPolynomial.eval₂ toPS (fun i : Fin (r + 1) => d_u^[i.val] S)
            (m.prod fun j e => jetConv j ^ e) =
          PowerSeries.X ^ wt m * ∏ j ∈ m.support, seriesJet F j.val ^ m j := by
        unfold Finsupp.prod
        rw [MvPolynomial.eval₂_prod]
        have hstep : ∀ j ∈ m.support,
            MvPolynomial.eval₂ toPS (fun i : Fin (r + 1) => d_u^[i.val] S) (jetConv j ^ m j) =
              PowerSeries.X ^ ((2 * j.val + 1) * m j) * seriesJet F j.val ^ m j := fun j _ => by
          rw [MvPolynomial.eval₂_pow, show MvPolynomial.eval₂ toPS (fun i : Fin (r + 1) => d_u^[i.val] S) (jetConv j) =
            formalEvalConv S (jetConv j) from rfl, hjet_eval j, mul_pow, ← pow_mul]
        rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; rfl
      rw [hprod]
      have hexp : (PowerSeries.X : PowerSeries ℂ) ^ (M - wt m) * PowerSeries.X ^ wt m =
          PowerSeries.X ^ M := by rw [← pow_add, Nat.sub_add_cancel (hwt_le m hm)]
      calc (toPS (P.coeff m) * PowerSeries.X ^ (M - wt m)) *
            (PowerSeries.X ^ wt m * ∏ j ∈ m.support, seriesJet F j.val ^ m j)
          = toPS (P.coeff m) * (PowerSeries.X ^ (M - wt m) * PowerSeries.X ^ wt m) *
              ∏ j ∈ m.support, seriesJet F j.val ^ m j := by ring
        _ = PowerSeries.X ^ M * (toPS (P.coeff m) * ∏ j ∈ m.support, seriesJet F j.val ^ m j) := by
            rw [hexp]; ring
    rw [heq, hP, mul_zero]
  have hPS_zero : P_S = 0 := hno P_S hPS_eval
  let K := FractionRing ConvergentPowerSeries
  let alg : ConvergentPowerSeries →+* K := algebraMap ConvergentPowerSeries K
  have halg_inj : Function.Injective alg := IsFractionRing.injective ConvergentPowerSeries K
  have hconvX_ne : convX ≠ 0 := by
    intro h0
    have h1 := congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff 1 a.val) h0
    simp [convX] at h1
  have hxK_ne : alg convX ≠ 0 := fun h0 => hconvX_ne (halg_inj (h0.trans (map_zero alg).symm))
  let g : Fin (r + 1) → MvPolynomial (Fin (r + 1)) K := fun j =>
    MvPolynomial.C ((alg convX ^ (2 * j.val + 1))⁻¹) * MvPolynomial.map alg (jetConv j)
  have hmap_PS : MvPolynomial.map alg P_S =
      MvPolynomial.C (alg convX ^ M) * MvPolynomial.aeval g (MvPolynomial.map alg P) := by
    dsimp only [P_S]
    rw [map_sum]
    conv_rhs => rw [MvPolynomial.as_sum P, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [map_mul, MvPolynomial.map_C, map_mul, map_pow, MvPolynomial.map_monomial,
      MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
    unfold Finsupp.prod
    rw [map_prod]
    have hprod_g : (∏ j ∈ m.support, MvPolynomial.map alg (jetConv j ^ m j)) =
        MvPolynomial.C (alg convX ^ wt m) * ∏ j ∈ m.support, g j ^ m j := by
      have hstep : ∀ j ∈ m.support,
          MvPolynomial.map alg (jetConv j ^ m j) =
            MvPolynomial.C (alg convX ^ ((2 * j.val + 1) * m j)) * g j ^ m j := fun j _ => by
        rw [map_pow]
        have hg_eq : MvPolynomial.map alg (jetConv j) =
            MvPolynomial.C (alg convX ^ (2 * j.val + 1)) * g j := by
          dsimp only [g]
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hxK_ne), map_one, one_mul]
        rw [hg_eq, mul_pow, ← map_pow, ← pow_mul]
      rw [Finset.prod_congr rfl hstep, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum]
      rfl
    rw [hprod_g]
    have hexp : MvPolynomial.C (alg convX ^ (M - wt m)) * MvPolynomial.C (alg convX ^ wt m) =
        (MvPolynomial.C (alg convX ^ M) : MvPolynomial (Fin (r + 1)) K) := by
      rw [← map_mul, ← pow_add, Nat.sub_add_cancel (hwt_le m hm)]
    calc MvPolynomial.C (alg (P.coeff m) * alg convX ^ (M - wt m)) *
          (MvPolynomial.C (alg convX ^ wt m) * ∏ j ∈ m.support, g j ^ m j)
        = MvPolynomial.C (alg (P.coeff m)) *
            (MvPolynomial.C (alg convX ^ (M - wt m)) * MvPolynomial.C (alg convX ^ wt m)) *
            ∏ j ∈ m.support, g j ^ m j := by rw [map_mul]; ring
      _ = MvPolynomial.C (alg convX ^ M) *
            (MvPolynomial.C (alg (P.coeff m)) * ∏ j ∈ m.support, g j ^ m j) := by rw [hexp]; ring
  rw [hPS_zero, map_zero] at hmap_PS
  have hCM_ne : (MvPolynomial.C (alg convX ^ M) : MvPolynomial (Fin (r + 1)) K) ≠ 0 := fun h0 =>
    pow_ne_zero M hxK_ne (MvPolynomial.C_eq_zero.mp h0)
  have haeval0 : MvPolynomial.aeval g (MvPolynomial.map alg P) = 0 :=
    (mul_eq_zero.mp hmap_PS.symm).resolve_left hCM_ne
  let u_K : Fin (r + 1) → K := fun j =>
    (alg convX ^ (2 * j.val + 1))⁻¹ * alg (convC ((-1 : ℂ) ^ j.val))
  let S_K : Fin (r + 1) → MvPolynomial (Fin (r + 1)) K := fun j =>
    MvPolynomial.C ((alg convX ^ (2 * j.val + 1))⁻¹) *
      ∑ k ∈ Finset.univ.filter (fun k : Fin (r + 1) => k.val < j.val),
        MvPolynomial.C (alg (convC (backCoeffH j.val k.val) * convX ^ (j.val - k.val))) * MvPolynomial.X k
  have hu_K : ∀ j : Fin (r + 1), IsUnit (u_K j) := fun j => by
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hxK_ne)) ?_)
    intro h0
    have hc0 : convC ((-1 : ℂ) ^ j.val) = 0 := halg_inj (h0.trans (map_zero alg).symm)
    have hcoeff0 := congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff 0 a.val) hc0
    simp [convC] at hcoeff0
  have hg_tri : ∀ j : Fin (r + 1), g j = MvPolynomial.C (u_K j) * MvPolynomial.X j + S_K j := fun j => by
    dsimp only [g, u_K, S_K, jetConv]
    have hsplit : Finset.univ.filter (fun k : Fin (r + 1) => k.val ≤ j.val) =
        insert j (Finset.univ.filter (fun k : Fin (r + 1) => k.val < j.val)) := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hj_not : j ∉ Finset.univ.filter (fun k : Fin (r + 1) => k.val < j.val) := by simp
    rw [hsplit, Finset.sum_insert hj_not, map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X,
      Nat.sub_self, pow_zero, mul_one, backCoeffH_diag, map_sum, mul_add]
    congr 1
    · rw [map_mul, mul_assoc]
    · congr 1
      refine Finset.sum_congr rfl fun k _ => by rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
  have hS_vars : ∀ j : Fin (r + 1), ∀ k ∈ (S_K j).vars, k.val < j.val := by
    intro j k hk
    dsimp only [S_K] at hk
    rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk) with hc | hs
    · exact absurd hc (by rw [MvPolynomial.vars_C]; simp)
    · obtain ⟨i, hi, hk_i⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hs)
      rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk_i) with hc2 | hx
      · exact absurd hc2 (by rw [MvPolynomial.vars_C]; simp)
      · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx
        subst hx; exact (Finset.mem_filter.mp hi).2
  have hmapP0 : MvPolynomial.map alg P = 0 :=
    triangular_aeval_injective g u_K hu_K S_K hg_tri hS_vars (haeval0.trans (map_zero _).symm)
  exact MvPolynomial.map_injective alg halg_inj (hmapP0.trans (map_zero _).symm)

private lemma seriesJet_addH (F G : PowerSeries ℂ) (j : ℕ) :
    seriesJet (F + G) j = seriesJet F j + seriesJet G j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [seriesJet, Function.iterate_succ_apply'] at ih ⊢
    rw [ih, map_add]

private lemma seriesJet_convDerivH (a : ConvergentPowerSeries) (j : ℕ) :
    seriesJet a.val j = (convDeriv^[j] a).val := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [seriesJet, Function.iterate_succ_apply'] at ih ⊢
    rw [ih]; rfl

/-- Adding ANY convergent power series `a ∈ ℂ{t}` preserves strong D-transcendence over `ℂ{t}`. -/
theorem stronglyDTransOverConvergent_add_conv {F : PowerSeries ℂ}
    (hF : StronglyDTransOverConvergent F) (a : ConvergentPowerSeries) :
    StronglyDTransOverConvergent (F + a.val) := by
  intro r P hP
  let g : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ConvergentPowerSeries := fun j =>
    MvPolynomial.X j + MvPolynomial.C (convDeriv^[j.val] a)
  let Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries := MvPolynomial.aeval g P
  have hQ_eval : ∀ R : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries,
      MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet F j.val) (MvPolynomial.aeval g R) =
      MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet (F + a.val) j.val) R := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C c => simp [MvPolynomial.algebraMap_eq]
    | add A B hA hB => simp only [map_add, MvPolynomial.eval₂_add] at hA hB ⊢; rw [hA, hB]
    | mul_X A j hA =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at hA ⊢
      rw [hA]
      congr 1
      simp only [g, MvPolynomial.eval₂_add, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
        toPS_apply, seriesJet_addH, seriesJet_convDerivH]
  have hQ0 : Q = 0 := hF Q (by rw [hQ_eval P, hP])
  refine triangular_aeval_injective g (fun _ => 1) (fun _ => isUnit_one)
    (fun j => MvPolynomial.C (convDeriv^[j.val] a))
    (fun j => by simp [g]) (fun j k hk => by rw [MvPolynomial.vars_C] at hk; simp at hk)
    (hQ0.trans (map_zero _).symm)

/-- Adding ANY convergent power series `a ∈ ℂ{t}` preserves strong D-transcendence over `ℂ({t})`. -/
theorem stronglyDTransOverMeromorphicGerms_add_conv {F : PowerSeries ℂ}
    (hF : StronglyDTransOverConvergent F) (a : ConvergentPowerSeries) :
    StronglyDTransOverMeromorphicGerms (F + a.val) :=
  stronglyDTransOverMeromorphicGerms_of_convergent (stronglyDTransOverConvergent_add_conv hF a)

private def mulJetMat (a : ConvergentPowerSeries) : ℕ → ℕ → ConvergentPowerSeries
  | 0, 0 => a
  | 0, _ + 1 => 0
  | j + 1, 0 => convDeriv (mulJetMat a j 0)
  | j + 1, i + 1 => convDeriv (mulJetMat a j (i + 1)) + mulJetMat a j i

private lemma mulJetMat_eq_zero_of_lt (a : ConvergentPowerSeries) :
    ∀ {j i : ℕ}, j < i → mulJetMat a j i = 0 := by
  intro j
  induction j with
  | zero => intro i hi; cases i with | zero => omega | succ _ => rfl
  | succ j ih =>
    intro i hi
    cases i with
    | zero => omega
    | succ i' =>
      simp only [mulJetMat, ih (by omega : j < i' + 1), ih (by omega : j < i'), add_zero]
      exact Subtype.ext (map_zero PowerSeries.derivative)

private lemma mulJetMat_diag (a : ConvergentPowerSeries) (j : ℕ) :
    mulJetMat a j j = a := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [mulJetMat, mulJetMat_eq_zero_of_lt a (Nat.lt_succ_self j), ih]
    have hd0 : convDeriv 0 = 0 := Subtype.ext (map_zero PowerSeries.derivative)
    rw [hd0, zero_add]

private lemma seriesJet_mul_conv (a : ConvergentPowerSeries) (F : PowerSeries ℂ) (j : ℕ) :
    seriesJet (a.val * F) j =
      ∑ i ∈ Finset.range (j + 1), (mulJetMat a j i).val * seriesJet F i := by
  induction j with
  | zero => simp [seriesJet, mulJetMat]
  | succ j ih =>
    have hsucc : seriesJet (a.val * F) (j + 1) = PowerSeries.derivative (seriesJet (a.val * F) j) := by
      dsimp only [seriesJet]; rw [Function.iterate_succ_apply']
    rw [hsucc, ih, map_sum]
    have hterm_deriv : ∀ i ∈ Finset.range (j + 1),
        PowerSeries.derivative ((mulJetMat a j i).val * seriesJet F i) =
          (convDeriv (mulJetMat a j i)).val * seriesJet F i +
          (mulJetMat a j i).val * seriesJet F (i + 1) := fun i _ => by
      have hs : PowerSeries.derivative (seriesJet F i) = seriesJet F (i + 1) := by
        dsimp only [seriesJet]; rw [Function.iterate_succ_apply']
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hs, add_comm, mul_comm (seriesJet F i)]
      rfl
    rw [Finset.sum_congr rfl hterm_deriv, Finset.sum_add_distrib]
    have hsum1 : ∑ i ∈ Finset.range (j + 1), (convDeriv (mulJetMat a j i)).val * seriesJet F i =
        (convDeriv (mulJetMat a j 0)).val * seriesJet F 0 +
        ∑ i ∈ Finset.range j, (convDeriv (mulJetMat a j (i + 1))).val * seriesJet F (i + 1) := by
      rw [Finset.sum_range_succ', add_comm]
    have hsum2 : ∑ i ∈ Finset.range (j + 1), (mulJetMat a j i).val * seriesJet F (i + 1) =
        (∑ i ∈ Finset.range j, (mulJetMat a j i).val * seriesJet F (i + 1)) +
        (mulJetMat a j j).val * seriesJet F (j + 1) := Finset.sum_range_succ _ j
    rw [hsum1, hsum2, Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [mulJetMat, mulJetMat_eq_zero_of_lt a (Nat.lt_succ_self j)]
    have hd0 : convDeriv 0 = 0 := Subtype.ext (map_zero PowerSeries.derivative)
    rw [hd0, zero_add]
    have hcomb : ∑ i ∈ Finset.range j,
          (convDeriv (mulJetMat a j (i + 1)) + mulJetMat a j i).val * seriesJet F (i + 1) =
        (∑ i ∈ Finset.range j, (convDeriv (mulJetMat a j (i + 1))).val * seriesJet F (i + 1)) +
        ∑ i ∈ Finset.range j, (mulJetMat a j i).val * seriesJet F (i + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by
        change ((convDeriv (mulJetMat a j (i + 1))).val + (mulJetMat a j i).val) * _ = _; ring
    rw [hcomb]; ring

/-- Multiplying by ANY nonzero convergent power series `a ∈ ℂ{t}` preserves strong D-transcendence
over `ℂ{t}`. -/
theorem stronglyDTransOverConvergent_mul_conv {F : PowerSeries ℂ}
    (hF : StronglyDTransOverConvergent F) {a : ConvergentPowerSeries} (ha : a ≠ 0) :
    StronglyDTransOverConvergent (a.val * F) := by
  classical
  intro r P hP
  let g : Fin (r + 1) → MvPolynomial (Fin (r + 1)) ConvergentPowerSeries := fun j =>
    ∑ i : Fin (r + 1), MvPolynomial.C (mulJetMat a j.val i.val) * MvPolynomial.X i
  let Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries := MvPolynomial.aeval g P
  have hQ_eval : ∀ R : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries,
      MvPolynomial.eval₂ toPS (fun i : Fin (r + 1) => seriesJet F i.val) (MvPolynomial.aeval g R) =
      MvPolynomial.eval₂ toPS (fun j : Fin (r + 1) => seriesJet (a.val * F) j.val) R := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C c => simp [MvPolynomial.algebraMap_eq]
    | add A B hA hB => simp only [map_add, MvPolynomial.eval₂_add] at hA hB ⊢; rw [hA, hB]
    | mul_X A j hA =>
      simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at hA ⊢
      rw [hA]; congr 1
      dsimp only [g]
      rw [MvPolynomial.eval₂_sum]
      simp_rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, toPS_apply]
      rw [seriesJet_mul_conv a F j.val, Fin.sum_univ_eq_sum_range
        (fun i => (mulJetMat a j.val i).val * seriesJet F i) (r + 1)]
      symm
      refine Finset.sum_subset (Finset.range_mono (Nat.succ_le_of_lt j.isLt)) fun i _ hnot => ?_
      have hgt : j.val < i := by rw [Finset.mem_range] at hnot; omega
      rw [mulJetMat_eq_zero_of_lt a hgt, Subring.coe_zero, zero_mul]
  have hQ0 : Q = 0 := hF Q (by rw [hQ_eval P, hP])
  let K := FractionRing ConvergentPowerSeries
  let alg : ConvergentPowerSeries →+* K := algebraMap ConvergentPowerSeries K
  have halg_inj : Function.Injective alg := IsFractionRing.injective ConvergentPowerSeries K
  have haK_ne : alg a ≠ 0 := fun h0 => ha (halg_inj (h0.trans (map_zero alg).symm))
  let gK : Fin (r + 1) → MvPolynomial (Fin (r + 1)) K := fun j => MvPolynomial.map alg (g j)
  have hmap_gen : ∀ R : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries,
      MvPolynomial.aeval gK (MvPolynomial.map alg R) = MvPolynomial.map alg (MvPolynomial.aeval g R) := by
    intro R
    induction R using MvPolynomial.induction_on with
    | C c => simp [MvPolynomial.algebraMap_eq]
    | add A B hA hB => simp only [map_add] at hA hB ⊢; rw [hA, hB]
    | mul_X A j hA => simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, gK] at hA ⊢; rw [hA]
  have haeval0 : MvPolynomial.aeval gK (MvPolynomial.map alg P) = 0 := by
    rw [hmap_gen P, show MvPolynomial.aeval g P = Q from rfl, hQ0, map_zero]
  let S_K : Fin (r + 1) → MvPolynomial (Fin (r + 1)) K := fun j =>
    ∑ i ∈ Finset.univ.filter (fun i : Fin (r + 1) => i.val < j.val),
      MvPolynomial.C (alg (mulJetMat a j.val i.val)) * MvPolynomial.X i
  have hg_split : ∀ j : Fin (r + 1),
      gK j = MvPolynomial.C (alg a) * MvPolynomial.X j + S_K j := fun j => by
    dsimp only [gK, g, S_K]
    rw [map_sum, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j),
      map_mul, MvPolynomial.map_C, MvPolynomial.map_X, mulJetMat_diag a j.val]
    congr 1
    simp_rw [map_mul, MvPolynomial.map_C, MvPolynomial.map_X]
    symm
    refine Finset.sum_subset (fun i hi => Finset.mem_erase.mpr
      ⟨fun h => (Finset.mem_filter.mp hi).2.ne (congrArg Fin.val h), Finset.mem_univ i⟩)
      (fun i hi hnot => ?_)
    have hne : i ≠ j := (Finset.mem_erase.mp hi).1
    have hnotlt : ¬ i.val < j.val := fun h => hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    have hgt : j.val < i.val := lt_of_le_of_ne (Nat.le_of_not_lt hnotlt) (fun h => hne (Fin.ext h.symm))
    rw [mulJetMat_eq_zero_of_lt a hgt, map_zero, map_zero, zero_mul]
  have hS_vars : ∀ j : Fin (r + 1), ∀ k ∈ (S_K j).vars, k.val < j.val := by
    intro j k hk
    dsimp only [S_K] at hk
    obtain ⟨i, hi, hk_i⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_sum_subset _ _ hk)
    rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hk_i) with hc | hx
    · exact absurd hc (by rw [MvPolynomial.vars_C]; simp)
    · rw [MvPolynomial.vars_X, Finset.mem_singleton] at hx
      subst hx; exact (Finset.mem_filter.mp hi).2
  have hmapP0 : MvPolynomial.map alg P = 0 :=
    triangular_aeval_injective gK (fun _ => alg a) (fun _ => isUnit_iff_ne_zero.mpr haK_ne)
      S_K hg_split hS_vars (haeval0.trans (map_zero _).symm)
  exact MvPolynomial.map_injective alg halg_inj (hmapP0.trans (map_zero _).symm)

/-! #### 3B. Universal `EGF → OGF` & `formalSeries φ` Strong `ℂ({t})` Master Theorems -/

/-- **General Meromorphic EGF → Strongly D-Transcendental OGF over `ℂ{t}`**:
For ANY analytic EGF `E : ℂ → ℂ` with `HigherOrderBorelData E θ₀ ω ord pp`,
`ogfOfEGF E = ∑_{n ≥ 0} E^{(n)}(0) t^n` satisfies NO nonzero ADE over `ConvergentPowerSeries` (`ℂ{t}`). -/
theorem ogf_stronglyDTransOverConvergent_of_higherOrderBorel
    {E : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData E θ₀ ω ord pp) :
    StronglyDTransOverConvergent (ogfOfEGF E) :=
  stronglyDTransOverConvergent_of_X_mul_no_conv_ade fun Q hQ => by
    rw [← formalSeries_eq_X_mul_ogfOfEGF] at hQ
    exact no_conv_ade_of_higher_order_borel h Q hQ

/-- **General Meromorphic EGF → Strongly D-Transcendental OGF over `ℂ({t})`**:
For ANY analytic EGF `E : ℂ → ℂ` with `HigherOrderBorelData E θ₀ ω ord pp`,
`ogfOfEGF E = ∑_{n ≥ 0} E^{(n)}(0) t^n` is **strongly differentially transcendental over
convergent meromorphic germs `ℂ({t})`** (`FractionRing ConvergentPowerSeries`). -/
theorem ogf_stronglyDTrans_of_higherOrderBorel
    {E : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData E θ₀ ω ord pp) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF E) :=
  stronglyDTransOverMeromorphicGerms_of_convergent
    (ogf_stronglyDTransOverConvergent_of_higherOrderBorel h)

/-- **Universal Strong `ℂ{w}` D-Transcendence of `formalSeries φ` (`d/dw`)**:
For ANY `h : HigherOrderBorelData φ θ₀ ω ord pp`, `formalSeries φ = ∑_{k ≥ 0} φ^{(k)}(0) w^{k+1}`
satisfies NO nonzero `d/dw`-ADE over `ConvergentPowerSeries` (`ℂ{w}`). -/
theorem stronglyDTransOverConvergent_of_higher_order_borel
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp) :
    StronglyDTransOverConvergent (formalSeries φ) := by
  have hconvX_ne : convX ≠ 0 := by
    intro h0
    have h1 := congrArg (fun a : ConvergentPowerSeries => PowerSeries.coeff 1 a.val) h0
    simp [convX] at h1
  rw [formalSeries_eq_X_mul_ogfOfEGF]
  change StronglyDTransOverConvergent (convX.val * ogfOfEGF φ)
  exact stronglyDTransOverConvergent_mul_conv
    (ogf_stronglyDTransOverConvergent_of_higherOrderBorel h) hconvX_ne

/-- **Universal Strong `ℂ({w})` D-Transcendence of `formalSeries φ`**:
For ANY `h : HigherOrderBorelData φ θ₀ ω ord pp`, `formalSeries φ` is **strongly differentially
transcendental over convergent meromorphic germs `ℂ({w})`** (`FractionRing ConvergentPowerSeries`). -/
theorem stronglyDTrans_of_higher_order_borel
    {φ : ℂ → ℂ} {θ₀ : ℝ} {ω : ℕ → ℝ} {ord : ℕ → ℕ} {pp : ℕ → ℕ → ℂ}
    (h : HigherOrderBorelData φ θ₀ ω ord pp) :
    StronglyDTransOverMeromorphicGerms (formalSeries φ) :=
  stronglyDTransOverMeromorphicGerms_of_convergent
    (stronglyDTransOverConvergent_of_higher_order_borel h)

/-! #### 3C. Unconditional Classical Combinatorial OGF Flagships over `ℂ({t})` -/

/-- **Flagship 1 (Bernoulli Numbers OGF over `ℂ({t})`)**:
`bernOGF = ∑_{n ≥ 0} B_n t^n` is unconditionally **strongly differentially transcendental over
convergent meromorphic germs `ℂ({t})`** (matching Klazar 2003 & Bostan–Di Vizio–Raschel Theorem 3). -/
theorem bernOGF_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms bernOGF := by
  let a : ConvergentPowerSeries := polyToConv (Polynomial.C 1 - Polynomial.C (1 / 2 : ℂ) * Polynomial.X)
  have hshift : bernOGF = ogfOfEGF phiBern + a.val := by
    ext n
    have hbern : bernOGF = ogfOfEGF bernEGF := ogfOfEGF_bernEGF.symm
    rw [hbern]
    have hlin_an : AnalyticAt ℂ (fun ξ : ℂ => (1 : ℂ) - ξ / 2) 0 :=
      analyticAt_const.sub (analyticAt_id.mul analyticAt_const)
    have hphi_an : AnalyticAt ℂ phiBern 0 := by
      have h0 : (0 : ℂ) ∈ rotatedPuncturedWedge (Real.pi / 2) phiBern_borelData.α₀
          phiBern_borelData.ε (fun m : ℕ => 2 * Real.pi * ((m : ℝ) + 1)) := by
        refine ⟨Or.inl (by simp [phiBern_borelData.hε_pos]), ?_⟩
        rintro ⟨m, hm⟩
        have hre := congrArg Complex.re hm
        simp only [mul_zero, Complex.zero_re, Complex.ofReal_re] at hre
        have hpos : 0 < 2 * Real.pi * ((m : ℝ) + 1) := by positivity
        linarith
      exact phiBern_borelData.analyticOn 0 h0
    have hfn : bernEGF = phiBern + fun ξ : ℂ => (1 : ℂ) - ξ / 2 := funext bernEGF_eq_phiBern_add
    simp only [ogfOfEGF, PowerSeries.coeff_mk, map_add, hfn,
      iteratedDeriv_add (hphi_an.contDiffAt.of_le le_top) (hlin_an.contDiffAt.of_le le_top)]
    congr 1
    change iteratedDeriv n (fun ξ : ℂ => (1 : ℂ) - ξ / 2) 0 =
      PowerSeries.coeff n ((Polynomial.C 1 - Polynomial.C (1 / 2 : ℂ) * Polynomial.X : Polynomial ℂ) : PowerSeries ℂ)
    rw [Polynomial.coeff_coe]
    rcases n with _ | _ | k
    · simp
    · have hder : deriv (fun ξ : ℂ => (1 : ℂ) - ξ / 2) 0 = -(2⁻¹ : ℂ) := by simp
      rw [iteratedDeriv_one, hder, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
      norm_num
    · have hdlin : deriv (fun ξ : ℂ => (1 : ℂ) - ξ / 2) = fun _ => -(2⁻¹ : ℂ) := by
        ext ξ; simp
      have h0 : iteratedDeriv (k + 2) (fun ξ : ℂ => (1 : ℂ) - ξ / 2) 0 = 0 := by
        rw [iteratedDeriv_succ', hdlin, iteratedDeriv_succ', deriv_const', iteratedDeriv_const]
        simp
      rw [h0, Polynomial.coeff_sub, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
      simp
  rw [hshift]
  exact stronglyDTransOverMeromorphicGerms_add_conv
    (ogf_stronglyDTransOverConvergent_of_higherOrderBorel phiBern_borelData) a

/-- **Flagship 2 (Tangent / Odd Euler Numbers OGF over `ℂ({t})`)**:
`ogfOfEGF Complex.tan` is unconditionally **strongly differentially transcendental over `ℂ({t})`**. -/
theorem tanOGF_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF Complex.tan) :=
  ogf_stronglyDTrans_of_higherOrderBorel tan_borelData

/-- **Flagship 3 (Secant / Even Euler Numbers OGF over `ℂ({t})`)**:
`ogfOfEGF (fun ξ => (Complex.cos ξ)⁻¹)` is unconditionally **strongly differentially transcendental over `ℂ({t})`**. -/
theorem secOGF_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF fun ξ => (Complex.cos ξ)⁻¹) :=
  ogf_stronglyDTrans_of_higherOrderBorel sec_borelData

/-- **Flagship 4 (Double-Pole `sec²` OGF over `ℂ({t})`)**:
`ogfOfEGF (fun ξ => (Complex.cos ξ)⁻¹ ^ 2)` is unconditionally **strongly differentially transcendental over `ℂ({t})`**. -/
theorem sec2OGF_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF fun ξ => (Complex.cos ξ)⁻¹ ^ 2) :=
  ogf_stronglyDTrans_of_higherOrderBorel sec2_borelData

/-- **Flagship 5 (Arbitrary-Order `sec^p` OGF over `ℂ({t})`)**:
For every `p ≥ 1`, `ogfOfEGF (fun ξ => (Complex.cos ξ)⁻¹ ^ p)` is unconditionally **strongly
differentially transcendental over `ℂ({t})`**. -/
theorem secPowOGF_stronglyDTrans (p : ℕ) (hp : 1 ≤ p) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF fun ξ => (Complex.cos ξ)⁻¹ ^ p) :=
  ogf_stronglyDTrans_of_higherOrderBorel (secPow_borelData p hp)

/-- **Flagship 6 (General Briot–Bouquet Rational-Exponential OGFs over `ℂ({t})`)**:
For ANY `lam ≠ 0`, `‖c‖ = 1` (`c ≠ 1`), and `p ≥ 1`,
`ogfOfEGF (fun ξ => (1 - c * Complex.exp (lam * ξ))⁻¹ ^ p)` is unconditionally **strongly
differentially transcendental over `ℂ({t})`**. -/
theorem ratExpOGF_stronglyDTrans (lam c : ℂ) (hlam : lam ≠ 0) (hc_norm : ‖c‖ = 1)
    (hc_ne : c ≠ 1) (p : ℕ) (hp : 1 ≤ p) :
    StronglyDTransOverMeromorphicGerms
      (ogfOfEGF fun ξ => (1 - c * Complex.exp (lam * ξ))⁻¹ ^ p) :=
  ogf_stronglyDTrans_of_higherOrderBorel (ratExp_borelData lam c hlam hc_norm hc_ne p hp)

/-- **Flagship 7 (Euler / Genocchi Arbitrary-Order `(1 + e^ξ)^{-p}` OGFs over `ℂ({t})`)**:
For every `p ≥ 1`, `ogfOfEGF (fun ξ => (1 + Complex.exp ξ)⁻¹ ^ p)` is unconditionally **strongly
differentially transcendental over `ℂ({t})`**. -/
theorem eulerGenocchiPowOGF_stronglyDTrans (p : ℕ) (hp : 1 ≤ p) :
    StronglyDTransOverMeromorphicGerms
      (ogfOfEGF fun ξ => (1 + Complex.exp ξ)⁻¹ ^ p) := by
  have h := ratExpOGF_stronglyDTrans (1 : ℂ) (-1 : ℂ) one_ne_zero (by simp) (by norm_num) p hp
  simpa [sub_neg_eq_add, one_mul] using h

/-- **Flagship 8 (Hurwitz / Trigamma Double-Pole OGF over `ℂ({t})`)**:
`ogfOfEGF trigammaSeries` is unconditionally **strongly differentially transcendental over `ℂ({t})`**. -/
theorem trigammaOGF_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF trigammaSeries) :=
  ogf_stronglyDTrans_of_higherOrderBorel trigammaSeries_borelData

/-- **Flagship 9 (Rotated Lambert Divisor Double-Pole OGF over `ℂ({t})`)**:
For any `θ₀ : ℝ`, `ogfOfEGF (lambertBorelSeries θ₀)` is unconditionally **strongly differentially
transcendental over `ℂ({t})`**. -/
theorem lambertOGF_stronglyDTrans (θ₀ : ℝ) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (lambertBorelSeries θ₀)) :=
  ogf_stronglyDTrans_of_higherOrderBorel (lambertBorelSeries_borelData θ₀)

/-- **Flagship 10 (Rotated Triple-Pole OGF over `ℂ({t})`)**:
For any `θ₀ : ℝ`, `ogfOfEGF (triplePoleSeries θ₀)` is unconditionally **strongly differentially
transcendental over `ℂ({t})`**. -/
theorem triplePoleOGF_stronglyDTrans (θ₀ : ℝ) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (triplePoleSeries θ₀)) :=
  ogf_stronglyDTrans_of_higherOrderBorel (triplePoleSeries_borelData θ₀)

/-- **Flagship 11 (General Higher-Order Dirichlet-Pole OGFs over `ℂ({t})`)**:
For any `p ≥ 2`, `θ₀ : ℝ`, and nonzero summable coefficients `c : ℕ → ℂ`,
`ogfOfEGF (dirichletPoleSeries c θ₀ p)` is unconditionally **strongly differentially transcendental
over `ℂ({t})`**. -/
theorem dirichletPoleOGF_stronglyDTrans
    (c : ℕ → ℂ) (θ₀ : ℝ) (p : ℕ) (hp : 2 ≤ p)
    (hc_ne : ∀ n : ℕ, 1 ≤ n → c n ≠ 0)
    (hsumm : Summable (fun n : ℕ => ‖c (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ p)) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (dirichletPoleSeries c θ₀ p)) :=
  ogf_stronglyDTrans_of_higherOrderBorel (dirichletPoleSeries_borelData c θ₀ p hp hc_ne hsumm)

/-! #### 3D. Riemann Hypothesis Critical-Line Strong `ℂ({1/u})` Flagships -/

/-- **RH Flagship 1 (`ℂ{1/u}` Formal `d_u`-Transcendence of `G_Lambda`)**:
Under Mathlib's literal `RiemannHypothesis` and `InfinitelyManyCriticalLineZeros`, the formal
Von Mangoldt critical-line Borel–Laplace series `G_Lambda` satisfies NO nonzero algebraic
differential equation with coefficients in `ConvergentPowerSeries` (`ℂ{1/u}`). -/
theorem riemannHypothesis_implies_G_Lambda_no_conv_ade
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : formalEvalConv G_Lambda Q = 0) : Q = 0 :=
  no_conv_ade_of_higher_order_borel (phiLambda_higherOrderBorelData hRH hInf) Q hQ

/-- **RH Flagship 2 (`ℂ({1/u})` Strong Differential Transcendence of `G_Lambda`)**:
Under Mathlib's literal `RiemannHypothesis` and `InfinitelyManyCriticalLineZeros`, `G_Lambda` is
**strongly differentially transcendental over convergent meromorphic germs `ℂ({1/u})`**
(`FractionRing ConvergentPowerSeries`). -/
theorem riemannHypothesis_implies_G_Lambda_stronglyDTrans
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros) :
    StronglyDTransOverMeromorphicGerms G_Lambda :=
  stronglyDTrans_of_higher_order_borel (phiLambda_higherOrderBorelData hRH hInf)

/-- **RH Flagship 3 (`ℂ{1/u}` Analytic Differential Transcendence of `G_Lambda_laplace`)**:
Under Mathlib's literal `RiemannHypothesis` and `InfinitelyManyCriticalLineZeros`, the regularized
real-axis Laplace integral `G_Lambda_laplace` satisfies NO nonzero convergent-germ algebraic
differential equation over `ℂ{1/u}` eventually as `u → +∞`. -/
theorem riemannHypothesis_implies_G_Lambda_laplace_no_conv_ade
    (hRH : RiemannHypothesis) (hInf : InfinitelyManyCriticalLineZeros)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val G_Lambda_laplace u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) : Q = 0 :=
  no_conv_ade_of_higher_order_borel_asymp (phiLambda_higherOrderBorelData hRH hInf)
    (G_Lambda_laplace_hasAsympExp hRH) Q hQ

end
end PakPrimes.HigherOrderStrongDTrans
