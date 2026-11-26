module

public import PakPrimes.FiniteContourStokes
public import PakPrimes.CompletedXiDTrans

/-!
# Statements Audit Ledger: Unconditional Completed-$\xi$ Strong `ℂ({t})` D-Transcendence & Finite-Contour Simple-Pole Engine

Thin statement ledger re-stating the **100% unconditional** theorems proved over **Mathlib plus
this repository's proved modules, with no extra hypotheses**, from `PakPrimes.CompletedXiDTrans`
and the core finite-contour transfer engine from `PakPrimes.FiniteContourStokes` (**ZERO
`RiemannHypothesis`**, **ZERO external data structures**, **ZERO numerical zero tables**, **ZERO
growth-at-`∞` assumptions**):

1. **Unconditional Completed-$\xi$ Flagship Theorems (`PakPrimes.CompletedXiDTrans`)**:
   - Exact entire definition `completedXi s := (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2`,
     functional equation `completedXi (1 - s) = completedXi s`, zero-free horizontal strip
     `{s : ℂ | |s.im| ≤ 1 / 2}`, critical-strip containment (`0 < Re ρ < 1`, `|Im ρ| > 1 / 2`,
     `riemannZeta ρ = 0`), and **unconditional infinitude of nontrivial zeros**
     `completedXi_zeros_infinite` proved directly from Mathlib plus this repository's proved
     modules, with no extra hypotheses (without Stirling's formula, Hadamard factorization, or
     Riemann–von Mangoldt);
   - Because `completedXi` is entire with **no trivial zeros** and **no pole at `s = 1`**, the
     transcendence results below are driven 100% by the infinitely many **nontrivial zeros** of
     `riemannZeta` in the critical strip — without assuming they lie on `Re s = 1 / 2`;
   - **Variable & object clarity:** Every differential-transcendence theorem below is in the formal
     variable `t = 1 / u` for the factorial-moment / formal-Laplace series (`ogfOfEGF (phiXiAt c)`,
     `formalSeries (phiXiAt c)`) and the real-axis Laplace integral `B_xi c u` of `-ξ'/ξ` — **NOT**
     for `ζ(s)` directly as a function of `s`;
   - Unconditional strong `ℂ({t})` differential transcendence of both `ogfOfEGF (phiXiAt c)` and
     `formalSeries (phiXiAt c)` for **every real center `c : ℝ`** (including `c = 1 / 2`,
     `phiXi_ogf_stronglyDTrans` and `phiXi_formalSeries_stronglyDTrans`);
   - **Unconditional joint multi-center strong `ℂ({t})` differential independence**
     (`completedXi_joint_ogf_stronglyDTrans`) for ANY finite injective family of real centers
     `c : Fin d → ℝ`;
   - **Unconditional real-axis Laplace integral `B_xi c`** all-orders `1 / u`-asymptotics
     (`B_xi_hasAsympExp`) and analytic `ℂ{1/u}` ADE obstruction (`completedXi_laplace_no_conv_ade`)
     at every real center `c : ℝ`.
2. **Core Finite-Contour Simple-Pole Transfer Engine over `ℂ({t})` (`PakPrimes.FiniteContourStokes`)**:
   - Sharp order-`r` finite-pole count bound (`finite_contour_pole_count_bound`);
   - Master scalar strong `ℂ({t})` D-transcendence (`finite_contour_ogf_stronglyDTrans`,
     `finite_contour_formalSeries_stronglyDTrans`) and joint multi-series differential independence
     (`finite_contour_joint_ogf_stronglyDTrans`) for plane-meromorphic Borel transforms with simple
     poles — requiring **ZERO growth at `∞`**, **ZERO global wedge**, and **ZERO collinearity**;
   - Universal entire logarithmic-derivative bridge (`entireLogDeriv_ogf_stronglyDTrans`,
     `entireLogDeriv_formalSeries_stronglyDTrans`) for `-E'(c + w) / E(c + w)` of ANY entire
     function `E` with infinitely many distinct zeros and `E c ≠ 0` (arbitrary zero multiplicities
     permitted).

For the separate, explicitly parameterized RH-free/GRH-free Cramér spectral positivity and strict
Hankel positive-definiteness theorems, see `Statements/SpectralPositivity.lean`.
See `docs/completed-xi-and-positivity.md` for full scope notes and literature attributions.
-/

public section

namespace Statements.CompletedXi

open PakPrimes.BorelStokesVandermonde PakPrimes.GeneralTheorem2 PakPrimes.PakYeliussizovEGF
open PakPrimes.FishburnStrongDTrans PakPrimes.HigherOrderStrongDTrans
open PakPrimes.FiniteContourStokes PakPrimes.CompletedXiDTrans

/-! ### 1. 100% Unconditional Completed-$\xi$ Flagship Theorems (Mathlib + Repo Modules, ZERO RH) -/

/-- Functional equation `ξ(1 - s) = ξ(s)` on all of `ℂ`. -/
theorem completedXi_one_sub (s : ℂ) : completedXi (1 - s) = completedXi s :=
  PakPrimes.CompletedXiDTrans.completedXi_one_sub s

/-- Unconditional non-vanishing of `completedXi` on the horizontal strip `{s : ℂ | |s.im| ≤ 1 / 2}`. -/
theorem completedXi_ne_zero_of_abs_im_le_half {s : ℂ} (him : |s.im| ≤ 1 / 2) :
    completedXi s ≠ 0 :=
  PakPrimes.CompletedXiDTrans.completedXi_ne_zero_of_abs_im_le_half him

/-- Every zero of `completedXi` lies strictly inside `0 < Re ρ < 1` with `|Im ρ| > 1 / 2` and is a
nontrivial zero of `riemannZeta`. -/
theorem completedXi_zero_mem_strip {ρ : ℂ} (hρ : completedXi ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 ∧ 1 / 2 < |ρ.im| ∧ riemannZeta ρ = 0 :=
  PakPrimes.CompletedXiDTrans.completedXi_zero_mem_strip hρ

/-- **100% Unconditional Infinitude of Nontrivial Zeros of `completedXi`**, proved over Mathlib
plus this repository's proved modules, with no extra hypotheses (zero RH, zero Stirling, zero
Hadamard factorization). -/
theorem completedXi_zeros_infinite : {ρ : ℂ | completedXi ρ = 0}.Infinite :=
  PakPrimes.CompletedXiDTrans.completedXi_zeros_infinite

/-- **100% Unconditional Strong `ℂ({t})` D-Transcendence of `ogfOfEGF (phiXiAt c)`** in `t = 1/u`
for the factorial-moment / formal-Laplace series of `-ξ'/ξ` at every real center `c : ℝ`
(including `c = 1 / 2`; zero RH; Mathlib plus this repository's proved modules, with no extra
hypotheses; NOT for `ζ(s)` in `s`). -/
theorem completedXi_ogf_stronglyDTrans (c : ℝ) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (phiXiAt (c : ℂ))) :=
  PakPrimes.CompletedXiDTrans.completedXi_ogf_stronglyDTrans c

/-- **100% Unconditional Strong `ℂ({t})` D-Transcendence of `formalSeries (phiXiAt c)`** in
`t = 1/u` at every real center `c : ℝ` (zero RH; Mathlib plus this repository's proved modules,
with no extra hypotheses). -/
theorem completedXi_formalSeries_stronglyDTrans (c : ℝ) :
    StronglyDTransOverMeromorphicGerms (formalSeries (phiXiAt (c : ℂ))) :=
  PakPrimes.CompletedXiDTrans.completedXi_formalSeries_stronglyDTrans c

/-- Canonical symmetric specialization at `c = 1 / 2`: `ogfOfEGF phiXi` is unconditionally
strongly D-transcendental over convergent meromorphic germs `ℂ({t})` in `t = 1/u`. -/
theorem phiXi_ogf_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF phiXi) :=
  PakPrimes.CompletedXiDTrans.phiXi_ogf_stronglyDTrans

/-- Canonical symmetric specialization at `c = 1 / 2`: `formalSeries phiXi` is unconditionally
strongly D-transcendental over convergent meromorphic germs `ℂ({t})` in `t = 1/u`. -/
theorem phiXi_formalSeries_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (formalSeries phiXi) :=
  PakPrimes.CompletedXiDTrans.phiXi_formalSeries_stronglyDTrans

/-- **100% Unconditional Joint Multi-Center Strong `ℂ({t})` Differential Independence**:
for ANY finite family of pairwise distinct real centers `c : Fin d → ℝ`, the completed-$\xi$
factorial-moment OGFs `ogfOfEGF (phiXiAt (c i))` are jointly differentially independent in
`t = 1/u` over `ℂ({t})` (zero RH). -/
theorem completedXi_joint_ogf_stronglyDTrans {d : ℕ} (c : Fin d → ℝ) (hc : Function.Injective c) :
    JointlyStronglyDTransOverMeromorphicGerms (fun i => ogfOfEGF (phiXiAt (c i : ℂ))) :=
  PakPrimes.CompletedXiDTrans.completedXi_joint_ogf_stronglyDTrans c hc

/-- Unconditional all-orders `1 / u`-asymptotic expansion of the real-axis Laplace integral
`B_xi c u` and all its derivatives at every real center `c : ℝ`. -/
theorem B_xi_hasAsympExp (c : ℝ) (j : ℕ) :
    HasAsympExp (iteratedDeriv j (B_xi c)) (d_u^[j] (formalSeries (phiXiAt (c : ℂ)))) :=
  PakPrimes.CompletedXiDTrans.B_xi_hasAsympExp c j

/-- **100% Unconditional Real-Axis Laplace Integral `ℂ{1/u}` ADE Obstruction**:
for EVERY real center `c : ℝ`, the actual real-axis Laplace integral `B_xi c u` of `-ξ'/ξ`
satisfies no nontrivial algebraic differential equation with convergent `ℂ{1/u}` coefficients
as `u → +∞` (in `u` / `1/u`, not for `ζ(s)` in `s`). -/
theorem completedXi_laplace_no_conv_ade (c : ℝ) {r : ℕ}
    (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (B_xi c) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) :
    Q = 0 :=
  PakPrimes.CompletedXiDTrans.completedXi_laplace_no_conv_ade c Q hQ

/-! ### 2. Core Finite-Contour Simple-Pole Transfer Engine over `ℂ({t})` -/

/-- Sharp finite-pole count bound: if `Q ≠ 0` is a vanishing order-`r` convergent-germ ADE for
`formalSeries b` (with `PlaneSimplePoleData b`, zero growth assumption at `∞`), then every finite
subset of `h.poles` has cardinality at most `r`. -/
theorem finite_contour_pole_count_bound {b : ℂ → ℂ} (h : PlaneSimplePoleData b)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ_ne : Q ≠ 0) (hQ : formalEvalConv (formalSeries b) Q = 0)
    (S : Finset ℂ) (hS : (S : Set ℂ) ⊆ h.poles) :
    S.card ≤ r :=
  PakPrimes.FiniteContourStokes.finite_contour_pole_count_bound h Q hQ_ne hQ S hS

/-- Master scalar finite-contour strong `ℂ({t})` D-transcendence theorem for `ogfOfEGF b`:
infinitely many simple poles suffice, with zero growth at `∞`, zero wedge, and zero collinearity. -/
theorem finite_contour_ogf_stronglyDTrans {b : ℂ → ℂ} (h : PlaneSimplePoleData b)
    (hinf : h.poles.Infinite) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF b) :=
  PakPrimes.FiniteContourStokes.finite_contour_ogf_stronglyDTrans h hinf

/-- Master scalar finite-contour strong `ℂ({t})` D-transcendence theorem for `formalSeries b`. -/
theorem finite_contour_formalSeries_stronglyDTrans {b : ℂ → ℂ} (h : PlaneSimplePoleData b)
    (hinf : h.poles.Infinite) :
    StronglyDTransOverMeromorphicGerms (formalSeries b) :=
  PakPrimes.FiniteContourStokes.finite_contour_formalSeries_stronglyDTrans h hinf

/-- Master joint multi-series finite-contour strong `ℂ({t})` differential independence theorem
via invertible joint residue-jet matrices. -/
theorem finite_contour_joint_ogf_stronglyDTrans {d : ℕ} {b : Fin d → ℂ → ℂ}
    (h : ∀ i, PlaneSimplePoleData (b i))
    (hspan : ∀ r : ℕ, ∃ ω : Fin d × Fin (r + 1) → ℂ,
      (∀ p, ω p ∈ unionPoles h) ∧
      (Matrix.of (fun p q : Fin d × Fin (r + 1) => jointVec h (ω p) q)).det ≠ 0) :
    JointlyStronglyDTransOverMeromorphicGerms (fun i => ogfOfEGF (b i)) :=
  PakPrimes.FiniteContourStokes.finite_contour_joint_ogf_stronglyDTrans h hspan

/-- Universal entire logarithmic-derivative strong `ℂ({t})` D-transcendence theorem for `ogfOfEGF`:
applies to `-E'(c + w) / E(c + w)` of ANY entire function `E` with infinitely many distinct zeros
and `E c ≠ 0` (zero growth condition, arbitrary zero multiplicities allowed). -/
theorem entireLogDeriv_ogf_stronglyDTrans {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    {c : ℂ} (hc : E c ≠ 0) (hinf : {ρ : ℂ | E ρ = 0}.Infinite) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF fun w => -deriv E (c + w) / E (c + w)) :=
  PakPrimes.FiniteContourStokes.entireLogDeriv_ogf_stronglyDTrans hE hc hinf

/-- Universal entire logarithmic-derivative strong `ℂ({t})` D-transcendence theorem for
`formalSeries`. -/
theorem entireLogDeriv_formalSeries_stronglyDTrans {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    {c : ℂ} (hc : E c ≠ 0) (hinf : {ρ : ℂ | E ρ = 0}.Infinite) :
    StronglyDTransOverMeromorphicGerms (formalSeries fun w => -deriv E (c + w) / E (c + w)) :=
  PakPrimes.FiniteContourStokes.entireLogDeriv_formalSeries_stronglyDTrans hE hc hinf

end Statements.CompletedXi
