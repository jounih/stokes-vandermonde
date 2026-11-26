module

public import PakPrimes.SelbergHyperbolic3DDTrans
public import PakPrimes.SelbergHyperbolicDTrans

/-!
# Statements Audit Ledger: 3D & 2D Compact Hyperbolic Selberg–Stokes–Vandermonde Theorems

Thin statement ledger re-stating the headline theorems from:

1. `PakPrimes.SelbergHyperbolic3DDTrans` — **3D compact orientable hyperbolic manifolds
   `M = ℍ³ / Γ`**: given the analytic Selberg zeta package `CompactHyperbolic3DSelbergData`
   (entire `Z`, self-adjoint 3D Selberg RH on `Re s = 1`, Weyl infinitude, right-half-plane bound,
   and pure-polynomial reflection law `Z'(1-ξ)/Z(1-ξ) + Z'(1+ξ)/Z(1+ξ) = (Vol(M)/π) ξ²`, with
   zero trivial zeros anywhere in `ℂ`), proves strong differential transcendence over convergent
   meromorphic germs `ℂ({t})` of the geodesic von Mangoldt OGF and formal Borel–Laplace series,
   together with `ℂ{1/u}` and `ℂ(u)` analytic ADE obstructions for the regularized real-axis
   Laplace integral;
2. `PakPrimes.SelbergHyperbolicDTrans` — **2D compact hyperbolic surfaces `M = ℍ² / Γ`** of
   genus `g ≥ 2`: given `CompactHyperbolicSelbergData`, proves the critical-line shifted
   functional equation `(2g - 2) · 2πξ tan(πξ)` and the analogous strong `ℂ({t})`, `ℂ{1/u}`, and
   `ℂ(u)` differential transcendence theorems.

See `docs/geometry-and-unconditional-primes.md` for explicit scope notes on the analytic input
packages.
-/

public section

namespace Statements.SelbergHyperbolic

open PakPrimes.GeneralTheorem2 PakPrimes.HigherOrderStokes PakPrimes.PakYeliussizovEGF
open PakPrimes.FishburnStrongDTrans PakPrimes.HigherOrderStrongDTrans
open PakPrimes.SelbergHyperbolic3DDTrans PakPrimes.SelbergHyperbolicDTrans

/-! ### 1. 3D Compact Orientable Hyperbolic Manifolds (`M = ℍ³ / Γ`) -/

/-- Critical-line pure-polynomial reflection law in 3D:
`Z'(1 - ξ) / Z(1 - ξ) + Z'(1 + ξ) / Z(1 + ξ) = (Vol(M) / π) ξ²`. -/
theorem selberg3D_func_eq_critical_shift (D : CompactHyperbolic3DSelbergData) {ξ : ℂ}
    (hZ1 : D.Z (1 + ξ) ≠ 0) (hZ2 : D.Z (1 - ξ) ≠ 0) :
    deriv D.Z (1 - ξ) / D.Z (1 - ξ) + deriv D.Z (1 + ξ) / D.Z (1 + ξ) =
      ((D.vol : ℂ) / (Real.pi : ℂ)) * ξ ^ 2 :=
  PakPrimes.SelbergHyperbolic3DDTrans.func_eq_critical_shift D hZ1 hZ2

/-- Strong `ℂ({t})` D-transcendence of the 3D hyperbolic geodesic von Mangoldt OGF. -/
theorem selberg3D_ogf_stronglyDTrans (D : CompactHyperbolic3DSelbergData) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (phiSelberg3D D)) :=
  PakPrimes.SelbergHyperbolic3DDTrans.selberg3D_ogf_stronglyDTrans D

/-- Strong `ℂ({t})` D-transcendence of the 3D hyperbolic formal Borel–Laplace series. -/
theorem selberg3D_formalSeries_stronglyDTrans (D : CompactHyperbolic3DSelbergData) :
    StronglyDTransOverMeromorphicGerms (formalSeries (phiSelberg3D D)) :=
  PakPrimes.SelbergHyperbolic3DDTrans.selberg3D_formalSeries_stronglyDTrans D

/-- Analytic `ℂ{1/u}` ADE obstruction for the 3D Selberg regularized real-axis Laplace integral. -/
theorem selberg3D_laplace_no_conv_ade (D : CompactHyperbolic3DSelbergData)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg3D_laplace D) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) :
    Q = 0 :=
  PakPrimes.SelbergHyperbolic3DDTrans.selberg3D_laplace_no_conv_ade D Q hQ

/-- Analytic `ℂ(u)` ADE obstruction for the 3D Selberg regularized real-axis Laplace integral. -/
theorem selberg3D_laplace_no_rat_ade (D : CompactHyperbolic3DSelbergData)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg3D_laplace D) u)
        (evalRatU P (u : ℂ)) = 0) :
    P = 0 :=
  PakPrimes.SelbergHyperbolic3DDTrans.selberg3D_laplace_no_rat_ade D P hP

/-! ### 2. 2D Compact Hyperbolic Surfaces (`M = ℍ² / Γ`, Genus `g ≥ 2`) -/

/-- Critical-line shifted Selberg functional equation in 2D:
`Z'(1/2 - ξ)/Z(1/2 - ξ) + Z'(1/2 + ξ)/Z(1/2 + ξ) = (2g - 2) · 2πξ tan(πξ)`. -/
theorem func_eq_critical_shift (D : CompactHyperbolicSelbergData) {ξ : ℂ}
    (hξ : ξ.im ≠ 0) (hZ1 : D.Z (1 / 2 + ξ) ≠ 0) (hZ2 : D.Z (1 / 2 - ξ) ≠ 0) :
    deriv D.Z (1 / 2 - ξ) / D.Z (1 / 2 - ξ) + deriv D.Z (1 / 2 + ξ) / D.Z (1 / 2 + ξ) =
      ((2 * D.g - 2 : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * ξ) * Complex.tan ((Real.pi : ℂ) * ξ) :=
  PakPrimes.SelbergHyperbolicDTrans.func_eq_critical_shift D hξ hZ1 hZ2

/-- Strong `ℂ({t})` D-transcendence of the 2D hyperbolic geodesic von Mangoldt OGF. -/
theorem selberg_ogf_stronglyDTrans (D : CompactHyperbolicSelbergData) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (phiSelberg D)) :=
  PakPrimes.SelbergHyperbolicDTrans.selberg_ogf_stronglyDTrans D

/-- Strong `ℂ({t})` D-transcendence of the 2D hyperbolic formal Borel–Laplace series. -/
theorem selberg_formalSeries_stronglyDTrans (D : CompactHyperbolicSelbergData) :
    StronglyDTransOverMeromorphicGerms (formalSeries (phiSelberg D)) :=
  PakPrimes.SelbergHyperbolicDTrans.selberg_formalSeries_stronglyDTrans D

/-- Analytic `ℂ{1/u}` ADE obstruction for the 2D Selberg regularized real-axis Laplace integral. -/
theorem selberg_laplace_no_conv_ade (D : CompactHyperbolicSelbergData)
    {r : ℕ} (Q : MvPolynomial (Fin (r + 1)) ConvergentPowerSeries)
    (hQ : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg_laplace D) u)
        (evalConvMvPoly Q (u : ℂ)⁻¹) = 0) :
    Q = 0 :=
  PakPrimes.SelbergHyperbolicDTrans.selberg_laplace_no_conv_ade D Q hQ

/-- Analytic `ℂ(u)` ADE obstruction for the 2D Selberg regularized real-axis Laplace integral. -/
theorem selberg_laplace_no_rat_ade (D : CompactHyperbolicSelbergData)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (G_Selberg_laplace D) u)
        (evalRatU P (u : ℂ)) = 0) :
    P = 0 :=
  PakPrimes.SelbergHyperbolicDTrans.selberg_laplace_no_rat_ade D P hP

end Statements.SelbergHyperbolic
