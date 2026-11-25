module

public import PakPrimes.VolterraVirialDTrans

/-!
# Statements Audit Ledger: Sibuya's Sub-Gevrey Theorem & Volterra Virial Functions (`μ`, `ν`)

Thin statement ledger re-stating the unconditional theorems from `PakPrimes.VolterraVirialDTrans`:

1. **Sibuya's Sub-Gevrey Convergence Theorem** (`sibuya_subGevrey_convergent`,
   `sibuya_subGevrey_convergent_euler`): any sub-Gevrey formal power series solving a nonzero
   algebraic differential equation over `ℂ[x]` (in `d/dx` or Euler `x d/dx`) has positive radius
   of convergence;
2. **Unconditional D-transcendence over `ℂ(t)` of the Volterra functions `μ(t, β, α)` and `ν(t)`**
   (governing the 2D interacting Fermi-gas second virial shift and 1D 3-body third virial shift),
   both in dimensionless coupling `t` and in physical temperature `T > 0`;
3. **Exact Laplace transform** `∫_0^∞ e^{-s t} ν(t) dt = (s log s)^{-1}` for all `s > 1`.

See `docs/volterra-virial-and-sibuya.md` for explicit scope notes.
-/

public section

namespace Statements.VolterraVirial

open PowerSeries PakPrimes.VolterraVirialDTrans

/-- Sibuya's Sub-Gevrey Convergence Theorem (standard derivative `d/dx`). -/
theorem sibuya_subGevrey_convergent {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)} (hP : P ≠ 0)
    {f : PowerSeries ℂ} (hsub : IsSubGevrey f) (hf : evalDerivPS P f = 0) :
    IsConvergentPS f :=
  PakPrimes.VolterraVirialDTrans.sibuya_subGevrey_convergent hP hsub hf

/-- Sibuya's Sub-Gevrey Convergence Theorem (Euler derivative `x d/dx`). -/
theorem sibuya_subGevrey_convergent_euler {r : ℕ}
    {P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)} (hP : P ≠ 0)
    {f : PowerSeries ℂ} (hsub : IsSubGevrey f) (hf : evalEulerPS P f = 0) :
    IsConvergentPS f :=
  PakPrimes.VolterraVirialDTrans.sibuya_subGevrey_convergent_euler hP hsub hf

/-- Unconditional D-transcendence over `ℂ(t)` of the Volterra function `μ(t, β, α)` (`Re β > -1`). -/
theorem volterraMu_no_rat_ade (α β : ℂ) (hβ : -1 < β.re) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ t ∈ Set.Ioi (0 : ℝ), evalRealADE P (volterraMu β α) t = 0) : False :=
  PakPrimes.VolterraVirialDTrans.volterraMu_no_rat_ade α β hβ P hP hADE

/-- Unconditional D-transcendence over `ℂ(t)` of Volterra `ν(t)` (2D interacting Fermi gas
second virial shift). -/
theorem volterraNu_no_rat_ade {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ t ∈ Set.Ioi (0 : ℝ), evalRealADE P volterraNu t = 0) : False :=
  PakPrimes.VolterraVirialDTrans.volterraNu_no_rat_ade P hP hADE

/-- Unconditional D-transcendence in physical temperature `T ↦ ν(E_B / T)` (`E_B > 0`). -/
theorem volterraNu_temp_no_rat_ade {E_B : ℝ} (hE : 0 < E_B) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ T ∈ Set.Ioi (0 : ℝ), evalRealADE P (fun T => volterraNu (E_B / T)) T = 0) : False :=
  PakPrimes.VolterraVirialDTrans.volterraNu_temp_no_rat_ade hE P hP hADE

/-- Unconditional D-transcendence over `ℂ(t)` of the 1D 3-body third virial shift. -/
theorem fermiGas1D_virial3_no_rat_ade {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ t ∈ Set.Ioi (0 : ℝ), evalRealADE P fermiGas1D_virial3 t = 0) : False :=
  PakPrimes.VolterraVirialDTrans.fermiGas1D_virial3_no_rat_ade P hP hADE

/-- Unconditional D-transcendence in physical temperature of the 1D 3-body third virial shift. -/
theorem fermiGas1D_virial3_temp_no_rat_ade {E_B : ℝ} (hE : 0 < E_B) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ)) (hP : P ≠ 0)
    (hADE : ∀ T ∈ Set.Ioi (0 : ℝ), evalRealADE P (fun T => fermiGas1D_virial3 (E_B / T)) T = 0) :
    False :=
  PakPrimes.VolterraVirialDTrans.fermiGas1D_virial3_temp_no_rat_ade hE P hP hADE

/-- Exact Laplace transform of Volterra `ν(t)` for all `s > 1`. -/
theorem laplace_volterraNu {s : ℝ} (hs : 1 < s) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ), Complex.exp (-(s : ℂ) * (t : ℂ)) * volterraNu t =
      ((s : ℂ) * (Real.log s : ℂ))⁻¹ :=
  PakPrimes.VolterraVirialDTrans.laplace_volterraNu hs

end Statements.VolterraVirial
