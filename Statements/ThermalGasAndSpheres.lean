module

public import PakPrimes.ThermalGasParity
public import PakPrimes.ThermalGasEOS
public import PakPrimes.QuasipolynomialIFF

/-!
# Statements Audit Ledger: Relativistic Quantum Gases, Equations of State, Casimir, and Spheres

Thin statement ledger re-stating the flagship theorems from `PakPrimes.ThermalGasParity`,
`PakPrimes.ThermalGasEOS`, and `PakPrimes.QuasipolynomialIFF` using the project's
definitions, each checked by the Lean 4 kernel with strictly
`[propext, Classical.choice, Quot.sound]`.

## Definitions used
- `bosePressure2D`, `fermiPressure2D`: `PakPrimes/ThermalGasParity.lean:53,60`
- `bosePressure1D`, `fermiPressure1D`, `bosePressure3D`, `fermiPressure3D`: `PakPrimes/ThermalGasParity.lean:1997-2013`
- `energyDensity`, `soundSpeedSq`: `PakPrimes/ThermalGasEOS.lean:843,847`
- `casimirEnergy1D/2D/3D`, `casimirForce1D/2D/3D`: `PakPrimes/ThermalGasEOS.lean:2734-2739`
- `conformalScalarSphereQP`: `PakPrimes/QuasipolynomialIFF.lean:9685`

See `docs/thermal-gas-and-spheres.md` for explicit scope notes (including the `j = 2E`
sphere variable convention).
-/

public section

namespace Statements.ThermalGasAndSpheres

open scoped Topology
open PakPrimes.HigherOrderStokes PakPrimes.ThermalGasParity PakPrimes.ThermalGasEOS
open PakPrimes.PrimeNome PakPrimes.QuasipolynomialEulerParity PakPrimes.QuasipolynomialIFF

/-! ### Textbook-pinning checks on thermodynamic definitions -/

/-- Thermodynamic energy density is `ε(T) = T · P'(T) - P(T)`. -/
example (P : ℝ → ℝ) (T : ℝ) : energyDensity P T = T * deriv P T - P T := rfl

/-- Squared sound speed is `c_s²(ε) = p'(ε)`. -/
example (p : ℝ → ℝ) (ε : ℝ) : soundSpeedSq p ε = deriv p ε := rfl

/-! ### Flagship theorems -/

/-- Relativistic ideal gas dimensional parity at zero chemical potential (`m > 0`):
2D Bose and Fermi pressures are D-algebraic (explicit order-3 ODEs); 1D and 3D Bose and Fermi
pressures satisfy no nonzero algebraic differential equation over `ℂ(T)`. -/
theorem ideal_gas_dimensional_parity {m : ℝ} (hm : 0 < m) :
    (∃ P : MvPolynomial (Fin 4) (Polynomial ℂ), P ≠ 0 ∧
      ∀ T : ℝ, 0 < T →
        MvPolynomial.eval
          (fun j : Fin 4 => iteratedDeriv j.val (fun t : ℝ => (bosePressure2D m t : ℂ)) T)
          (evalU P (T : ℂ)) = 0) ∧
    (∃ P : MvPolynomial (Fin 4) (Polynomial ℂ), P ≠ 0 ∧
      ∀ T : ℝ, 0 < T →
        MvPolynomial.eval
          (fun j : Fin 4 => iteratedDeriv j.val (fun t : ℝ => (fermiPressure2D m t : ℂ)) T)
          (evalU P (T : ℂ)) = 0) ∧
    (∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ T : ℝ, 0 < T →
        (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (bosePressure1D m t : ℂ)) T)
          (evalRatU P (T : ℂ)) = 0) → P = 0) ∧
    (∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ T : ℝ, 0 < T →
        (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (fermiPressure1D m t : ℂ)) T)
          (evalRatU P (T : ℂ)) = 0) → P = 0) ∧
    (∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ T : ℝ, 0 < T →
        (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (bosePressure3D m t : ℂ)) T)
          (evalRatU P (T : ℂ)) = 0) → P = 0) ∧
    (∀ {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ T : ℝ, 0 < T →
        (∀ β ∈ P.support, (P.coeff β).denom.eval (T : ℂ) ≠ 0) →
        MvPolynomial.eval
          (fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => (fermiPressure3D m t : ℂ)) T)
          (evalRatU P (T : ℂ)) = 0) → P = 0) :=
  relativistic_ideal_gas_dimensional_parity hm

/-- Unconditional 3D relativistic Bose equation of state `p(ε)` and squared sound speed
`c_s²(ε) = p'(ε)`: neither satisfies any nonzero ADE over `ℂ(ε)`. -/
theorem bose_eos_3D_dTrans {m : ℝ} (hm : 0 < m)
    {p : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) p U)
    {T₀ : ℝ} (hT₀ : 0 < T₀) (hE₀_mem : energyDensity (bosePressure3D m) T₀ ∈ U)
    (heos : ∀ᶠ T in 𝓝 T₀, p (energyDensity (bosePressure3D m) T) = bosePressure3D m T) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (soundSpeedSq p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) :=
  boseEOS3D_no_rat_ade hm hU hp_smooth hT₀ hE₀_mem heos

/-- Unconditional 3D relativistic Fermi equation of state `p(ε)` and squared sound speed
`c_s²(ε) = p'(ε)` (zero auxiliary derivative hypotheses): neither satisfies any nonzero ADE over `ℂ(ε)`. -/
theorem fermi_eos_3D_dTrans {m : ℝ} (hm : 0 < m)
    {p : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hp_smooth : ContDiffOn ℝ (⊤ : ℕ∞) p U)
    {T₀ : ℝ} (hT₀ : 0 < T₀) (hE₀_mem : energyDensity (fermiPressure3D m) T₀ ∈ U)
    (heos : ∀ᶠ T in 𝓝 T₀, p (energyDensity (fermiPressure3D m) T) = fermiPressure3D m T) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ ε ∈ U, (∀ β ∈ R.support, (R.coeff β).denom.eval (ε : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun e : ℝ => (soundSpeedSq p e : ℂ)) ε)
          (evalRatU R (ε : ℂ)) = 0) → R = 0) :=
  fermiEOS3D_no_rat_ade hm hU hp_smooth hT₀ hE₀_mem heos

/-- 2D massive Casimir force and energy satisfy explicit polynomial ADEs over `ℂ[L]`. -/
theorem casimir_2D_dAlgebraic {m : ℝ} (hm : 0 < m) :
    (∃ P : MvPolynomial (Fin 3) (Polynomial ℂ), P ≠ 0 ∧
      ∀ L : ℝ, 0 < L →
        MvPolynomial.eval
          (fun j : Fin 3 => iteratedDeriv j.val (fun l : ℝ => (casimirForce2D m l : ℂ)) L)
          (evalU P (L : ℂ)) = 0) ∧
    (∃ P : MvPolynomial (Fin 4) (Polynomial ℂ), P ≠ 0 ∧
      ∀ L : ℝ, 0 < L →
        MvPolynomial.eval
          (fun j : Fin 4 => iteratedDeriv j.val (fun l : ℝ => (casimirEnergy2D m l : ℂ)) L)
          (evalU P (L : ℂ)) = 0) :=
  ⟨casimirForce2D_dAlgebraic hm, casimirEnergy2D_dAlgebraic hm⟩

/-- 1D massive Casimir energy and force satisfy no nonzero ADE over `ℂ(L)`. -/
theorem casimir_1D_dTrans {m : ℝ} (hm : 0 < m) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L → (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirEnergy1D m l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) → R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L → (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirForce1D m l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) → R = 0) :=
  casimir1D_no_rat_ade hm

/-- 3D massive Casimir energy and force satisfy no nonzero ADE over `ℂ(L)`. -/
theorem casimir_3D_dTrans {m : ℝ} (hm : 0 < m) :
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L → (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirEnergy3D m l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) → R = 0) ∧
    (∀ {r : ℕ} (R : MvPolynomial (Fin (r + 1)) (RatFunc ℂ)),
      (∀ L : ℝ, 0 < L → (∀ β ∈ R.support, (R.coeff β).denom.eval (L : ℂ) ≠ 0) →
        MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (fun l : ℝ => (casimirForce3D m l : ℂ)) L)
          (evalRatU R (L : ℂ)) = 0) → R = 0) :=
  casimir3D_no_rat_ade hm

/-- All-dimension free conformal scalar on `S^s` (`∀ s ≥ 2`): `Z_{S^s}` (in the `j = 2E` variable
`x = q^{1/2}`) is D-algebraic over `ℂ(x)` iff `Odd s`. -/
theorem conformalScalar_sphere_allDim_iff {s : ℕ} (hs : 2 ≤ s) :
    ¬ AlgebraicIndependent ℂ
        (seriesCoordinates (eulerProduct (fun n => (conformalScalarSphereQP s).eval (n : ℤ)))) ↔
      Odd s :=
  conformalScalar_sphere_allDim_eulerProduct_iff hs

end Statements.ThermalGasAndSpheres

end
