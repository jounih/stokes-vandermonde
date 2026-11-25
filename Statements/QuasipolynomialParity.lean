module

public import PakPrimes.QuasipolynomialEulerParity
public import PakPrimes.QuasipolynomialIFF

/-!
# Statements Audit Ledger: Quasipolynomial Euler-Product Parity Dichotomy

Thin statement ledger re-stating the flagship theorems from
`PakPrimes.QuasipolynomialEulerParity` and `PakPrimes.QuasipolynomialIFF` using the
project's definitions, each checked by the Lean 4 kernel with strictly
`[propext, Classical.choice, Quot.sound]`.

## Definitions used
- `Quasipoly`, `Quasipoly.eval`, `Quasipoly.oddPart`: `PakPrimes/QuasipolynomialEulerParity.lean:79`
- `lambertSeries`: `PakPrimes/QuasipolynomialEulerParity.lean:583`
- `eulerProduct`: `PakPrimes/QuasipolynomialEulerParity.lean:626`
- `PakPrimes.HarmonicTrap.bose`, `hasProd_bose`: `PakPrimes/HarmonicTrapShift.lean:130-142`
- `seriesCoordinates`: `PakPrimes/AutonomousTransfer.lean:65`
- `jointCoords`: `PakPrimes/QuasipolynomialIFF.lean:1447`
- `conformalScalarPoly`, `conformalScalarSphereQP`: `PakPrimes/QuasipolynomialIFF.lean:9580,9685`

See `docs/quasipolynomial-parity.md` for explicit scope boundaries (including what is
and is not formalized in v3.0.0).
-/

public section

namespace Statements.QuasipolynomialParity

open scoped PowerSeries.WithPiTopology
open Filter PowerSeries PakPrimes.PrimeNome PakPrimes.QuasipolynomialEulerParity
open PakPrimes.QuasipolynomialIFF

/-! ### Textbook-pinning checks on project definitions -/

/-- `PakPrimes.HarmonicTrap.bose g` is the literal convergent infinite product
`∏' i, ((1 - X^(i+1))⁻¹)^(g (i+1))` in `PowerSeries.WithPiTopology`. -/
example (g : ℕ → ℕ) :
    HasProd (fun i : ℕ => ((1 - (X : PowerSeries ℂ) ^ (i + 1))⁻¹) ^ (g (i + 1)))
      (PakPrimes.HarmonicTrap.bose g) :=
  PakPrimes.HarmonicTrap.hasProd_bose g

/-- For `g : ℕ → ℕ`, the recurrence-defined `eulerProduct` equals the literal product `bose g`. -/
example (g : ℕ → ℕ) :
    eulerProduct (fun n => (g n : ℂ)) = PakPrimes.HarmonicTrap.bose g :=
  eulerProduct_eq_bose g

/-- The `n`-th coefficient of `lambertSeries w` is `∑_{d ∣ n} d · w(d)` for `n ≥ 1` (and `0` for `n = 0`). -/
example (w : ℕ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (lambertSeries w) =
      if n = 0 then 0 else ∑ d ∈ Nat.divisors n, (d : ℂ) * w d := by
  simp [lambertSeries]

/-- On `S²`, `conformalScalarPoly 2` evaluates to `j` (exact spherical harmonic multiplicity at `j = 2ℓ + 1`). -/
example (j : ℂ) : (conformalScalarPoly 2).eval j = j := by
  simp [conformalScalarPoly]

/-- On `S³`, `conformalScalarPoly 3` evaluates to `j² / 4` (exact multiplicity `(ℓ + 1)²` at `j = 2ℓ + 2`). -/
example (j : ℂ) : (conformalScalarPoly 3).eval j = j ^ 2 / 4 := by
  simp [conformalScalarPoly]
  ring

/-! ### Flagship theorems -/

/-- Master Theorem A: any pure quasipolynomial `P` with nonzero odd part `P⁻` has
a D-transcendental Lambert series `H_P(q) = ∑_{n ≥ 1} P(n) q^n / (1 - q^n)` over `ℂ(q)`. -/
theorem quasipoly_lambert_pure_dTrans (P : Quasipoly)
    (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) :
    AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries (fun n => P.eval (n : ℤ)))) :=
  quasipoly_lambert_pure_algebraicIndependent P hodd

/-- Master Theorem B: finite-perturbation invariance for Lambert series `H_w(q)`
eventually agreeing with a quasipolynomial `P` having `P⁻ ≠ 0`. -/
theorem quasipoly_lambert_eventually_dTrans (P : Quasipoly)
    (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) {w : ℕ → ℂ}
    (hw : ∀ᶠ n : ℕ in atTop, w n = P.eval (n : ℤ)) :
    AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries w)) :=
  quasipoly_lambert_algebraicIndependent P hodd hw

/-- Master Theorem D: weighted Euler products `G_w(q) = ∏_{n ≥ 1} (1 - q^n)^{-w(n)}`
eventually agreeing with a quasipolynomial `P` having `P⁻ ≠ 0` are D-transcendental over `ℂ(q)`. -/
theorem quasipoly_eulerProduct_eventually_dTrans (P : Quasipoly)
    (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) {w : ℕ → ℂ}
    (hw : ∀ᶠ n : ℕ in atTop, w n = P.eval (n : ℤ)) :
    AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct w)) :=
  quasipoly_eulerProduct_algebraicIndependent P hodd hw

/-- Master Theorem E: literal infinite Bose–Euler products `PakPrimes.HarmonicTrap.bose g`
with `g : ℕ → ℕ` eventually agreeing with a quasipolynomial `P` having `P⁻ ≠ 0`. -/
theorem quasipoly_bose_eventually_dTrans (P : Quasipoly)
    (hodd : ∃ n : ℤ, P.oddPart n ≠ 0) {g : ℕ → ℕ}
    (hg : ∀ᶠ n : ℕ in atTop, (g n : ℂ) = P.eval (n : ℤ)) :
    AlgebraicIndependent ℂ (seriesCoordinates (PakPrimes.HarmonicTrap.bose g)) :=
  quasipoly_bose_algebraicIndependent P hodd hg

/-- Showcase: partitions into parts `≡ 1 mod 5` (`∏_{n ≡ 1 (5)} (1 - q^n)^{-1}`) are
D-transcendental over `ℂ(q)`, contrasting with the modular Rogers–Ramanujan product (`±1 mod 5`). -/
theorem partsMod5One_dTrans :
    AlgebraicIndependent ℂ
      (seriesCoordinates (PakPrimes.HarmonicTrap.bose (fun n => if n % 5 = 1 then 1 else 0))) :=
  partsMod5One_algebraicIndependent

/-- Complete IFF dichotomy for all period-1 (polynomial) weights: Lambert series. -/
theorem period1_lambert_iff (P : Quasipoly) (hM : P.M = 1) :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries (fun n => P.eval (n : ℤ)))) ↔
      ∀ n : ℤ, P.oddPart n = 0 :=
  quasipoly_period1_lambert_iff P hM

/-- Complete IFF dichotomy for all period-1 (polynomial) weights: Euler products. -/
theorem period1_eulerProduct_iff (P : Quasipoly) (hM : P.M = 1) :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct (fun n => P.eval (n : ℤ)))) ↔
      ∀ n : ℤ, P.oddPart n = 0 :=
  quasipoly_period1_eulerProduct_iff P hM

/-- Complete IFF dichotomy for all period-2 quasipolynomials: Lambert series. -/
theorem period2_lambert_iff (P : Quasipoly) (hM : P.M = 2) :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (lambertSeries (fun n => P.eval (n : ℤ)))) ↔
      ∀ n : ℤ, P.oddPart n = 0 :=
  quasipoly_period2_lambert_iff P hM

/-- Complete IFF dichotomy for all period-2 quasipolynomials: Euler products. -/
theorem period2_eulerProduct_iff (P : Quasipoly) (hM : P.M = 2) :
    ¬ AlgebraicIndependent ℂ (seriesCoordinates (eulerProduct (fun n => P.eval (n : ℤ)))) ↔
      ∀ n : ℤ, P.oddPart n = 0 :=
  quasipoly_period2_eulerProduct_iff P hM

/-- Unconditional 3-tuple joint differential independence over `ℂ(q)` of MacMahon's `M(q)`,
partitions into parts `≡ 1 mod 5`, and partitions into parts `≡ 2 mod 5`. -/
theorem macMahon_partsMod5One_partsMod5Two_joint_dIndep :
    AlgebraicIndependent ℂ (jointCoords
      ![PakPrimes.DivisorAndMacMahon.macmahonSeries,
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 1 then 1 else 0),
        PakPrimes.HarmonicTrap.bose (fun n : ℕ => if n % 5 = 2 then 1 else 0)]) :=
  macMahon_partsMod5One_partsMod5Two_euler_joint_algIndep

/-- All-dimension conformal scalar parity theorem (`∀ s ≥ 2`): the thermal partition function
`Z_{S^s}` (in the `j = 2E` variable `x = q^{1/2}`) of a free conformal scalar on `S^s` is
D-algebraic over `ℂ(x)` iff `Odd s`. -/
theorem conformalScalar_allDim_sphere_iff {s : ℕ} (hs : 2 ≤ s) :
    ¬ AlgebraicIndependent ℂ
        (seriesCoordinates (eulerProduct (fun n => (conformalScalarSphereQP s).eval (n : ℤ)))) ↔
      Odd s :=
  conformalScalar_sphere_allDim_eulerProduct_iff hs

end Statements.QuasipolynomialParity

end
