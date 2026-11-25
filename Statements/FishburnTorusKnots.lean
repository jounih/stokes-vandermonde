module

public import PakPrimes.FishburnTorusKnots
public import PakPrimes.FishburnStrongDTrans

/-!
# Statements Audit Ledger: Fishburn Series (Bostan–Di Vizio–Raschel §2.2.6) & Torus-Knot Kernel Series `T(p, q)`

Thin statement ledger re-stating the flagship 100% unconditional (zero-hypothesis) theorems
from `PakPrimes.FishburnTorusKnots` (over `ℂ(x)`) and `PakPrimes.FishburnStrongDTrans`
(strong differential transcendence over the full field `ℂ({x})` of convergent meromorphic
germs at `0`):

1. Zagier's formal identity (2001, Theorem 3) formalized from scratch in `ℂ[[t]]`,
2. Differential transcendence over `ℂ(x)` **and** strong differential transcendence over `ℂ({x})`
   of the literal divergent Fishburn OGF `P(x) = ∑_{m ≥ 0} ∏_{j=1}^m (1 - (1 - x)^j)` — settling
   the open question posed in Bostan, Di Vizio, and Raschel (*Amer. J. Math.* 146(6), 2024, §2.2.6)
   both in its literal `ℂ(x)` form and in the stronger `ℂ({x})` setting of their Theorem 3 and
   Klazar (2003),
3. Differential transcendence over `ℂ(t)` and strong differential transcendence over `ℂ({t})` of
   Glaisher's `T`-number EGF `∑_{k ≥ 0} (T_k / k!) t^k`,
4. Differential transcendence over `ℂ(t)` and strong differential transcendence over `ℂ({t})` of
   the general torus-knot kernel series `∑_{k ≥ 0} ((±1)^k T_k^{(p,q)} / k!) t^k` defined from
   `sin(p s) sin(q s) / sin(p q s)` for all integers `p, q ≥ 2` (for coprime `(p, q)`, this is the
   odd-character trigonometric kernel governing the Lawrence–Zagier 1999 / Hikami 2004 asymptotic
   expansions; the link to the literal knot invariant is formalized directly in Lean for the
   trefoil `(2, 3)` via Zagier's formal identity above).

## Definitions used
- `seriesCoordinates F`: `PakPrimes/AutonomousTransfer.lean:65` (`0 ↦ X`, `k + 1 ↦ derivative^[k] F`)
- `fishburnTerm m`: `PakPrimes/FishburnTorusKnots.lean:4743` (`∏ j ∈ Finset.range m, (1 - (1 - X)^(j + 1))`)
- `fishburnSeries`: `PakPrimes/FishburnTorusKnots.lean:4766` (formal sum `∑_{m ≥ 0} fishburnTerm m`)
- `zagierSubst`: `PakPrimes/FishburnTorusKnots.lean:4806` (`1 - exp(-24 t)`)
- `torusKnotBorel p q`: `PakPrimes/FishburnTorusKnots.lean:3800` (removable-cleared `sin(p s) sin(q s) / (s sin(p q s))` at `z = s^2`)
- `torusKnotCoeff p q k`: `PakPrimes/FishburnTorusKnots.lean:4324` (`(2k+1)`-st derivative of `sin(p s) sin(q s) / sin(p q s)` at `s = 0`, matching `torusKnotCoeff_eq_iteratedDeriv`)
- `torusKnotEulerSeries p q`: `PakPrimes/FishburnTorusKnots.lean:4329` (`∑_{k ≥ 0} (T_k^{(p,q)} / k!) t^k`)
- `torusKnotPerturbativeSeries p q`: `PakPrimes/FishburnTorusKnots.lean:4334` (`∑_{k ≥ 0} ((-1)^k T_k^{(p,q)} / k!) t^k`)
- `fishburnEulerSeries`: `PakPrimes/FishburnTorusKnots.lean:4339` (`torusKnotEulerSeries 2 3`)
- `IsConvergentPS`, `ConvergentPowerSeries`: `PakPrimes/FishburnStrongDTrans.lean:56,143` (ring `ℂ{x}` of convergent power series at `0`)
- `StronglyDTransOverMeromorphicGerms`: `PakPrimes/FishburnStrongDTrans.lean:4592` (`AlgebraicIndependent (FractionRing ConvergentPowerSeries) (fun j => fracPS_of_ps (seriesJet F j))`, i.e., over `ℂ({x})`)

See `docs/fishburn-and-torus-knots.md` for explicit scope notes.
-/

public section

namespace Statements.FishburnTorusKnots

open PowerSeries PakPrimes.PrimeNome PakPrimes.FishburnTorusKnots PakPrimes.FishburnStrongDTrans

/-! ### Textbook-pinning checks on project definitions -/

/-- At every order `n`, `[x^n] fishburnSeries` agrees with every finite truncation
`∑_{m < M} [x^n] ∏_{j=1}^m (1 - (1 - x)^j)` for `M > n`. -/
example (n M : ℕ) (hM : n < M) :
    PowerSeries.coeff n fishburnSeries =
      ∑ m ∈ Finset.range M, PowerSeries.coeff n (fishburnTerm m) :=
  fishburnSeries_coeff_eq_sum hM

/-- Leading Fishburn numbers (OEIS A022493): `1, 1, 2, …`. -/
example : PowerSeries.coeff 0 fishburnSeries = 1 := fishburnSeries_coeff_zero
example : PowerSeries.coeff 1 fishburnSeries = 1 := fishburnSeries_coeff_one
example : PowerSeries.coeff 2 fishburnSeries = 2 := fishburnSeries_coeff_two

/-- `torusKnotCoeff 2 3 k` is literally the `(2k + 1)`-st derivative of `sin(2s) / (2 cos(3s))` at `s = 0`
(Glaisher's `T`-numbers `1, 23, 1681, 257543, …`, OEIS A002439). -/
example (k : ℕ) :
    torusKnotCoeff 2 3 k =
      iteratedDeriv (2 * k + 1) (fun s : ℂ => Complex.sin (2 * s) / (2 * Complex.cos (3 * s))) 0 :=
  fishburnEulerCoeff_eq_trig k

/-- `ConvergentPowerSeries` is literally the ring `ℂ{x}` of Taylor series of holomorphic germs
at `0` (`AnalyticAt ℂ g 0`), so `FractionRing ConvergentPowerSeries` is `ℂ({x})`. -/
example (f : PowerSeries ℂ) :
    IsConvergentPS f ↔
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧ ∀ n : ℕ, PowerSeries.coeff n f = iteratedDeriv n g 0 / (n.factorial : ℂ) :=
  isConvergentPS_iff_exists_analyticAt f

/-! ### Flagship unconditional theorems over `ℂ(x)` -/

/-- **Zagier (2001, Theorem 3)** formalized unconditionally from scratch in `ℂ[[t]]`:
`P(1 - e^{-24t}) = e^t · ∑_{k ≥ 0} (T_k / k!) t^k`. -/
theorem zagier_2001_thm3 :
    fishburnSeries.subst zagierSubst = PowerSeries.exp ℂ * fishburnEulerSeries :=
  zagier_formal_identity

/-- **Bostan–Di Vizio–Raschel (AJM 2024, §2.2.6) Open Question over `ℂ(x)`**:
The literal divergent Fishburn ordinary generating function
`P(x) = ∑_{m ≥ 0} ∏_{j=1}^m (1 - (1 - x)^j) ∈ ℂ[[x]]`
is unconditionally differentially transcendental over `ℂ(x)`. -/
theorem fishburn_ogf_dTrans_over_ratFunc :
    AlgebraicIndependent ℂ (seriesCoordinates fishburnSeries) :=
  fishburnSeries_algebraicIndependent

/-- Glaisher's `T`-number EGF `∑_{k ≥ 0} (T_k / k!) t^k` is unconditionally
differentially transcendental over `ℂ(t)`. -/
theorem glaisher_T_egf_dTrans_over_ratFunc :
    AlgebraicIndependent ℂ (seriesCoordinates fishburnEulerSeries) :=
  fishburnEulerSeries_algebraicIndependent

/-- For all integers `p, q ≥ 2`, the torus-knot kernel Euler series
`∑_{k ≥ 0} (T_k^{(p,q)} / k!) t^k` (where `T_k^{(p,q)}` is the `(2k+1)`-st derivative of
`sin(p s) sin(q s) / sin(p q s)` at `0`) is unconditionally differentially transcendental over `ℂ(t)`. -/
theorem torusKnot_kernel_euler_dTrans_over_ratFunc {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    AlgebraicIndependent ℂ (seriesCoordinates (torusKnotEulerSeries p q)) :=
  torusKnotEulerSeries_algebraicIndependent hp hq

/-- For all integers `p, q ≥ 2`, the alternating torus-knot kernel series
`∑_{k ≥ 0} ((-1)^k T_k^{(p,q)} / k!) t^k` is unconditionally differentially transcendental over `ℂ(t)`. -/
theorem torusKnot_kernel_alternating_dTrans_over_ratFunc {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    AlgebraicIndependent ℂ (seriesCoordinates (torusKnotPerturbativeSeries p q)) :=
  torusKnotPerturbativeSeries_algebraicIndependent hp hq

/-! ### Flagship unconditional STRONG D-transcendence theorems over `ℂ({x})` (meromorphic germs at `0`) -/

/-- **Bostan–Di Vizio–Raschel (AJM 2024, Theorem 3 & §2.2.6; Klazar 2003) — Strong Form over `ℂ({x})`**:
The literal divergent Fishburn OGF `P(x) = ∑_{m ≥ 0} ∏_{j=1}^m (1 - (1 - x)^j)` is
unconditionally **strongly** differentially transcendental over the field `ℂ({x})` of
convergent meromorphic germs at `0`. -/
theorem fishburn_ogf_stronglyDTrans_over_meromorphicGerms :
    StronglyDTransOverMeromorphicGerms fishburnSeries :=
  fishburnSeries_stronglyDTrans

/-- Glaisher's `T`-number EGF `∑_{k ≥ 0} (T_k / k!) t^k` is unconditionally **strongly**
differentially transcendental over `ℂ({t})`. -/
theorem glaisher_T_egf_stronglyDTrans_over_meromorphicGerms :
    StronglyDTransOverMeromorphicGerms fishburnEulerSeries :=
  fishburnEulerSeries_stronglyDTrans

/-- For all integers `p, q ≥ 2`, the torus-knot kernel Euler series is unconditionally
**strongly** differentially transcendental over `ℂ({t})`. -/
theorem torusKnot_kernel_euler_stronglyDTrans_over_meromorphicGerms {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    StronglyDTransOverMeromorphicGerms (torusKnotEulerSeries p q) :=
  torusKnotEulerSeries_stronglyDTrans hp hq

/-- For all integers `p, q ≥ 2`, the alternating torus-knot kernel series is unconditionally
**strongly** differentially transcendental over `ℂ({t})`. -/
theorem torusKnot_kernel_alternating_stronglyDTrans_over_meromorphicGerms {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    StronglyDTransOverMeromorphicGerms (torusKnotPerturbativeSeries p q) :=
  torusKnotPerturbativeSeries_stronglyDTrans hp hq

end Statements.FishburnTorusKnots

end
