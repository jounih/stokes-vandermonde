module

public import PakPrimes.MockThetaAndHurwitz
public import PakPrimes.FalseThetaDichotomy

/-!
# Statements Audit Ledger: Mordell, Eichler, and Stieltjes Integrals over `ℂ(u)`

Thin statement ledger re-stating the flagship integral-transform theorems from
`PakPrimes.MockThetaAndHurwitz` and `PakPrimes.FalseThetaDichotomy` using the project's
definitions (`mockThetaFMordell`, `mockThetaOmegaMordell`, `eichlerIntegral jacobiThetaCoeff`,
`falseThetaSinhMordell`, `kontsevichFalseMordell`, `rogersFalseThetaStieltjes`,
`fiveMockFalseMordell` — defined in `PakPrimes/MockThetaAndHurwitz.lean` and
`PakPrimes/FalseThetaDichotomy.lean`).

**Explicit Scope Notice:** The theorems in this file prove differential transcendence
over `ℂ(u)` for the **Mordell integrals, split Eichler integrals, and Stieltjes transforms**
associated with Ramanujan's mock theta functions `f, ω`, Zagier's Hurwitz shadow, Rogers's
false theta function `Ψ`, and Kontsevich's strange function—**not** directly for the
`q`-series `f(q), ω(q), H(q), Ψ(q)` in `ℂ[[q]]`. Literal `q`-series theorems are staged
separately for `v3.1.0`.

See `docs/mordell-and-false-theta-integrals.md` for full scope details.
-/

public section

namespace Statements.MordellAndFalseThetaIntegrals

open PakPrimes.HigherOrderStokes PakPrimes.MockModularWeightOne
open PakPrimes.MockThetaAndHurwitz PakPrimes.FalseThetaDichotomy

/-- D-transcendence over `ℂ(u)` of the Mordell integral associated with Ramanujan's `f(q)`. -/
theorem mockThetaF_mordell_dTrans {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val mockThetaFMordell u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  mockThetaF_no_rat_ade P hP

/-- D-transcendence over `ℂ(u)` of the Mordell integral associated with Ramanujan's `ω(q)`. -/
theorem mockThetaOmega_mordell_dTrans {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val mockThetaOmegaMordell u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  mockThetaOmega_no_rat_ade P hP

/-- D-transcendence over `ℂ(u)` of the split Eichler integral for Zagier's Hurwitz theta shadow. -/
theorem hurwitz_eichler_shadow_dTrans {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (eichlerIntegral jacobiThetaCoeff) u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  hurwitzThetaShadow_no_rat_ade P hP

/-- D-transcendence over `ℂ(u)` of the sinh false-theta Mordell integral. -/
theorem falseThetaSinh_mordell_dTrans {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val falseThetaSinhMordell u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  falseThetaSinhMordell_no_rat_ade P hP

/-- D-transcendence over `ℂ(u)` of the Kontsevich false-theta Mordell integral. -/
theorem kontsevich_mordell_dTrans {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val kontsevichFalseMordell u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  kontsevichFalseMordell_no_rat_ade P hP

/-- D-transcendence over `ℂ(u)` of the Rogers false-theta Stieltjes transform. -/
theorem rogers_stieltjes_dTrans {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val rogersFalseThetaStieltjes u)
        (evalRatU P (u : ℂ)) = 0) : P = 0 :=
  rogersFalseThetaStieltjes_no_rat_ade P hP

/-- 5-tuple joint differential independence over `ℂ(u)` of the five mock/false Mordell integrals. -/
theorem five_mordell_joint_dIndep {r : ℕ}
    (P : MvPolynomial (Fin 5 × Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ u : ℝ in Filter.atTop,
      MvPolynomial.eval (fun ij : Fin 5 × Fin (r + 1) =>
        iteratedDeriv ij.2.val (fiveMockFalseMordell ij.1) u)
        (jointEvalRatU P (u : ℂ)) = 0) : P = 0 :=
  five_mock_false_mordell_joint_no_rat_ade P hP

/-- Algebraic Chazy order-3 ODE for `E₂` from Ramanujan's differential system `(E₂, E₄, E₆)`. -/
theorem chazy_ode_from_ramanujan {R : Type*} [CommRing R] [Algebra ℂ R]
    (D : Derivation ℂ R R) {E2 E4 E6 : R}
    (h2 : (12 : R) * D E2 = E2 ^ 2 - E4)
    (h4 : (3 : R) * D E4 = E2 * E4 - E6)
    (h6 : (2 : R) * D E6 = E2 * E6 - E4 ^ 2) :
    (2 : R) * D (D (D E2)) - 2 * E2 * D (D E2) + 3 * (D E2) ^ 2 = 0 :=
  ramanujan_chazy_ode D h2 h4 h6

end Statements.MordellAndFalseThetaIntegrals

end
