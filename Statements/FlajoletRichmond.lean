module

public import PakPrimes.FlajoletRichmondDTrans

/-!
# Statements Audit Ledger: Flajolet–Richmond Generalized Digital Trees (BDR §2.2.6, Example #3)

Thin statement ledger re-stating the unconditional theorems from `PakPrimes.FlajoletRichmondDTrans`
for the Flajolet–Richmond (1992) generalized digital tree exponential generating function
`f_b(t) = ∑_{n ≥ 0} f_{b,n} t^n / n!` solving
`f_b^{(b)}(t) = 2 e^{t/2} f_b(t/2) + e^t`, `f_{b,0} = 0`, `f_{b,1} = … = f_{b,b} = 1`:

1. **Exact `b = 1` collapse** (`f_1(t) = t e^t`, `G_1(t) = t`), supplying the missing `b ≥ 2`
   hypothesis on p. 12 of Bostan, Di Vizio, and Raschel (*Amer. J. Math.* 146(6), 2024, §2.2.6);
2. **Unconditional differential transcendence over `ℂ(t)` for every integer `b ≥ 2`** of both
   the exponential generating function `f_b(t)` (`frEGFSeries b`) and its Poisson transform
   `h_b(t) = e^{-t} f_b(t)` (`frPoissonSeries b`), both as formal power series over `RatFunc ℂ`
   and as analytic functions on `(0, ∞)`.

Note on scope: Bostan, Di Vizio, and Raschel had already proved differential transcendence of
the inverse Borel transform `G_b = B^{-1}(e^{-t} f_b)` via their Theorem 2 (`q = 1/2`) and
left open the D-algebraic nature of `f_b`. This ledger certifies `f_b` and `h_b = e^{-t} f_b`
over `ℂ(t)`; strong differential transcendence over `ℂ({t})` remains open.

See `docs/flajolet-richmond.md` for explicit scope notes.
-/

public section

namespace Statements.FlajoletRichmond

open PowerSeries PakPrimes.PrimeNome PakPrimes.FlajoletRichmondDTrans

/-- Exact differential-delay equation satisfied by `frEGF b` for all `b ≥ 1`. -/
theorem frEGF_diff_eq (b : ℕ) (hb : 1 ≤ b) (t : ℂ) :
    iteratedDeriv b (frEGF b) t = 2 * Complex.exp (t / 2) * frEGF b (t / 2) + Complex.exp t :=
  PakPrimes.FlajoletRichmondDTrans.frEGF_diff_eq b hb t

/-- Exact combinatorial initial conditions `f_0 = 0`, `f_1 = … = f_b = 1`. -/
theorem frEGF_init (b : ℕ) (hb : 1 ≤ b) :
    frCoeff b 0 = 0 ∧ ∀ k : ℕ, 1 ≤ k → k ≤ b → frCoeff b k = 1 :=
  PakPrimes.FlajoletRichmondDTrans.frEGF_init b hb

/-- Exact `b = 1` edge-case collapse: `f_1(t) = t e^t` is D-finite and NOT D-transcendental. -/
theorem frEGF_one (t : ℂ) : frEGF 1 t = t * Complex.exp t :=
  PakPrimes.FlajoletRichmondDTrans.frEGF_one t

/-- Exact `b = 1` non-D-transcendence over `RatFunc ℂ`. -/
theorem frEGF_one_not_dTrans : ¬DTransOverRatFunc (frEGFSeries 1) :=
  PakPrimes.FlajoletRichmondDTrans.frEGF_one_not_dTrans

/-- Strict positivity of the leading order-`b` elliptic pole coefficient `K_b` for all `b ≥ 2`. -/
theorem K_b_pos (b : ℕ) (hb : 2 ≤ b) : 0 < K_b b :=
  PakPrimes.FlajoletRichmondDTrans.K_b_pos b hb

/-- Unconditional D-transcendence over `ℂ(t)` of the Flajolet–Richmond EGF `f_b` for all `b ≥ 2`
(formal power series form over `RatFunc ℂ`). -/
theorem frEGFSeries_dTrans_over_ratFunc (b : ℕ) (hb : 2 ≤ b) :
    DTransOverRatFunc (frEGFSeries b) :=
  PakPrimes.FlajoletRichmondDTrans.frEGFSeries_dTrans_over_ratFunc b hb

/-- Equivalent algebraic independence of `(t, f_b, f_b', f_b'', …)` over `ℂ` for all `b ≥ 2`. -/
theorem frEGFSeries_algebraicIndependent (b : ℕ) (hb : 2 ≤ b) :
    AlgebraicIndependent ℂ (seriesCoordinates (frEGFSeries b)) :=
  PakPrimes.FlajoletRichmondDTrans.frEGFSeries_algebraicIndependent b hb

/-- Unconditional D-transcendence over `ℂ(t)` of the Poisson transform `h_b(t) = e^{-t} f_b(t)`
for all `b ≥ 2`. -/
theorem frPoissonSeries_dTrans_over_ratFunc (b : ℕ) (hb : 2 ≤ b) :
    DTransOverRatFunc (frPoissonSeries b) :=
  PakPrimes.FlajoletRichmondDTrans.frPoissonSeries_dTrans_over_ratFunc b hb

/-- Analytic non-existence of any polynomial ADE for `frEGF b` on `(0, ∞)` for all `b ≥ 2`. -/
theorem frEGF_no_ade (b : ℕ) (hb : 2 ≤ b) {r : ℕ}
    (P : MvPolynomial (Fin (r + 1)) (Polynomial ℂ))
    (hP : ∀ x : ℝ, 0 < x →
      (MvPolynomial.eval fun j : Fin (r + 1) => iteratedDeriv j.val (fun t : ℝ => frEGF b ↑t) x)
        ((MvPolynomial.map (Polynomial.evalRingHom (x : ℂ))) P) = 0) :
    P = 0 :=
  PakPrimes.FlajoletRichmondDTrans.frEGF_no_ade b hb P hP

end Statements.FlajoletRichmond
