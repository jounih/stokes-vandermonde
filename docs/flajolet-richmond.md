# Scope Note: Flajolet–Richmond Generalized Digital Trees (BDR §2.2.6, Example #3)

**Audit ledger:** [`Statements/FlajoletRichmond.lean`](../Statements/FlajoletRichmond.lean)  
**Full proof:** [`PakPrimes/FlajoletRichmondDTrans.lean`](../PakPrimes/FlajoletRichmondDTrans.lean) (`12,366` lines)

## What Is Formalized (100% Unconditional, Zero Unproved Hypotheses)
- Exact combinatorial recurrence, entire exponential generating function `f_b(t) = ∑ f_{b,n} t^n / n!`, Poisson transform `h_b(t) = e^{-t} f_b(t)`, and verification of `f_b^{(b)}(t) = 2 e^{t/2} f_b(t/2) + e^t` with `f_{b,0} = 0`, `f_{b,1} = … = f_{b,b} = 1` for all integers `b ≥ 1`.
- **Exact `b = 1` edge-case correction:** `f_1(t) = t e^t`, `h_1(t) = t`, `G_1(t) = t`, proved D-algebraic and NOT D-transcendental over `ℂ(t)` (supplying the missing `b ≥ 2` hypothesis on p. 12 of Bostan–Di Vizio–Raschel, *Amer. J. Math.* 146(6), 2024).
- **Unconditional D-transcendence over `ℂ(t)` for every integer `b ≥ 2`** of both `f_b(t)` and `h_b(t) = e^{-t} f_b(t)`, proved via exact telescoping, strict positivity `K_b > 2 / (3 P_∞^b) > 0`, a single-rectangle Cauchy residue integral + Gamma reflection, finite-trapezoid Hankel asymptotics, and shift-and-scale descent on `∑_{m ∈ ℤ} 2^m e^{-2^m x}`.

## What Is NOT Formalized Here
- **Inverse Borel transform `G_b = B^{-1}(e^{-t} f_b)`:** Already proved D-transcendental over `ℂ(t)` by Bostan, Di Vizio, and Raschel (2024, §2.2.6) via their Theorem 2 (`q = 1/2`), subject to `b ≥ 2`. Our certificate closes the open `f_b` half.
- **Strong differential transcendence over `ℂ({t})`:** Remains open; the Hankel asymptotic reduction evaluates along `x = 2^N x_0 → +∞`, outside the convergence disk of a germ in `ℂ{t}`.
- **Schmid's equation (BDR §2.2.6, Example #2):** Not formalized in this module; full D-transcendence of Schmid's equation remains open.
