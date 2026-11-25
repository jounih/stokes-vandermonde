# Scope Note: Sibuya's Sub-Gevrey Convergence Theorem & Volterra Virial Functions (`μ`, `ν`)

**Audit ledger:** [`Statements/VolterraVirial.lean`](../Statements/VolterraVirial.lean)  
**Full proof:** [`PakPrimes/VolterraVirialDTrans.lean`](../PakPrimes/VolterraVirialDTrans.lean) (`8,362` lines)

## What Is Formalized (100% Unconditional, Mathlib-Only Dependencies)
- **Sibuya's Sub-Gevrey Convergence Theorem:** Any formal power series `f ∈ ℂ[[x]]` of sub-Gevrey growth (`|a_n| ≤ C^n (n!)^{ε}` for every `ε > 0`, or equivalently `o(n!)` faster than every Gevrey order `s > 0`) that satisfies a nonzero algebraic differential equation over `ℂ[x]` (in `d/dx` or Euler `x d/dx`) necessarily has positive radius of convergence (`IsConvergentPS f`).
- **Unconditional D-transcendence over `ℂ(t)`** of Volterra's functions `μ(t, β, α)` (for all `Re β > -1`, `α ∈ ℂ`) and `ν(t) = ∫_0^∞ t^u / Γ(u + 1) du` (governing the 2D interacting Fermi-gas second virial shift) and the 1D 3-body third virial shift, both in dimensionless variable `t > 0` and in physical temperature `T > 0` (`t = E_B / T`).
- **Exact Laplace transform:** `∫_0^∞ e^{-s t} ν(t) dt = (s log s)^{-1}` for all `s > 1`.

## What Is NOT Formalized Here
- Strong D-transcendence over `ℂ({t})` for `ν(t)` is not asserted in this ledger; all ADE exclusions here are over `ℂ(t)` (equivalently `ℂ[t]`).
- Multi-body virial coefficients `b_n` for `n ≥ 4` are not treated.
