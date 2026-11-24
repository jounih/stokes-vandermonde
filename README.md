# The Stokes–Vandermonde Criterion and Differential Transcendence of Prime-Counting Series

Lean 4 (`v4.36.0`, Mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`) formalization of a general meromorphic Borel–Laplace Stokes–Vandermonde criterion for differential transcendence, together with its applications to $\sum_{n \ge 2} q^n / \log n$ and the prime-counting half of Igor Pak’s ICM 2018 Conjecture 2.5.

*Companion to the Lean 4 formalization of the cubic theta series ([jounih/pak-cubic-theta](https://github.com/jounih/pak-cubic-theta), Zenodo [10.5281/zenodo.24492865](https://doi.org/10.5281/zenodo.24492865)).*

## What Lean Checks

Every theorem below is checked by the Lean 4 kernel and `lake env leanchecker --fresh PakPrimes` with zero `sorry`, zero custom `axiom`, and zero `native_decide` (axioms strictly `[propext, Classical.choice, Quot.sound]`).

| Theorem | Location | Hypotheses | What it proves |
| --- | --- | --- | --- |
| `borel_stokes_vandermonde_no_autonomous_ade` | [GeneralTheorem2.lean](PakPrimes/GeneralTheorem2.lean) | `MeromorphicBorelData φ ω res` | **The Stokes–Vandermonde Criterion:** for *any* Borel transform $\phi$ analytic on a punctured open wedge around $[0,\infty)$ with simple poles at $0 < \omega_0 < \omega_1 < \dots$, nonzero residues, and exponential type on two flanking rays $e^{\pm i\theta}$, its formal Laplace series $\sum_{k\ge 0}\phi^{(k)}(0)u^{-k-1}$ satisfies no nonzero autonomous polynomial ODE over $\mathbb{C}$. |
| `no_autonomous_ade_of_meromorphic_borel` | [GeneralTheorem2.lean](PakPrimes/GeneralTheorem2.lean) | `MeromorphicBorelData φ ω res` + all-orders asymptotic match | Any real function $f$ whose derivatives share the all-orders $1/u$ expansion of $\sum_{k\ge 0}\phi^{(k)}(0)u^{-k-1}$ satisfies no nonzero autonomous polynomial ODE over $\mathbb{C}$. |
| `gHat_no_autonomous_ade_via_general_theorem_2` | [GeneralTheorem2.lean](PakPrimes/GeneralTheorem2.lean) | None | Non-vacuity instantiation of the general criterion on $\phi(\xi) = \Gamma(1-\xi)$, $\omega_m = m+1$, $\mathrm{res}_m = (-1)^{m+1}/m!$. |
| `logReciprocal_algebraicIndependent` | [MainTheorem.lean](PakPrimes/MainTheorem.lean) | **None (unconditional)** | $\sum_{n \ge 2} q^n / \log n$ satisfies no nonzero algebraic differential equation over $\mathbb{C}(q)$ (`AlgebraicIndependent ℂ logReciprocalCoordinates` in $\mathbb{C}[[q]]$). |
| `pak_conjecture_2_5b_of_pnt` | [MainTheorem.lean](PakPrimes/MainTheorem.lean) | `PNTAllOrders` (classical PNT error term) | Both $\sum_{p\text{ prime}} q^p$ and $\sum_{n \ge 0} \pi(n) q^n$ satisfy no nonzero algebraic differential equation over $\mathbb{C}(q)$ — the prime-counting half of Pak’s Conjecture 2.5. *(The $n$-th prime half $\sum p_n q^n$ remains open.)* |

## Exact Definitions to Audit

Only the formal power-series definitions, coordinate tuple, and `PNTAllOrders` need to be trusted; every intermediate step (Borel convolution algebra `Minor`/`BorelExpr`, lateral Borel-sum equation transfer, triangle Cauchy–Goursat and residue calculus, Stokes jump expansion, Watson’s lemma, and the autonomous transfer from $\mathbb{C}(q)$ to $\mathbb{C}$) is proved inside Lean.

- **Power series ([AutonomousTransfer.lean](PakPrimes/AutonomousTransfer.lean)):**
  - `I_prime`: $\sum_{p\text{ prime}} q^p$ (`PowerSeries.mk fun n => if Nat.Prime n then 1 else 0`)
  - `Pi_series`: $\sum_{n \ge 0} \pi(n) q^n$ (`PowerSeries.mk fun n => (Nat.primeCounting n : ℂ)`)
  - `logReciprocalSeries`: $\sum_{n \ge 2} q^n / \log n$
  - `seriesCoordinates F`: $0 \mapsto q$, $j + 1 \mapsto (d/dq)^j F$ in $\mathbb{C}[[q]]$, so `AlgebraicIndependent ℂ (seriesCoordinates F)` means $F$ satisfies no nonzero algebraic differential equation over $\mathbb{C}(q)$.
- **Prime Number Theorem hypothesis ([MainTheorem.lean](PakPrimes/MainTheorem.lean)):**
  ```lean
  def li (x : ℝ) : ℝ := ∫ v in (2 : ℝ)..x, (Real.log v)⁻¹

  def PNTAllOrders : Prop :=
    ∀ M : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      |(Nat.primeCounting ⌊x⌋₊ : ℝ) - li x| ≤ C * x / (Real.log x) ^ M
  ```
  Discharging `PNTAllOrders` from the Kontorovich–Tao [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd) project immediately upgrades `pak_conjecture_2_5b_of_pnt` to an unconditional Lean theorem.

## Reproducing the Check

```bash
lake exe cache get
lake build
lake env lean Verify.lean
lake env leanchecker --fresh PakPrimes
```

*(On macOS, run `(ulimit -s 65520 && lake env leanchecker --fresh PakPrimes)` so `leanchecker` has sufficient stack headroom.)*

## AI Assistance & License

Google Gemini, OpenAI Codex, and Anthropic Claude provided substantial assistance with the mathematical investigation, adversarial auditing, manuscript drafting, and Lean 4 formalization. Licensed under [Apache-2.0](LICENSE).
