# The Stokes–Vandermonde criterion and prime-counting series

This Lean 4 development proves that each of two ordinary generating functions satisfies no nonzero algebraic differential equation over $\mathbb C(q)$. They are the prime-indicator series $\sum_{p\ \mathrm{prime}}q^p$ and the prime-counting series $\sum_{n\ge0}\pi(n)q^n$. Their differential transcendence is equivalent because multiplication by $1-q$ takes the second series to the first. This settles the prime-counting part of Conjecture 2.5 in Igor Pak’s survey. The part about the generating function of the $n$th prime remains open here. [Pak’s survey](https://arxiv.org/abs/1803.06636)

## The prime theorem

The theorem below is in namespace `PakPrimes.Main`. Its statement takes no hypotheses.

```lean
theorem primeCounting_and_indicator_independent :
    AlgebraicIndependent ℂ PrimeNome.indicatorCoordinates ∧
      AlgebraicIndependent ℂ PrimeNome.piCoordinates
```

For a power series $F$, `seriesCoordinates F` contains $q,F,F',F'',\dots$ in $\mathbb C[[q]]$. Algebraic independence over $\mathbb C$ rules out every algebraic differential equation over $\mathbb C(q)$ after clearing denominators. The conjunction makes a separate independence assertion for each series. [Definitions](PakPrimes/AutonomousTransfer.lean) · [Theorem](PNTIntegration/Final.lean)

The version 1.0.1 manuscript gives the analytic argument and records the formalization as it stood at that release. The Lean prime theorem then took `PNTAllOrders` as a hypothesis. This is the estimate $\pi(x)-\int_2^x dt/\log t=O_M(x/(\log x)^M)$ for every natural $M$. The original manuscript and source remain available in that archive. [Manuscript](paper/main.pdf) · [Version 1.0.1](https://doi.org/10.5281/zenodo.24500832)

Version 1.1.0 proves `PNTAllOrders` inside Lean. The PNT+ theorem `MediumPNT` bounds the error for Chebyshev’s ψ by $O(x\exp(-c(\log x)^{1/10}))$ for some $c>0$. A bound for the prime-power contribution transfers the estimate to θ. Abel summation then transfers it to π. Splitting the integral at $\sqrt x$ gives the required bound for every $M$. The earlier theorem `pak_conjecture_2_5b_of_pnt` applies to this proved estimate. Another development proves a stretched-exponential remainder for π on Lean 4.28. [Transfer proof](PNTIntegration/PrimeCountingFromPsi.lean) · [PNT+ source and attribution](vendor/README.md) · [Erdős 768 proof](https://github.com/ericlisg/erdos768-lean/blob/e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9/RequestProject/PNT.lean#L321-L324)

## Other results in the development

- `borel_stokes_vandermonde_no_autonomous_ade` gives a criterion for ruling out autonomous algebraic differential equations for the formal Laplace series of a meromorphic Borel transform. The hypotheses on the wedge, poles, residues and exponential growth are explicit in `MeromorphicBorelData`. The chapter also instantiates the criterion for $\Gamma(1-\xi)$. [General criterion](PakPrimes/GeneralTheorem2.lean)
- `logReciprocal_algebraicIndependent` gives differential transcendence over $\mathbb C(q)$ for $\sum_{n\ge2}q^n/\log n$. [Main theorem file](PakPrimes/MainTheorem.lean)
- A separate companion repository contains the Lean proof for the cubic theta series in Conjecture 2.6. [Cubic theta release](https://doi.org/10.5281/zenodo.24492865)

## Reproduce the check

Use Lean 4.36.0. The Lake manifest pins Mathlib to `fc4f59e577feb1a4956671bc04ac18aaaf8cd842`. The source files for the two additional upstream libraries are included in the release.

```bash
lake exe cache get
lake build
lake env lean Verify.lean
lake env leanchecker --fresh PakPrimes
```

On macOS run the last command with a larger stack if necessary, using `(ulimit -s 65520 && lake env leanchecker --fresh PakPrimes)`. The expected axiom line is

```text
'PakPrimes.Main.primeCounting_and_indicator_independent' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Credits and license

Google Gemini, OpenAI Codex, and Anthropic Claude assisted with the mathematical investigation, auditing, drafting, and Lean formalization. The Lean development incorporates work from the PNT+ and LeanArchitect projects. Independent specialist review is welcome. [License](LICENSE) · [Third-party credits and licenses](vendor/README.md)
