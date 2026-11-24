# Upstream sources

The `PrimeNumberTheoremAnd` directory contains the thirteen Lean modules imported by `MediumPNT` from the Prime Number Theorem and project. That theorem gives an error bound for Chebyshev’s ψ function. The source files retain their upstream headers. [Source revision a4fb6989](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/tree/a4fb6989b07e9c76b511807ae93e33e25b820e9b) · [Upstream license](LICENSE-PrimeNumberTheoremAnd)

Three files in this distribution include compatibility edits for Lean and Mathlib 4.36. Each has a notice in its first line. In `MediumPNT.lean` we use `self_mem_nhdsWithin` and supply a pointwise proof of interval inclusion. In `MellinCalculus.lean` we use the current measure-restriction monotonicity lemma. In `ZetaBounds.lean` we give the open-set proof with explicit continuous functions. The statement of `MediumPNT` is unchanged.

The `Architect` directory and `Architect.lean` contain the nine original LeanArchitect modules used for PNT+ blueprint annotations. The upstream tactic library includes a tactic to record unfinished blueprint entries. CI audits the mathematical sources for invocations and checks the axiom dependencies of the actual theorems. [Source revision c948bae1](https://github.com/hanwenzhu/LeanArchitect/tree/c948bae1767330bb4cf09071f47752a10311d7d2) · [Upstream license](LICENSE-LeanArchitect)
