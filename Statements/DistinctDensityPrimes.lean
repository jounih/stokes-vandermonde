module

public import PakPrimes.DistinctDensityPrimes

/-!
# Statements Audit Ledger: Joint Differential Independence of Distinct-Density Prime OGFs

Thin statement ledger re-stating the unconditional theorems from `PakPrimes.DistinctDensityPrimes`:

1. Joint algebraic independence over `ℂ` of all derivatives of shifted logarithmic branches
   `{I_+(u - log δ_i)}` for any finite family of distinct positive densities `δ_1, …, δ_d`;
2. Joint differential independence over `ℂ(x)` of any finite family of sequence OGFs
   `∑ a_i(n) x^n` obeying distinct-density prime-number asymptotics `HasDensityPNT (a i) (δ i)`;
3. Finite and countably infinite joint differential independence for the nested dyadic tower
   of densities `2^{-k}` (e.g., primes `p ≡ 1 mod 2^k` under quantitative Dirichlet PNT).

See `docs/distinct-density-and-strong-lift.md` for explicit scope notes.
-/

public section

namespace Statements.DistinctDensityPrimes

open PakPrimes.DistinctDensityPrimes

/-- Joint algebraic independence of all derivatives of distinct-density shifted branches. -/
theorem distinctDensity_branches_algebraicIndependent {d : ℕ} (δ : Fin d → ℝ)
    (hδ_pos : ∀ i, 0 < δ i) (hδ_inj : Function.Injective δ) :
    AlgebraicIndependent ℂ
      (fun p : Fin d × ℕ => fun u : ℝ => iteratedDeriv p.2 (J_plus δ p.1) u) :=
  PakPrimes.DistinctDensityPrimes.distinctDensity_branches_algebraicIndependent δ hδ_pos hδ_inj

/-- Joint differential independence of finitely many distinct-density prime-asymptotic OGFs. -/
theorem distinctDensity_ogf_joint_algebraicIndependent
    {d : ℕ} (a : Fin d → ℕ → ℕ) (δ : Fin d → ℝ)
    (hd : ∀ i, HasDensityPNT (a i) (δ i))
    (hinj : Function.Injective δ) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i => seqSeries (a i))) :=
  PakPrimes.DistinctDensityPrimes.distinctDensity_ogf_joint_algebraicIndependent a δ hd hinj

/-- Finite nested dyadic-density tower joint differential independence. -/
theorem distinctDensity_dyadic_finite
    {d : ℕ} (a : Fin d → ℕ → ℕ) (k : Fin d → ℕ)
    (hkinj : Function.Injective k)
    (hd : ∀ i, HasDensityPNT (a i) (dyadicDensity (k i))) :
    AlgebraicIndependent ℂ (jointSeriesCoordinates (fun i => seqSeries (a i))) :=
  PakPrimes.DistinctDensityPrimes.distinctDensity_dyadic_finite a k hkinj hd

/-- Countably infinite nested dyadic-density tower joint differential independence. -/
theorem distinctDensity_dyadic_countable
    (a : ℕ → ℕ → ℕ)
    (hd : ∀ k : ℕ, HasDensityPNT (a k) (dyadicDensity (k + 1))) :
    AlgebraicIndependent ℂ (countableSeriesCoordinates (fun k => seqSeries (a k))) :=
  PakPrimes.DistinctDensityPrimes.distinctDensity_dyadic_countable a hd

end Statements.DistinctDensityPrimes
