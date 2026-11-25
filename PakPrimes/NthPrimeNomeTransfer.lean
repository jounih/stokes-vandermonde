module

public import PakPrimes.AutonomousTransfer

/-! # The differentiated nome readout for the nth-prime series

The frozen-parameter calculation starts with the derivative of the source
multiplied by the square of the exponential scale.  This module transfers any
formal differential dependence of a disk-convergent power series to a nonzero
autonomous equation for that precise readout.
-/

public section
noncomputable section
namespace PakPrimes.PrimeNome

open Filter MvPolynomial
open scoped Topology

/-- With `t = exp (-u)` and `q = exp (-t)`, this is `D_u(t² F(q)) - 1`. -/
@[expose] def nthPrimeRay (F : PowerSeries ℂ) (u : ℝ) : ℂ :=
  deriv (fun v => tRay v ^ 2 * value F (qRay v)) u - 1

theorem nthPrimeRay_analytic {F : PowerSeries ℂ} (hF : DiskCoeffBound F) (u : ℝ) :
    AnalyticAt ℝ (nthPrimeRay F) u := by
  have hval : AnalyticAt ℝ (fun v => value F (qRay v)) u := ray_source_analytic hF 1 u
  exact (((tRay_analytic u).pow 2).mul hval).deriv.sub analyticAt_const

/-- The input is the literal formal series.  The output is an autonomous
polynomial in the ordinary real-variable derivatives of the differentiated readout. -/
theorem nthPrime_autonomous_transfer_disk {F : PowerSeries ℂ} (hF : DiskCoeffBound F)
    (hdep : ¬ AlgebraicIndependent ℂ (seriesCoordinates F)) :
    ∃ (J : ℕ) (P : MvPolynomial (Fin J) ℂ), P ≠ 0 ∧
      ∀ᶠ u : ℝ in atTop,
        MvPolynomial.eval (fun i : Fin J => iteratedDeriv i.val (nthPrimeRay F) u) P = 0 := by
  refine autonomous_transfer_readout hF (nthPrimeRay_analytic hF) ?_ hdep
  unfold NomeReadout
  intro ι inst v x gt gs smooth closed
  have hprod : Generated v x (fun u => tRay u ^ 2 * value F (qRay u)) := (gt.pow 2).mul gs
  exact (hprod.deriv smooth closed).sub (Generated.const 1)

end PakPrimes.PrimeNome
end
