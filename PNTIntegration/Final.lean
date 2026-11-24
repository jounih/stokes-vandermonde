import PNTIntegration.PrimeCountingFromPsi
import PrimeNumberTheoremAnd.MediumPNT

namespace PakPrimes.Main

/-- The all-orders error estimate for π follows from PNT+'s medium-strength theorem for ψ. -/
theorem pntAllOrders : PNTAllOrders :=
  pntAllOrders_of_mediumPsi MediumPNT

/-- The generating series of the prime indicator and that of the prime-counting
function are differentially transcendental over ℂ(q). -/
theorem primeCounting_and_indicator_independent :
    AlgebraicIndependent ℂ PrimeNome.indicatorCoordinates ∧
      AlgebraicIndependent ℂ PrimeNome.piCoordinates :=
  pak_conjecture_2_5b_of_pnt pntAllOrders

end PakPrimes.Main
