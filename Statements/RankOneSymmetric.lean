module

public import PakPrimes.RankOneSymmetricParity

/-!
# Statements Audit Ledger: Compact Rank-1 Symmetric Spaces (CROSS), ADE Spherical 3-Manifolds, & Unconditional All-CROSS Heat-Trace D-Transcendence

Thin statement ledger re-stating the unconditional theorems from `PakPrimes.RankOneSymmetricParity`:

1. **Bosonic Euler-Product Odd-Sphere / Odd-Dimension Uniqueness over `ℂ(q)`**
   (`cross_simplyConnected_dAlg_iff`, `cross_all_dAlg_iff`): across the Cartan CROSS multiplicity
   quasipolynomials (`Sˢ`, `ℝℙˢ`, `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`), the formal conformal bosonic Euler product
   is D-algebraic over `ℂ(q)` if and only if `dim_ℝ M` is odd (and among simply connected CROSS,
   uniquely for odd spheres `S^{2r+1}`);
2. **Unconditional Strong `ℂ({t})` Wave-EGF D-Transcendence** across all four even-dimensional
   simply connected CROSS families (`S^{2r}`, `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`);
3. **ADE Spherical 3-Manifold (`S³ / I*`, `S³ / O*`, `S³ / T*`, `S³ / D_m*`) Molien Reciprocity &
   Even Parity**: exact formal `PowerSeries ℂ` Molien identities together with identical vanishing
   of `oddPart` and odd-parity Borel Stokes amplitudes `borelAmp`;
4. **Unconditional `ℂ(t)`-D-Transcendence of All Even-Dimensional Simply Connected CROSS Heat
   Traces** (`baseHeatInt_no_rat_ade`, `baseHeatHalf_no_rat_ade`, `evenCROSS_heatTrace_no_rat_ade`,
   and the family corollaries for `S^{2d}`, `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`): proved over `ℂ(t)` as `t → 0+`
   via constant-coefficient differential-operator reduction `P(-∂_t)` to `baseHeatInt` and
   `baseHeatHalf` (distinct from the `ℂ(q)` bosonic Euler-product classification in Item 1).

**Scope note:** The Cartan CROSS multiplicity quasipolynomials (`conformalScalarSphereQP`, `rpsQP`,
`cpnQP`, `hpnQP`, `op2QP`), ADE Molien series, and shifted spectral heat sums (`evenCROSSHeatTrace`,
`evenSphereHeatTrace`, `cpnHeatTrace`, `hpnHeatTrace`, `op2HeatTrace`) are defined directly from
the standard closed-form spectral-multiplicity formulas (not derived from Riemannian manifolds or
`L²(M)` harmonic analysis inside Lean). See `docs/geometry-and-unconditional-primes.md` for full
scope details.
-/

public section

namespace Statements.RankOneSymmetric

open PakPrimes.PrimeNome PakPrimes.DivisorAndMacMahon PakPrimes.QuasipolynomialEulerParity
open PakPrimes.HigherOrderStokes PakPrimes.PakYeliussizovEGF PakPrimes.FishburnStrongDTrans
open PakPrimes.RankOneSymmetricParity
open scoped Topology

/-! ### 1. Complete Cartan CROSS Bosonic Euler-Product Classification -/

/-- Across all simply connected compact rank-1 symmetric spaces (`Sˢ`, `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`),
the conformal bosonic Euler product is D-algebraic over `ℂ(q)` iff `M` is an odd sphere `S^{2r+1}`. -/
theorem cross_simplyConnected_dAlg_iff (M : SimplyConnectedCROSS) :
    ¬ AlgebraicIndependent ℂ
        (seriesCoordinates (eulerProduct (fun s => M.qp.eval (s : ℤ)))) ↔
      M.isOddSphere :=
  PakPrimes.RankOneSymmetricParity.cross_simplyConnected_dAlg_iff M

/-- Across ALL compact rank-1 symmetric spaces (`Sˢ`, `ℝℙˢ`, `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`),
the conformal bosonic Euler product is D-algebraic over `ℂ(q)` iff `dim_ℝ M` is odd. -/
theorem cross_all_dAlg_iff (M : CompactRankOneSymmetric) :
    ¬ AlgebraicIndependent ℂ
        (seriesCoordinates (eulerProduct (fun s => M.qp.eval (s : ℤ)))) ↔
      Odd M.realDim :=
  PakPrimes.RankOneSymmetricParity.cross_all_dAlg_iff M

/-! ### 2. Unconditional Strong `ℂ({t})` Wave-EGF D-Transcendence Across All Four Families -/

/-- Unconditional strong `ℂ({t})` D-transcendence of the regularized wave EGF OGF on `S^{2r}` (`r ≥ 1`). -/
theorem evenSphere_waveEGF_ogf_stronglyDTrans (r : ℕ) (hr : 1 ≤ r) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (evenSphereWaveEGFReg r)) :=
  PakPrimes.RankOneSymmetricParity.evenSphere_waveEGF_ogf_stronglyDTrans r hr

/-- Unconditional strong `ℂ({t})` D-transcendence of the regularized wave EGF OGF on `ℂℙⁿ` (`n ≥ 1`). -/
theorem cpn_waveEGF_ogf_stronglyDTrans (n : ℕ) (hn : 1 ≤ n) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (cpnWaveEGFReg n)) :=
  PakPrimes.RankOneSymmetricParity.cpn_waveEGF_ogf_stronglyDTrans n hn

/-- Unconditional strong `ℂ({t})` D-transcendence of the regularized wave EGF OGF on `ℍℙⁿ` (`n ≥ 1`). -/
theorem hpn_waveEGF_ogf_stronglyDTrans (n : ℕ) (hn : 1 ≤ n) :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF (hpnWaveEGFReg n)) :=
  PakPrimes.RankOneSymmetricParity.hpn_waveEGF_ogf_stronglyDTrans n hn

/-- Unconditional strong `ℂ({t})` D-transcendence of the regularized wave EGF OGF on `𝕆ℙ²`. -/
theorem op2_waveEGF_ogf_stronglyDTrans :
    StronglyDTransOverMeromorphicGerms (ogfOfEGF op2WaveEGFReg) :=
  PakPrimes.RankOneSymmetricParity.op2_waveEGF_ogf_stronglyDTrans

/-! ### 3. ADE Spherical 3-Manifolds (`S³ / I*`, `O*`, `T*`, `D_m*`): Molien Reciprocity & Even Parity -/

/-- Universal vanishing of `oddPart` for any palindromic ADE spherical 3-manifold quasipolynomial. -/
theorem adeSphere3QP_oddPart_eq_zero {M : ℕ} (hM : 0 < M) {A : Polynomial ℂ}
    (hpal : IsPalindromic (2 * M - 2) A) (u : ℤ) :
    (adeSphere3QP M hM A).oddPart u = 0 :=
  PakPrimes.RankOneSymmetricParity.adeSphere3QP_oddPart_eq_zero hM hpal u

/-- Universal vanishing of all odd-parity Borel Stokes amplitudes for any palindromic ADE
spherical 3-manifold quasipolynomial. -/
theorem adeSphere3QP_borelAmp_eq_zero {M : ℕ} (hM : 0 < M) {A : Polynomial ℂ}
    (hpal : IsPalindromic (2 * M - 2) A) (d : Fin 3) (m : ℕ) :
    (adeSphere3QP M hM A).borelAmp d m = 0 :=
  PakPrimes.RankOneSymmetricParity.adeSphere3QP_borelAmp_eq_zero hM hpal d m

/-- Exact formal Molien power-series identity for the Poincaré homology sphere `S³ / I*`. -/
theorem poincareSphere_molien_identity :
    (1 - PowerSeries.X ^ 12 : PowerSeries ℂ) * (1 - PowerSeries.X ^ 20 : PowerSeries ℂ) *
        adeMolienSeries 60 poincareMolienNum =
      1 + PowerSeries.X ^ 30 :=
  PakPrimes.RankOneSymmetricParity.poincareSphere_molien_identity

/-- Identical vanishing of `oddPart` on the Poincaré homology sphere `S³ / I*`. -/
theorem poincareSphereQP_oddPart_eq_zero (m : ℤ) :
    poincareSphereQP.oddPart m = 0 :=
  PakPrimes.RankOneSymmetricParity.poincareSphereQP_oddPart_eq_zero m

/-- Identical vanishing of all odd-parity Borel Stokes amplitudes on `S³ / I*`. -/
theorem poincareSphereQP_borelAmp_eq_zero (d : Fin 3) (m : ℕ) :
    poincareSphereQP.borelAmp d m = 0 :=
  PakPrimes.RankOneSymmetricParity.poincareSphereQP_borelAmp_eq_zero d m

/-- Exact formal Molien power-series identity for the octahedral spherical 3-manifold `S³ / O*`. -/
theorem octahedralSphere_molien_identity :
    (1 - PowerSeries.X ^ 8 : PowerSeries ℂ) * (1 - PowerSeries.X ^ 12 : PowerSeries ℂ) *
        adeMolienSeries 24 octahedralMolienNum =
      1 + PowerSeries.X ^ 18 :=
  PakPrimes.RankOneSymmetricParity.octahedralSphere_molien_identity

/-- Identical vanishing of `oddPart` on the octahedral spherical 3-manifold `S³ / O*`. -/
theorem octahedralSphereQP_oddPart_eq_zero (m : ℤ) :
    octahedralSphereQP.oddPart m = 0 :=
  PakPrimes.RankOneSymmetricParity.octahedralSphereQP_oddPart_eq_zero m

/-- Exact formal Molien power-series identity for the tetrahedral spherical 3-manifold `S³ / T*`. -/
theorem tetrahedralSphere_molien_identity :
    (1 - PowerSeries.X ^ 6 : PowerSeries ℂ) * (1 - PowerSeries.X ^ 8 : PowerSeries ℂ) *
        adeMolienSeries 12 tetrahedralMolienNum =
      1 + PowerSeries.X ^ 12 :=
  PakPrimes.RankOneSymmetricParity.tetrahedralSphere_molien_identity

/-- Identical vanishing of `oddPart` on the tetrahedral spherical 3-manifold `S³ / T*`. -/
theorem tetrahedralSphereQP_oddPart_eq_zero (m : ℤ) :
    tetrahedralSphereQP.oddPart m = 0 :=
  PakPrimes.RankOneSymmetricParity.tetrahedralSphereQP_oddPart_eq_zero m

/-- Exact formal Molien power-series identity for the binary dihedral prism manifold `S³ / D_m*` (`m ≥ 2`). -/
theorem binaryDihedralSphere_molien_identity {m : ℕ} (hm : 2 ≤ m) :
    (1 - PowerSeries.X ^ 4 : PowerSeries ℂ) * (1 - PowerSeries.X ^ (2 * m) : PowerSeries ℂ) *
        adeMolienSeries (4 * m) (binaryDihedralMolienNum m) =
      1 + PowerSeries.X ^ (2 * m + 2) :=
  PakPrimes.RankOneSymmetricParity.binaryDihedralSphere_molien_identity hm

/-- Identical vanishing of `oddPart` on the binary dihedral prism manifold `S³ / D_m*` (`m ≥ 2`). -/
theorem binaryDihedralSphereQP_oddPart_eq_zero {m : ℕ} (hm : 2 ≤ m) (u : ℤ) :
    (binaryDihedralSphereQP m hm).oddPart u = 0 :=
  PakPrimes.RankOneSymmetricParity.binaryDihedralSphereQP_oddPart_eq_zero hm u

/-! ### 4. Unconditional All-CROSS Heat-Trace D-Transcendence over `ℂ(t)` -/

/-- Unconditional `ℂ(t)`-D-transcendence of `baseHeatInt(t) = ∑_{n ≥ 1} n e^{-t n²}` as `t → 0+`. -/
theorem baseHeatInt_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val baseHeatInt t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  PakPrimes.RankOneSymmetricParity.baseHeatInt_no_rat_ade P hP

/-- Unconditional `ℂ(t)`-D-transcendence of `baseHeatHalf(t) = ∑_{k ≥ 0} (k + 1/2) e^{-t (k + 1/2)²}`
as `t → 0+`. -/
theorem baseHeatHalf_no_rat_ade {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val baseHeatHalf t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  PakPrimes.RankOneSymmetricParity.baseHeatHalf_no_rat_ade P hP

/-- Master unconditional `ℂ(t)`-D-transcendence of the shifted spectral heat trace for EVERY
even-dimensional simply connected compact rank-1 symmetric space (`S^{2r}`, `ℂℙⁿ`, `ℍℙⁿ`, `𝕆ℙ²`). -/
theorem evenCROSS_heatTrace_no_rat_ade (M : SimplyConnectedCROSS) (hEven : Even M.realDim)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (evenCROSSHeatTrace M) t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  PakPrimes.RankOneSymmetricParity.evenCROSS_heatTrace_no_rat_ade M hEven P hP

/-- Unconditional `ℂ(t)`-D-transcendence of the shifted spectral heat trace on every even sphere `S^{2d}` (`d ≥ 1`). -/
theorem evenSphere_heatTrace_no_rat_ade {d : ℕ} (hd : 1 ≤ d)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (evenSphereHeatTrace d) t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  PakPrimes.RankOneSymmetricParity.evenSphere_heatTrace_no_rat_ade hd P hP

/-- Unconditional `ℂ(t)`-D-transcendence of the shifted spectral heat trace on every `ℂℙⁿ` (`n ≥ 1`). -/
theorem cpn_heatTrace_no_rat_ade {n : ℕ} (hn : 1 ≤ n)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (cpnHeatTrace n) t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  PakPrimes.RankOneSymmetricParity.cpn_heatTrace_no_rat_ade hn P hP

/-- Unconditional `ℂ(t)`-D-transcendence of the shifted spectral heat trace on every `ℍℙⁿ` (`n ≥ 1`). -/
theorem hpn_heatTrace_no_rat_ade {n : ℕ} (hn : 1 ≤ n)
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val (hpnHeatTrace n) t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  PakPrimes.RankOneSymmetricParity.hpn_heatTrace_no_rat_ade hn P hP

/-- Unconditional `ℂ(t)`-D-transcendence of the shifted spectral heat trace on `𝕆ℙ²`. -/
theorem op2_heatTrace_no_rat_ade
    {r : ℕ} (P : MvPolynomial (Fin (r + 1)) (RatFunc ℂ))
    (hP : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      MvPolynomial.eval (fun j : Fin (r + 1) => iteratedDeriv j.val op2HeatTrace t)
        (evalRatU P (t : ℂ)) = 0) : P = 0 :=
  PakPrimes.RankOneSymmetricParity.op2_heatTrace_no_rat_ade P hP

end Statements.RankOneSymmetric
