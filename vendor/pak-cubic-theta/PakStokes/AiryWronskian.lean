module

public import PakStokes.PhysicalAiry
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Tactic.FieldSimp

/-! An identification test for the Airy contour and the Kummer integral.
The bounded and recessive solutions can be compared on one fixed ray. -/
public section
namespace CubicTheta.Physical
open Complex Filter Set
open scoped Topology
noncomputable section

theorem recessive_eq_of_wronskian (q f f' g g' : ℝ → ℂ)
    (df : ∀ x > 0, HasDerivAt f (f' x) x) (ddf : ∀ x > 0, HasDerivAt f' (q x*f x) x)
    (dg : ∀ x > 0, HasDerivAt g (g' x) x) (ddg : ∀ x > 0, HasDerivAt g' (q x*g x) x)
    (bf : IsBoundedUnder (· ≤ ·) atTop (norm ∘ f)) (bf' : IsBoundedUnder (· ≤ ·) atTop (norm ∘ f'))
    (dec : Tendsto g atTop (𝓝 0)) (dec' : Tendsto g' atTop (𝓝 0)) (nz : ∀ x > 0, g x ≠ 0)
    {v : ℂ} (hv : v ≠ 0) (f0 : Tendsto f (𝓝[>] 0) (𝓝 v)) (g0 : Tendsto g (𝓝[>] 0) (𝓝 v)) :
    ∀ x > 0, f x = g x := by
  let W (x : ℝ) := f x*g' x - f' x*g x
  have dw (x : ℝ) (hx : 0 < x) : HasDerivAt W 0 x := by
    convert! (((df x hx).mul (ddg x hx)).sub ((ddf x hx).mul (dg x hx))) using 1; ring
  have constant {H : ℝ → ℂ} (h : ∀ x > 0, HasDerivAt H 0 x) {x y : ℝ}
      (hx : 0<x) (hy : 0<y) : H x = H y := by
    exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      (fun t ht ↦ (h t ht).differentiableAt.differentiableWithinAt)
      (fun t ht ↦ (h t ht).deriv) hx hy
  have wzero (x : ℝ) (hx : 0<x) : W x = 0 := by
    have htop : Tendsto W atTop (𝓝 0) := by
      simpa [W] using (isBoundedUnder_le_mul_tendsto_zero bf dec').sub
        (isBoundedUnder_le_mul_tendsto_zero bf' dec)
    apply tendsto_nhds_unique _ htop
    exact tendsto_const_nhds.congr' ((eventually_gt_atTop (0:ℝ)).mono fun y hy ↦ constant dw hx hy)
  have ratio (x : ℝ) (hx : 0<x) : HasDerivAt (fun t ↦ f t/g t) 0 x := by
    convert! (df x hx).div (dg x hx) (nz x hx) using 1
    have eqn := sub_eq_zero.mp (wzero x hx)
    simp [eqn.symm]
  have hlim := f0.div g0 hv
  rw [div_self hv] at hlim
  intro x hx
  have h : f x/g x = 1 := tendsto_nhds_unique (f := fun y ↦ f y/g y)
    (tendsto_const_nhds.congr' (eventually_of_mem self_mem_nhdsWithin fun y hy ↦ constant ratio hx hy)) hlim
  exact (div_eq_one_iff_eq (nz x hx)).mp h

/-- Clearing the denominators in the Kummer integration-by-parts identity.
Write s=v+2z and w=e^(-v)v^(-1/6)s^(-1/6). The left side is the kernel
of 3z T''+(1-6z)T'-T divided by w, and the right side is (v w/s)'/w. -/
theorem kummer_ibp_identity (v z : ℂ) (hn : v+2*z ≠ 0) :
    7*z/(3*(v+2*z)^2) - (1-6*z)/(3*(v+2*z))-1 =
      2*z/(v+2*z)^2-v/(v+2*z)-1/(6*(v+2*z))-v/(6*(v+2*z)^2) := by
  generalize eq : v+2*z = s at hn ⊢
  field_simp [hn]; rw [← eq]; ring

end
end CubicTheta.Physical
