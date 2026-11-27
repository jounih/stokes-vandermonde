module

public import PakStokes.AllD.UniversalThimble
public import PakStokes.PhysicalParity
public import PakStokes.MarkedJacobian
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Finsupp.WellFounded
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import all PakStokes.AllD.UniversalThimble
import all PakStokes.RayAlgebra
import all PakStokes.PhysicalParity
import all PakStokes.MarkedJacobian
import all Laplace
import all DirectionalLaplace

/-! 1. Exact extreme-ray geometry of the active saddle cone for all `d ≥ 3`
and the extreme-ray prime-ideal algebra homomorphism `Π_E` on `AddMonoidAlgebra`.
2. `FiniteParities M` (generalizing `TwoParities` to arbitrary modulus `M ≥ 1`),
argument rescaling of `PowerClass`, and `exp(c / p^r) ∈ PowerClass 0`.
3. Generalized `MarkedJacobian` over any `CharZero` domain `K` with injective
`algebraMap K R` and non-zero-divisor Jacobian determinant via lexicographic
leading units on `MvPowerSeries σ R` (for finite linearly ordered `σ`). -/
public section
namespace CubicTheta.AllD
open Complex Filter Set MeasureTheory MvPolynomial Matrix
open scoped Topology
noncomputable section

/-! ### 1. Extreme Ray `E_d = ℝ_{≥0} A_0` and Strict Positivity of `rotIm` -/

/-- The argument `θ_0(d) = α_0(d) - π/2 = -(d - 2) π / (2 (d - 1))` of the
principal extreme saddle `A_0(d)`. -/
def principalAngle (d : ℕ) : ℝ := saddleAngle d 0 - Real.pi / 2

/-- The principal extreme saddle `A_0(d) = (d - 1) exp(i θ_0(d))`. -/
def principalSaddle (d : ℕ) : ℂ := saddleAction d 0

theorem principalAngle_eq {d : ℕ} (hd : 3 ≤ d) :
    principalAngle d = -(((d - 2 : ℕ) : ℝ) / (2 * ((d - 1 : ℕ) : ℝ))) * Real.pi := by
  unfold principalAngle saddleAngle
  have hr0 : ((d - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show d - 1 ≠ 0 by omega)
  have hd2 : ((d - 2 : ℕ) : ℝ) = ((d - 1 : ℕ) : ℝ) - 1 := by
    have : d - 2 + 1 = d - 1 := by omega
    have hcast : ((d - 2 : ℕ) : ℝ) + 1 = ((d - 1 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  rw [hd2]
  field_simp [hr0]
  ring

theorem principalSaddle_re_pos {d : ℕ} (hd : 3 ≤ d) : 0 < (principalSaddle d).re :=
  uhp_saddle_re_pos hd (by omega)

theorem principalSaddle_ne_zero {d : ℕ} (hd : 3 ≤ d) : principalSaddle d ≠ 0 := by
  intro h
  have := principalSaddle_re_pos hd
  simp [h] at this

/-- Rotation test functional `z ↦ Im(exp(-i θ_0(d)) z)`. It vanishes on the
extreme ray `ℝ A_0(d)` and is strictly positive on every other active saddle. -/
def rotIm (d : ℕ) (z : ℂ) : ℝ := (Complex.exp (-I * (principalAngle d : ℂ)) * z).im

def rotImHom (d : ℕ) : ℂ →+ ℝ where
  toFun := rotIm d
  map_zero' := by simp [rotIm]
  map_add' x y := by simp [rotIm, mul_add]

@[simp] theorem rotIm_zero (d : ℕ) : rotIm d 0 = 0 := (rotImHom d).map_zero
@[simp] theorem rotIm_add (d : ℕ) (x y : ℂ) : rotIm d (x + y) = rotIm d x + rotIm d y :=
  (rotImHom d).map_add x y

theorem rotIm_smul_real (d : ℕ) (t : ℝ) (z : ℂ) : rotIm d ((t : ℂ) * z) = t * rotIm d z := by
  unfold rotIm
  rw [mul_left_comm, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

theorem rotIm_principal {d : ℕ} (hd : 3 ≤ d) : rotIm d (principalSaddle d) = 0 := by
  unfold rotIm principalSaddle
  rw [saddleAction_polar hd 0]
  change (Complex.exp (-I * (principalAngle d : ℂ)) *
    (((d - 1 : ℕ) : ℂ) * Complex.exp (I * (principalAngle d : ℂ)))).im = 0
  rw [mul_left_comm, ← Complex.exp_add]
  have h0 : -I * (principalAngle d : ℂ) + I * (principalAngle d : ℂ) = 0 := by ring
  rw [h0, Complex.exp_zero, mul_one, Complex.natCast_im]

private theorem rotIm_saddleAction {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    rotIm d (saddleAction d ℓ) =
      ((d - 1 : ℕ) : ℝ) * Real.sin (saddleAngle d ℓ - saddleAngle d 0) := by
  unfold rotIm
  rw [saddleAction_polar hd ℓ, mul_left_comm, ← Complex.exp_add]
  have hexp : -I * (principalAngle d : ℂ) + I * ((saddleAngle d ℓ - Real.pi / 2 : ℝ) : ℂ) =
      ((saddleAngle d ℓ - saddleAngle d 0 : ℝ) : ℂ) * I := by
    unfold principalAngle; push_cast; ring
  rw [hexp, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
      Complex.exp_ofReal_mul_I_im]

private theorem rotIm_star_saddleAction {d : ℕ} (hd : 3 ≤ d) (ℓ : ℕ) :
    rotIm d (star (saddleAction d ℓ)) =
      ((d - 1 : ℕ) : ℝ) * Real.sin (saddleAngle d ℓ + saddleAngle d 0) := by
  unfold rotIm
  have hstar : star (saddleAction d ℓ) =
      ((d - 1 : ℕ) : ℂ) * Complex.exp (I * ((Real.pi / 2 - saddleAngle d ℓ : ℝ) : ℂ)) := by
    rw [saddleAction_polar hd ℓ, star_mul', Complex.star_def, Complex.conj_natCast,
        ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  rw [hstar, mul_left_comm, ← Complex.exp_add]
  have hexp : -I * (principalAngle d : ℂ) + I * ((Real.pi / 2 - saddleAngle d ℓ : ℝ) : ℂ) =
      ((Real.pi - (saddleAngle d ℓ + saddleAngle d 0) : ℝ) : ℂ) * I := by
    unfold principalAngle; push_cast; ring
  rw [hexp, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
      Complex.exp_ofReal_mul_I_im, Real.sin_pi_sub]

/-- **Exact Extreme-Ray Positivity Theorem**: Every active saddle `z ∈ activeSaddles d`
other than `A_0(d)` has strictly positive rotated imaginary part `rotIm d z > 0`. -/
theorem rotIm_other_active_pos {d : ℕ} (hd : 3 ≤ d) {z : ℂ}
    (hz : z ∈ activeSaddles d) (hne : z ≠ principalSaddle d) :
    0 < rotIm d z := by
  classical
  have hr_pos : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
  unfold activeSaddles at hz
  by_cases he : Even d
  · simp only [he, ↓reduceIte, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨ℓ, hℓ, rfl⟩ := hz
    have hℓ0 : 1 ≤ ℓ := by
      by_contra h0
      have : ℓ = 0 := by omega
      subst this; exact hne rfl
    rw [rotIm_saddleAction hd ℓ]
    have hdiff : saddleAngle d ℓ - saddleAngle d 0 =
        2 * (ℓ : ℝ) * Real.pi / ((d - 1 : ℕ) : ℝ) := by
      unfold saddleAngle; field_simp [hr_pos.ne']; ring
    rw [hdiff]
    have hpos : 0 < 2 * (ℓ : ℝ) * Real.pi / ((d - 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (show 0 < ℓ by omega)
      positivity
    have hlt : 2 * (ℓ : ℝ) * Real.pi / ((d - 1 : ℕ) : ℝ) < Real.pi := by
      rw [div_lt_iff₀ hr_pos]
      have hnat : 2 * ℓ < d - 1 := by omega
      have hreal : 2 * (ℓ : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
      nlinarith [Real.pi_pos]
    exact mul_pos hr_pos (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
  · have ho : Odd d := Nat.not_even_iff_odd.mp he
    simp only [he, ↓reduceIte, Finset.mem_union, Finset.mem_image, Finset.mem_range] at hz
    rcases hz with ⟨ℓ, hℓ, rfl⟩ | ⟨ℓ, hℓ, rfl⟩
    · have hℓ0 : 1 ≤ ℓ := by
        by_contra h0
        have : ℓ = 0 := by omega
        subst this; exact hne rfl
      rw [rotIm_saddleAction hd ℓ]
      have hdiff : saddleAngle d ℓ - saddleAngle d 0 =
          2 * (ℓ : ℝ) * Real.pi / ((d - 1 : ℕ) : ℝ) := by
        unfold saddleAngle; field_simp [hr_pos.ne']; ring
      rw [hdiff]
      have hpos : 0 < 2 * (ℓ : ℝ) * Real.pi / ((d - 1 : ℕ) : ℝ) := by
        have : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (show 0 < ℓ by omega)
        positivity
      have hlt : 2 * (ℓ : ℝ) * Real.pi / ((d - 1 : ℕ) : ℝ) < Real.pi := by
        rw [div_lt_iff₀ hr_pos]
        have hnat : 2 * ℓ < d - 1 := by omega
        have hreal : 2 * (ℓ : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
        nlinarith [Real.pi_pos]
      exact mul_pos hr_pos (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
    · rw [rotIm_star_saddleAction hd ℓ]
      obtain ⟨hℓ0, hℓh⟩ := odd_active_angle_lt_pi_div_two hd ho hℓ
      obtain ⟨h00, h0h⟩ := odd_active_angle_lt_pi_div_two hd ho (by omega : 0 < (d + 1) / 4)
      exact mul_pos hr_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))

theorem rotIm_active_nonneg {d : ℕ} (hd : 3 ≤ d) {z : ℂ} (hz : z ∈ activeSaddles d) :
    0 ≤ rotIm d z := by
  by_cases h0 : z = principalSaddle d
  · rw [h0, rotIm_principal hd]
  · exact (rotIm_other_active_pos hd hz h0).le

/-- Exact face characterization: inside the half-space `{rotIm ≥ 0}`, a sum lies
on the extreme face `{rotIm = 0}` iff BOTH summands lie on the extreme face. -/
theorem extremeRay_face_iff {d : ℕ} {a b : ℂ} (ha : 0 ≤ rotIm d a) (hb : 0 ≤ rotIm d b) :
    rotIm d (a + b) = 0 ↔ rotIm d a = 0 ∧ rotIm d b = 0 := by
  rw [rotIm_add]
  constructor
  · intro h; constructor <;> linarith
  · rintro ⟨h1, h2⟩; linarith

/-! ### 2. Extreme-Ray Prime-Ideal Algebra Homomorphism `Π_E` on `AddMonoidAlgebra` -/

/-- The closed half-space `{z ∈ ℂ | rotIm d z ≥ 0}` containing the entire active saddle cone. -/
def ActiveHalfSpace (d : ℕ) : AddSubmonoid ℂ where
  carrier := {z : ℂ | 0 ≤ rotIm d z}
  zero_mem' := by simp
  add_mem' ha hb := by
    change 0 ≤ rotIm d (_ + _)
    rw [rotIm_add]
    exact add_nonneg ha hb

/-- The extreme face `{z ∈ ActiveHalfSpace d | rotIm d z = 0}`. -/
def ExtremeFace (d : ℕ) : AddSubmonoid (ActiveHalfSpace d) where
  carrier := {z : ActiveHalfSpace d | rotIm d z.val = 0}
  zero_mem' := by change rotIm d 0 = 0; simp
  add_mem' ha hb := by
    change rotIm d (_ + _) = 0
    rw [rotIm_add, ha, hb, add_zero]

private theorem sum_restrict_extremeFace (d : ℕ)
    (h : AddMonoidAlgebra ℂ (ActiveHalfSpace d)) (F : ActiveHalfSpace d → ℂ)
    (hzero : ∀ a, a ∉ ExtremeFace d → F a = 0) :
    ∑ a ∈ h.coeff.support, F a =
    ∑ a ∈ (h.coeff.comapDomain (Subtype.val : ExtremeFace d → ActiveHalfSpace d)
      Subtype.val_injective.injOn).support, F a.val := by
  classical
  have hfilt : ∑ a ∈ h.coeff.support.filter (fun a ↦ a ∈ ExtremeFace d), F a =
      ∑ a ∈ h.coeff.support, F a :=
    Finset.sum_filter_of_ne (fun a _ hne ↦ by
      by_contra hnot; exact hne (hzero a hnot))
  rw [← hfilt]
  symm
  refine Finset.sum_bij (fun a _ ↦ a.val) ?_ (fun _ _ _ _ hEq ↦ Subtype.ext hEq) ?_ (fun _ _ ↦ rfl)
  · intro a ha
    rw [Finset.mem_filter, Finsupp.mem_support_iff]
    rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply] at ha
    exact ⟨ha, a.property⟩
  · intro a ha
    rw [Finset.mem_filter, Finsupp.mem_support_iff] at ha
    exact ⟨⟨a, ha.2⟩, by rw [Finsupp.mem_support_iff, Finsupp.comapDomain_apply]; exact ha.1, rfl⟩

/-- **Exact Extreme-Ray Prime-Ideal Projection `Π_E`**: discarding all terms
outside the extreme face `{rotIm d z = 0}` is an exact `ℂ`-algebra homomorphism
on `AddMonoidAlgebra ℂ (ActiveHalfSpace d)`. -/
def extremeRayProj (d : ℕ) :
    AddMonoidAlgebra ℂ (ActiveHalfSpace d) →ₐ[ℂ] AddMonoidAlgebra ℂ (ExtremeFace d) where
  toFun f := AddMonoidAlgebra.ofCoeff (f.coeff.comapDomain Subtype.val Subtype.val_injective.injOn)
  map_one' := by
    classical
    ext z
    simp only [Finsupp.comapDomain_apply, AddMonoidAlgebra.one_def,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hz : (0 : ExtremeFace d) = z
    · subst hz; simp
    · have hne : (0 : ActiveHalfSpace d) ≠ z.val := fun h ↦ hz (Subtype.ext h)
      simp [hz, hne]
  map_mul' f g := by
    classical
    ext z
    simp only [Finsupp.comapDomain_apply, AddMonoidAlgebra.coeff_mul]
    change ∑ a ∈ f.coeff.support, ∑ b ∈ g.coeff.support,
        (if a + b = z.val then f.coeff a * g.coeff b else 0) =
      ∑ a ∈ (f.coeff.comapDomain Subtype.val Subtype.val_injective.injOn).support,
        ∑ b ∈ (g.coeff.comapDomain Subtype.val Subtype.val_injective.injOn).support,
          if a + b = z then f.coeff a.val * g.coeff b.val else 0
    have houter : ∀ a, a ∉ ExtremeFace d →
        (∑ b ∈ g.coeff.support, if a + b = z.val then f.coeff a * g.coeff b else 0) = 0 := by
      intro a hna
      apply Finset.sum_eq_zero
      intro b _
      split_ifs with hab
      · exfalso
        have hsum : rotIm d (a.val + b.val) = 0 := by
          have heq : a.val + b.val = z.val.val := congrArg Subtype.val hab
          rw [heq]; exact z.property
        exact hna ((extremeRay_face_iff a.property b.property).mp hsum).1
      · rfl
    rw [sum_restrict_extremeFace d f _ houter]
    apply Finset.sum_congr rfl
    intro a _
    have hinner : ∀ b, b ∉ ExtremeFace d →
        (if a.val + b = z.val then f.coeff a.val * g.coeff b else 0) = 0 := by
      intro b hnb
      split_ifs with hab
      · exfalso
        have hsum : rotIm d (a.val.val + b.val) = 0 := by
          have heq : a.val.val + b.val = z.val.val := congrArg Subtype.val hab
          rw [heq]; exact z.property
        exact hnb ((extremeRay_face_iff a.val.property b.property).mp hsum).2
      · rfl
    rw [sum_restrict_extremeFace d g _ hinner]
    apply Finset.sum_congr rfl
    intro b _
    have hiff : a.val + b.val = z.val ↔ a + b = z :=
      ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
    simp [hiff]
  map_zero' := by ext z; simp
  map_add' f g := by ext z; simp
  commutes' c := by
    classical
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    ext z
    simp only [Finsupp.comapDomain_apply,
      AddMonoidAlgebra.coeff_smul, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]
    by_cases hz : (0 : ExtremeFace d) = z
    · subst hz; simp
    · have hne : (0 : ActiveHalfSpace d) ≠ z.val := fun h ↦ hz (Subtype.ext h)
      simp [hz, hne]

theorem extremeRayProj_single_mem (d : ℕ) (z : ExtremeFace d) (c : ℂ) :
    extremeRayProj d (AddMonoidAlgebra.single z.val c) = AddMonoidAlgebra.single z c := by
  classical
  ext w
  simp only [extremeRayProj, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    AddMonoidAlgebra.coeff_ofCoeff, Finsupp.comapDomain_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply]
  have hiff : z.val = w.val ↔ z = w := ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  simp [hiff]

theorem extremeRayProj_single_off (d : ℕ) {z : ActiveHalfSpace d} (hz : z ∉ ExtremeFace d) (c : ℂ) :
    extremeRayProj d (AddMonoidAlgebra.single z c) = 0 := by
  classical
  ext w
  simp only [extremeRayProj, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    AddMonoidAlgebra.coeff_ofCoeff, Finsupp.comapDomain_apply, AddMonoidAlgebra.coeff_single,
    Finsupp.single_apply, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have hne : z ≠ w.val := fun h ↦ hz (h ▸ w.property)
  simp [hne]

/-! ### 3. `FiniteParities M`, Argument Rescaling, and `exp(c / p^r) ∈ PowerClass 0` -/

/-- Finite parity sum `⊕_{r=0}^{M-1} PowerClass (r / M)` generalizing `TwoParities`
(`M = 2`) to arbitrary modulus `M ≥ 1` (needed for `p^{(d-1)/d}` and dilations). -/
def FiniteParities (M : ℕ) (f : ℝ → ℂ) : Prop :=
  ∃ a : Fin M → ℝ → ℂ, (∀ r : Fin M, PowerClass ((r.val : ℝ) / (M : ℝ)) (a r)) ∧
    f =ᶠ[atTop] fun x ↦ ∑ r : Fin M, a r x

namespace FiniteParities

theorem congr {M : ℕ} {f g : ℝ → ℂ} (hf : FiniteParities M f) (he : f =ᶠ[atTop] g) :
    FiniteParities M g := by
  obtain ⟨a, ha, hfa⟩ := hf
  exact ⟨a, ha, he.symm.trans hfa⟩

theorem of_class {M : ℕ} (r : Fin M) {f : ℝ → ℂ}
    (hf : PowerClass ((r.val : ℝ) / (M : ℝ)) f) : FiniteParities M f := by
  classical
  refine ⟨fun i ↦ if i = r then f else fun _ ↦ 0, fun i ↦ ?_, ?_⟩
  · by_cases hi : i = r
    · subst hi; simpa using hf
    · simp [hi, PowerClass.zero]
  · filter_upwards with x
    have hsum : (∑ i : Fin M, (if i = r then f else fun _ ↦ (0 : ℂ)) x) = f x := by
      trans ∑ i : Fin M, if i = r then f x else (0 : ℂ)
      · apply Finset.sum_congr rfl; intro i _; split_ifs <;> rfl
      · simp
    exact hsum.symm

theorem of_zero {M : ℕ} (hM : 0 < M) {f : ℝ → ℂ} (hf : PowerClass 0 f) :
    FiniteParities M f := by
  have h0 : ((⟨0, hM⟩ : Fin M).val : ℝ) / (M : ℝ) = 0 := by simp
  exact of_class ⟨0, hM⟩ (h0.symm ▸ hf)

theorem of_half {d : ℕ} (hd : 0 < d) {f : ℝ → ℂ} (hf : PowerClass (1 / 2) f) :
    FiniteParities (2 * d) f := by
  have hlt : d < 2 * d := by omega
  have heq : ((⟨d, hlt⟩ : Fin (2 * d)).val : ℝ) / ((2 * d : ℕ) : ℝ) = 1 / 2 := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast; field_simp [hd0]
  exact of_class ⟨d, hlt⟩ (heq.symm ▸ hf)

theorem of_twoParities {d : ℕ} (hd : 0 < d) {f : ℝ → ℂ} (hf : TwoParities f) :
    FiniteParities (2 * d) f := by
  obtain ⟨a, b, ha, hb, he⟩ := hf
  have hfa := of_zero (M := 2 * d) (by omega) ha
  have hfb := of_half hd hb
  obtain ⟨u, hu, heu⟩ := hfa
  obtain ⟨v, hv, hev⟩ := hfb
  refine ⟨fun r x ↦ u r x + v r x, fun r ↦ (hu r).add (hv r), ?_⟩
  filter_upwards [he, heu, hev] with x hx h1 h2
  rw [hx, h1, h2, Finset.sum_add_distrib]

theorem add {M : ℕ} {f g : ℝ → ℂ} (hf : FiniteParities M f) (hg : FiniteParities M g) :
    FiniteParities M (fun x ↦ f x + g x) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  refine ⟨fun r x ↦ a r x + b r x, fun r ↦ (ha r).add (hb r), ?_⟩
  filter_upwards [hfa, hgb] with x h1 h2
  rw [h1, h2, Finset.sum_add_distrib]

theorem finsetSum {M : ℕ} (hM : 0 < M) {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ i ∈ S, FiniteParities M (f i)) :
    FiniteParities M (fun x ↦ ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using of_zero hM (PowerClass.const 0)
  | insert i S hi ih =>
    simpa [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self ..)).add (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

theorem mul {M : ℕ} (hM : 0 < M) {f g : ℝ → ℂ}
    (hf : FiniteParities M f) (hg : FiniteParities M g) :
    FiniteParities M (fun x ↦ f x * g x) := by
  obtain ⟨a, ha, hfa⟩ := hf
  obtain ⟨b, hb, hgb⟩ := hg
  have hpair (r₁ r₂ : Fin M) : FiniteParities M (fun x ↦ a r₁ x * b r₂ x) := by
    let idx : Fin M := ⟨(r₁.val + r₂.val) % M, Nat.mod_lt _ hM⟩
    let q : ℤ := ((r₁.val + r₂.val) / M : ℕ)
    have hdiv : (r₁.val : ℝ) / (M : ℝ) + (r₂.val : ℝ) / (M : ℝ) =
        (idx.val : ℝ) / (M : ℝ) + (q : ℝ) := by
      have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      have hnat : r₁.val + r₂.val = (r₁.val + r₂.val) % M + M * ((r₁.val + r₂.val) / M) :=
        (Nat.mod_add_div (r₁.val + r₂.val) M).symm
      have hreal : (r₁.val : ℝ) + (r₂.val : ℝ) =
          (idx.val : ℝ) + (M : ℝ) * (q : ℝ) := by
        dsimp [idx, q]
        have hcast : ((r₁.val + r₂.val : ℕ) : ℝ) =
            (((r₁.val + r₂.val) % M + M * ((r₁.val + r₂.val) / M) : ℕ) : ℝ) := by
          exact_mod_cast hnat
        push_cast at hcast
        exact hcast
      field_simp [hM0]
      linarith
    exact of_class idx (((ha r₁).mul (hb r₂)).reindex q hdiv)
  have hsum := finsetSum hM (Finset.univ : Finset (Fin M × Fin M))
    (fun p x ↦ a p.1 x * b p.2 x) (fun p _ ↦ hpair p.1 p.2)
  refine hsum.congr ?_
  filter_upwards [hfa, hgb] with x h1 h2
  rw [h1, h2, Finset.sum_mul_sum, ← Finset.sum_product']
  rfl

/-- Every `PowerClass s` function is either eventually zero or has a nonzero leading
power asymptotic `x^(n - s - k) • f x → z ≠ 0` for some `n : ℕ, k : ℤ`. -/
private theorem powerClass_leading {s : ℝ} {f : ℝ → ℂ} (hf : PowerClass s f) :
    (∀ᶠ x : ℝ in atTop, f x = 0) ∨
      ∃ (n : ℕ) (k : ℤ) (z : ℂ), z ≠ 0 ∧
        Tendsto (fun x : ℝ ↦ x ^ ((n : ℝ) - (s + (k : ℝ))) • f x) atTop (𝓝 z) := by
  obtain ⟨k, F, hF, he⟩ := hf
  obtain ⟨ha, C, D, _, hD, hg⟩ := hF
  rcases raySum_dichotomy ha hD (fun u hu ↦ hg u hu.le) with hz | ⟨n, z, hzn, hl⟩
  · left
    filter_upwards [he, (eventually_gt_atTop (0 : ℝ)).mono hz] with x hx h0
    rw [hx, h0, smul_zero]
  · right
    refine ⟨n, k, z, hzn, ?_⟩
    apply hl.congr'
    filter_upwards [he, eventually_gt_atTop (0 : ℝ)] with x hx hxp
    rw [hx, smul_smul, ← Real.rpow_add hxp, sub_add_cancel, Real.rpow_natCast]

/-- **Exact Leading-Order Dichotomy for `FiniteParities M`**: since the `M` cosets
`ℤ + r/M` (`0 ≤ r < M`) are pairwise disjoint, any `FiniteParities M` function is
either eventually zero or admits an exact nonzero leading power asymptotic. -/
theorem leading_dichotomy {M : ℕ} (hM : 0 < M) {f : ℝ → ℂ} (hf : FiniteParities M f) :
    (∀ᶠ x : ℝ in atTop, f x = 0) ∨
      ∃ v : ℝ, ∃ z : ℂ, z ≠ 0 ∧ Tendsto (fun x : ℝ ↦ x ^ v • f x) atTop (𝓝 z) := by
  classical
  obtain ⟨a, ha, hfa⟩ := hf
  let active : Finset (Fin M) := Finset.univ.filter fun r ↦ ¬ ∀ᶠ x : ℝ in atTop, a r x = 0
  by_cases hne : active.Nonempty
  · right
    have hlead (r : Fin M) (hr : r ∈ active) :=
      (powerClass_leading (ha r)).resolve_left (Finset.mem_filter.mp hr).2
    choose n k z hz hl using hlead
    let ord (r : Fin M) : ℝ :=
      if hr : r ∈ active then (n r hr : ℝ) - ((r.val : ℝ) / (M : ℝ) + (k r hr : ℝ)) else 0
    obtain ⟨r₀, hr₀, hmin⟩ := active.exists_min_image ord hne
    have hstrict : ∀ r (hr : r ∈ active), r ≠ r₀ → ord r₀ < ord r := by
      intro r hr hne_r
      apply lt_of_le_of_ne (hmin r hr)
      intro heq
      simp only [ord, hr₀, hr, ↓reduceDIte] at heq
      have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
      have hmul : ((n r₀ hr₀ : ℝ) - (k r₀ hr₀ : ℝ)) * (M : ℝ) - (r₀.val : ℝ) =
          ((n r hr : ℝ) - (k r hr : ℝ)) * (M : ℝ) - (r.val : ℝ) := by
        have h1 := congrArg (· * (M : ℝ)) heq
        field_simp [hM0] at h1
        linarith
      have hint : (((n r₀ hr₀ : ℤ) - k r₀ hr₀) * (M : ℤ) - (r₀.val : ℤ)) =
          (((n r hr : ℤ) - k r hr) * (M : ℤ) - (r.val : ℤ)) := by
        exact_mod_cast hmul
      have hmod : (r₀.val : ℤ) % (M : ℤ) = (r.val : ℤ) % (M : ℤ) := by
        have hdiff : ((M : ℤ)) ∣ ((r.val : ℤ) - (r₀.val : ℤ)) :=
          ⟨((n r hr : ℤ) - k r hr) - ((n r₀ hr₀ : ℤ) - k r₀ hr₀), by linarith⟩
        exact Int.modEq_iff_dvd.mpr hdiff
      have h1 : (r₀.val : ℤ) % (M : ℤ) = (r₀.val : ℤ) :=
        Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast r₀.isLt)
      have h2 : (r.val : ℤ) % (M : ℤ) = (r.val : ℤ) :=
        Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast r.isLt)
      rw [h1, h2] at hmod
      exact hne_r (Fin.ext (by exact_mod_cast hmod.symm))
    refine ⟨ord r₀, z r₀ hr₀, hz r₀ hr₀, ?_⟩
    have hterm (r : Fin M) :
        Tendsto (fun x : ℝ ↦ x ^ ord r₀ • a r x) atTop (𝓝 (if r = r₀ then z r₀ hr₀ else 0)) := by
      by_cases hrr₀ : r = r₀
      · subst hrr₀
        simpa only [↓reduceIte, ord, hr₀, ↓reduceDIte] using hl r hr₀
      · simp only [hrr₀, ↓reduceIte]
        by_cases hact : r ∈ active
        · have hlt : ord r₀ < ord r := hstrict r hact hrr₀
          have hdec : Tendsto (fun x : ℝ ↦ x ^ (ord r₀ - ord r)) atTop (𝓝 0) := by
            simpa [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr hlt)
          have hlr : Tendsto (fun x : ℝ ↦ x ^ ord r • a r x) atTop (𝓝 (z r hact)) := by
            simpa only [ord, hact, ↓reduceDIte] using hl r hact
          have hprod := hdec.smul hlr
          rw [zero_smul] at hprod
          apply hprod.congr'
          filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
          rw [smul_smul, ← Real.rpow_add hx, sub_add_cancel]
        · have hz_a : ∀ᶠ x : ℝ in atTop, a r x = 0 := by
            simpa [active] using hact
          apply tendsto_const_nhds.congr'
          filter_upwards [hz_a] with x hx
          simp [hx]
    have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin M)) (fun r _ ↦ hterm r)
    rw [Finset.sum_ite_eq' Finset.univ r₀] at hsum
    simp only [Finset.mem_univ, ↓reduceIte] at hsum
    apply hsum.congr'
    filter_upwards [hfa] with x hx
    rw [hx, Finset.smul_sum]
  · left
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hall : ∀ r : Fin M, ∀ᶠ x : ℝ in atTop, a r x = 0 := by
      intro r
      have hr : r ∉ active := hne ▸ Finset.notMem_empty r
      simpa [active] using hr
    filter_upwards [hfa, eventually_all.mpr hall] with x hx h0
    rw [hx]
    simp [h0]

end FiniteParities

/-! ### 4. Argument Rescaling & `exp(c / p^r) ∈ PowerClass 0` -/

theorem rayDensity_scale_arg {F : ℝ → ℂ} (hF : RayDensity F) {σ : ℝ} (hσ : 0 < σ) :
    RayDensity (fun u : ℝ ↦ F (u / σ)) := by
  obtain ⟨ha, C, D, hC, hD, hbound⟩ := hF
  refine ⟨fun u hu ↦ ?_, C, D / σ, hC, div_nonneg hD hσ.le, fun u hu ↦ ?_⟩
  · have hlin : AnalyticAt ℝ (fun x : ℝ ↦ x / σ) u :=
      analyticAt_id.div analyticAt_const hσ.ne'
    exact (ha (u / σ) (div_nonneg hu hσ.le)).comp_of_eq hlin rfl
  · have h1 := hbound (u / σ) (div_nonneg hu hσ.le)
    rwa [show D * (u / σ) = (D / σ) * u by ring] at h1

theorem atPower_scale_arg {s : ℝ} {f : ℝ → ℂ} (hf : AtPower s f) {σ : ℝ} (hσ : 0 < σ) :
    AtPower s (fun x : ℝ ↦ f (σ * x)) := by
  obtain ⟨F, hF, hfe⟩ := hf
  have hF' : RayDensity (fun u : ℝ ↦ ((σ ^ s : ℝ) : ℂ) * F (u / σ)) := by
    have hsc := rayDensity_scale_arg hF hσ
    obtain ⟨ha, C, D, hC, hD, hb⟩ := hsc
    refine ⟨fun u hu ↦ analyticAt_const.mul (ha u hu),
      ‖((σ ^ s : ℝ) : ℂ)‖ * C, D, mul_nonneg (norm_nonneg _) hC, hD, fun u hu ↦ ?_⟩
    rw [norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb u hu) (norm_nonneg _)
  refine ⟨_, hF', ?_⟩
  have hcomp : ∀ᶠ x : ℝ in atTop, f (σ * x) = (σ * x) ^ s • raySum F (σ * x) :=
    (tendsto_id.const_mul_atTop hσ).eventually hfe
  filter_upwards [hcomp, eventually_gt_atTop (0 : ℝ)] with x hx hxp
  rw [hx, Real.mul_rpow hσ.le hxp.le, mul_comm (σ ^ s) (x ^ s), ← smul_smul]
  congr 1
  unfold raySum
  rw [Complex.real_smul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u _
  dsimp only
  rw [Complex.real_smul, Complex.real_smul, show u / (σ * x) = (u / x) / σ by ring]
  ring

theorem powerClass_scale_arg {s : ℝ} {f : ℝ → ℂ} (hf : PowerClass s f) {σ : ℝ} (hσ : 0 < σ) :
    PowerClass s (fun x : ℝ ↦ f (σ * x)) := by
  obtain ⟨k, hk⟩ := hf
  exact ⟨k, atPower_scale_arg hk hσ⟩

theorem powerClass_rpow (s : ℝ) : PowerClass s (fun x : ℝ ↦ ((x ^ s : ℝ) : ℂ)) := by
  refine ⟨0, fun _ ↦ 1, RayDensity.const 1, ?_⟩
  filter_upwards with x
  have h1 : raySum (fun _ ↦ (1 : ℂ)) x = 1 := by
    simp only [raySum, integral_smul_const, integral_exp_neg_Ioi_zero, one_smul]
  simp [h1, Complex.real_smul]

private def expInvCoeff (r : ℕ) (c : ℝ) (m : ℕ) : ℂ :=
  ((c ^ m / ((m.factorial : ℝ) * ((r * m).factorial : ℝ)) : ℝ) : ℂ)

private def expInvKernelC (r : ℕ) (c : ℝ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, expInvCoeff r c m * z ^ (r * m)

private def expInvKernel (r : ℕ) (c : ℝ) (u : ℝ) : ℂ :=
  expInvKernelC r c (u : ℂ)

private theorem expInvTerm_norm_le {r : ℕ} (hr : 1 ≤ r) (c : ℝ) (z : ℂ) (m : ℕ) :
    ‖expInvCoeff r c m * z ^ (r * m)‖ ≤
      ((|c| + 1) * ‖z‖) ^ (r * m) / ((r * m).factorial : ℝ) := by
  rw [expInvCoeff, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (by positivity : (0 : ℝ) < (m.factorial : ℝ) * ((r * m).factorial : ℝ))]
  have hm_ge1 : (1 : ℝ) ≤ (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hc1 : |c| ^ m ≤ (|c| + 1) ^ (r * m) := by
    calc |c| ^ m ≤ (|c| + 1) ^ m := pow_le_pow_left₀ (abs_nonneg c) (by linarith) m
      _ ≤ (|c| + 1) ^ (r * m) :=
          pow_le_pow_right₀ (by linarith [abs_nonneg c]) (Nat.le_mul_of_pos_left m (by omega))
  have hdiv : |c| ^ m / ((m.factorial : ℝ) * ((r * m).factorial : ℝ)) ≤
      (|c| + 1) ^ (r * m) / ((r * m).factorial : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : |c| ^ m * ((r * m).factorial : ℝ) ≤
        (|c| + 1) ^ (r * m) * ((r * m).factorial : ℝ) :=
      mul_le_mul_of_nonneg_right hc1 (by positivity)
    have h2 : (|c| + 1) ^ (r * m) * ((r * m).factorial : ℝ) ≤
        (|c| + 1) ^ (r * m) * ((m.factorial : ℝ) * ((r * m).factorial : ℝ)) := by
      have : (|c| + 1) ^ (r * m) * ((r * m).factorial : ℝ) * 1 ≤
          (|c| + 1) ^ (r * m) * ((r * m).factorial : ℝ) * (m.factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hm_ge1 (by positivity)
      linarith
    exact h1.trans h2
  rw [mul_pow, mul_div_right_comm]
  exact mul_le_mul_of_nonneg_right hdiv (pow_nonneg (norm_nonneg z) _)

private theorem expInv_summable_bound {r : ℕ} (hr : 1 ≤ r) (c : ℝ) (R : ℝ) :
    Summable (fun m : ℕ ↦ ((|c| + 1) * R) ^ (r * m) / ((r * m).factorial : ℝ)) := by
  have hinj : Function.Injective (fun m : ℕ ↦ r * m) :=
    fun a b h ↦ Nat.eq_of_mul_eq_mul_left (by omega : 0 < r) h
  exact (Real.summable_pow_div_factorial ((|c| + 1) * R)).comp_injective hinj

private theorem expInvKernelC_differentiable {r : ℕ} (hr : 1 ≤ r) (c : ℝ) :
    Differentiable ℂ (expInvKernelC r c) := by
  intro z₀
  let R : ℝ := ‖z₀‖ + 1
  have hR : 0 < R := by dsimp [R]; linarith [norm_nonneg z₀]
  have hz₀ : z₀ ∈ Metric.ball (0 : ℂ) R := by simp [Metric.mem_ball, R]
  let f (m : ℕ) (z : ℂ) : ℂ := expInvCoeff r c (m + 1) * z ^ (r * (m + 1))
  let g (m : ℕ) (z : ℂ) : ℂ :=
    expInvCoeff r c (m + 1) * ((r * (m + 1) : ℕ) : ℂ) * z ^ (r * (m + 1) - 1)
  have hd (m : ℕ) (z : ℂ) : HasDerivAt (f m) (g m z) z := by
    have h := (hasDerivAt_pow (r * (m + 1)) z).const_mul (expInvCoeff r c (m + 1))
    simpa [f, g, mul_assoc] using h
  let u (m : ℕ) : ℝ := (|c| + 1) * (((|c| + 1) * R) ^ (r * (m + 1) - 1) /
      (((r * (m + 1) - 1).factorial : ℝ)))
  have hu_sum : Summable u := by
    have hinj : Function.Injective (fun m : ℕ ↦ r * (m + 1) - 1) := by
      intro a b hab
      dsimp only at hab
      have ha1 : 1 ≤ r * (a + 1) := Nat.mul_pos (by omega) (Nat.succ_pos a)
      have hb1 : 1 ≤ r * (b + 1) := Nat.mul_pos (by omega) (Nat.succ_pos b)
      have heq : r * (a + 1) = r * (b + 1) := by omega
      exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_left (by omega : 0 < r) heq)
    exact ((Real.summable_pow_div_factorial ((|c| + 1) * R)).comp_injective hinj).mul_left _
  have hbound : ∀ m (z : ℂ), z ∈ Metric.ball (0 : ℂ) R → ‖g m z‖ ≤ u m := by
    intro m z hz
    have hzR : ‖z‖ ≤ R := by simpa [Metric.mem_ball] using (Metric.mem_ball.mp hz).le
    have hk_pos : 1 ≤ r * (m + 1) := Nat.mul_pos (by omega) (Nat.succ_pos m)
    have hfac : ((r * (m + 1)).factorial : ℝ) =
        ((r * (m + 1) : ℕ) : ℝ) * (((r * (m + 1) - 1).factorial : ℝ)) := by
      have h1 : (r * (m + 1)).factorial = (r * (m + 1)) * (r * (m + 1) - 1).factorial :=
        (Nat.mul_factorial_pred (by omega : r * (m + 1) ≠ 0)).symm
      exact_mod_cast h1
    rw [show g m z = (expInvCoeff r c (m + 1) * ((r * (m + 1) : ℕ) : ℂ)) * z ^ (r * (m + 1) - 1)
        by rfl, norm_mul, norm_pow, norm_mul, expInvCoeff, Complex.norm_natCast,
        Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow,
        abs_of_pos (by positivity : (0 : ℝ) < ((m + 1).factorial : ℝ) * ((r * (m + 1)).factorial : ℝ))]
    rw [hfac]
    have hkn : ((r * (m + 1) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show r * (m + 1) ≠ 0 by omega)
    have hsimp : |c| ^ (m + 1) / (((m + 1).factorial : ℝ) *
        (((r * (m + 1) : ℕ) : ℝ) * (((r * (m + 1) - 1).factorial : ℝ)))) *
        ((r * (m + 1) : ℕ) : ℝ) =
        |c| ^ (m + 1) / (((m + 1).factorial : ℝ) * (((r * (m + 1) - 1).factorial : ℝ))) := by
      field_simp [hkn]
    rw [hsimp]
    have hm_ge1 : (1 : ℝ) ≤ ((m + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (m + 1)
    have hc1 : |c| ^ (m + 1) ≤ (|c| + 1) ^ (r * (m + 1)) := by
      calc |c| ^ (m + 1) ≤ (|c| + 1) ^ (m + 1) := pow_le_pow_left₀ (abs_nonneg c) (by linarith) _
        _ ≤ (|c| + 1) ^ (r * (m + 1)) :=
            pow_le_pow_right₀ (by linarith [abs_nonneg c]) (Nat.le_mul_of_pos_left _ (by omega))
    have hpow_split : (|c| + 1) ^ (r * (m + 1)) = (|c| + 1) * (|c| + 1) ^ (r * (m + 1) - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hk_pos]
    have hdiv : |c| ^ (m + 1) / (((m + 1).factorial : ℝ) * (((r * (m + 1) - 1).factorial : ℝ))) ≤
        ((|c| + 1) * (|c| + 1) ^ (r * (m + 1) - 1)) / (((r * (m + 1) - 1).factorial : ℝ)) := by
      rw [← hpow_split, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : |c| ^ (m + 1) * (((r * (m + 1) - 1).factorial : ℝ)) ≤
          (|c| + 1) ^ (r * (m + 1)) * (((r * (m + 1) - 1).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_right hc1 (by positivity)
      have h2 : (|c| + 1) ^ (r * (m + 1)) * (((r * (m + 1) - 1).factorial : ℝ)) * 1 ≤
          (|c| + 1) ^ (r * (m + 1)) * (((r * (m + 1) - 1).factorial : ℝ)) * ((m + 1).factorial : ℝ) :=
        mul_le_mul_of_nonneg_left hm_ge1 (by positivity)
      linarith
    calc |c| ^ (m + 1) / (((m + 1).factorial : ℝ) * (((r * (m + 1) - 1).factorial : ℝ))) *
          ‖z‖ ^ (r * (m + 1) - 1)
        ≤ ((|c| + 1) * (|c| + 1) ^ (r * (m + 1) - 1)) / (((r * (m + 1) - 1).factorial : ℝ)) *
          R ^ (r * (m + 1) - 1) :=
          mul_le_mul hdiv (pow_le_pow_left₀ (norm_nonneg z) hzR _) (by positivity) (by positivity)
      _ = u m := by dsimp [u]; rw [mul_pow]; ring
  have hsum_all (z : ℂ) : Summable (fun m : ℕ ↦ expInvCoeff r c m * z ^ (r * m)) :=
    Summable.of_norm_bounded (expInv_summable_bound hr c ‖z‖) (expInvTerm_norm_le hr c z)
  have hsum_f : Summable (fun m ↦ f m z₀) :=
    (hsum_all z₀).comp_injective Nat.succ_injective
  have hd_tsum := hasDerivAt_tsum_of_isPreconnected hu_sum Metric.isOpen_ball
    (convex_ball (0 : ℂ) R).isPreconnected (fun m z _ ↦ hd m z) hbound hz₀ hsum_f hz₀
  have hsplit : expInvKernelC r c = fun z ↦ (1 : ℂ) + ∑' m : ℕ, f m z := by
    funext z
    have hs := (hsum_all z).sum_add_tsum_nat_add 1
    simpa [expInvKernelC, f, expInvCoeff] using hs.symm
  rw [hsplit]
  exact (hd_tsum.const_add (1 : ℂ)).differentiableAt

private theorem expInvKernel_rayDensity {r : ℕ} (hr : 1 ≤ r) (c : ℝ) :
    RayDensity (expInvKernel r c) := by
  have hanC : AnalyticOnNhd ℂ (expInvKernelC r c) Set.univ :=
    (expInvKernelC_differentiable hr c).differentiableOn.analyticOnNhd isOpen_univ
  refine ⟨fun u _ ↦ (hanC (u : ℂ) (Set.mem_univ _)).restrictScalars.comp
      (Complex.ofRealCLM.analyticAt u),
    1, |c| + 1, zero_le_one, by positivity, fun u hu ↦ ?_⟩
  rw [one_mul]
  have hsum := expInv_summable_bound hr c u
  have hterm : ∀ m : ℕ, ‖expInvCoeff r c m * (u : ℂ) ^ (r * m)‖ ≤
      ((|c| + 1) * u) ^ (r * m) / ((r * m).factorial : ℝ) := fun m ↦ by
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu] using
      expInvTerm_norm_le hr c (u : ℂ) m
  have hnorm_sum : Summable (fun m : ℕ ↦ ‖expInvCoeff r c m * (u : ℂ) ^ (r * m)‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hsum
  have hle1 : ‖expInvKernel r c u‖ ≤
      ∑' m : ℕ, ((|c| + 1) * u) ^ (r * m) / ((r * m).factorial : ℝ) :=
    (norm_tsum_le_tsum_norm hnorm_sum).trans (hnorm_sum.tsum_le_tsum hterm hsum)
  have hle2 : (∑' m : ℕ, ((|c| + 1) * u) ^ (r * m) / ((r * m).factorial : ℝ)) ≤
      ∑' k : ℕ, ((|c| + 1) * u) ^ k / (k.factorial : ℝ) := by
    have hinj : Function.Injective (fun m : ℕ ↦ r * m) :=
      fun a b h ↦ Nat.eq_of_mul_eq_mul_left (by omega : 0 < r) h
    exact hsum.tsum_le_tsum_of_inj (fun m ↦ r * m) hinj (fun k _ ↦ by positivity) (fun _ ↦ le_rfl)
      (Real.summable_pow_div_factorial ((|c| + 1) * u))
  have hexp : (∑' k : ℕ, ((|c| + 1) * u) ^ k / (k.factorial : ℝ)) =
      Real.exp ((|c| + 1) * u) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact hle1.trans (hle2.trans_eq hexp)

/-- **Unconditional `PowerClass 0` membership for `exp(c / p^r)`** (`r ≥ 1`, `c ∈ ℝ`). -/
theorem exp_inv_pow_powerClass {r : ℕ} (hr : 1 ≤ r) (c : ℝ) :
    PowerClass 0 (fun p : ℝ ↦ (Real.exp (c / p ^ r) : ℂ)) := by
  refine ⟨0, expInvKernel r c, expInvKernel_rayDensity hr c, ?_⟩
  filter_upwards [eventually_gt_atTop (|c| + 2)] with p hp
  have hp_pos : 0 < p := by linarith [abs_nonneg c]
  simp only [Int.cast_zero, add_zero, Real.rpow_zero, one_smul]
  rw [raySum_eq_weighted _ hp_pos]
  let term (m : ℕ) (u : ℝ) : ℂ :=
    Real.exp (-p * u) • (expInvCoeff r c m * (u : ℂ) ^ (r * m))
  have hpt : ∀ u : ℝ, weighted p (expInvKernel r c) u = ∑' m : ℕ, term m u := by
    intro u
    unfold weighted expInvKernel expInvKernelC
    rw [Complex.real_smul, ← tsum_mul_left]
    apply tsum_congr; intro m; simp [term, Complex.real_smul, neg_mul]
  have hint_m (m : ℕ) :
      (∫ u in Ioi (0 : ℝ), u ^ (r * m) * Real.exp (-p * u)) =
        ((r * m).factorial : ℝ) / p ^ (r * m + 1) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := ((r * m : ℕ) : ℝ) + 1)
      (by positivity) hp_pos
    have hrpow : ∀ u ∈ Ioi (0 : ℝ),
        u ^ (((r * m : ℕ) : ℝ) + 1 - 1) * Real.exp (-(p * u)) = u ^ (r * m) * Real.exp (-p * u) := by
      intro u _
      rw [add_sub_cancel_right, Real.rpow_natCast, neg_mul]
    rw [← setIntegral_congr_fun measurableSet_Ioi hrpow, h, Real.Gamma_nat_eq_factorial,
        show (((r * m : ℕ) : ℝ) + 1) = ((r * m + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast, one_div, inv_pow, div_eq_mul_inv, mul_comm]
  have hint_norm (m : ℕ) :
      (∫ u in Ioi (0 : ℝ), ‖term m u‖) =
        (|c| ^ m / (m.factorial : ℝ)) * p⁻¹ * (p ^ r)⁻¹ ^ m := by
    have heq : EqOn (fun u : ℝ ↦ ‖term m u‖)
        (fun u : ℝ ↦ (|c| ^ m / ((m.factorial : ℝ) * ((r * m).factorial : ℝ))) *
          (u ^ (r * m) * Real.exp (-p * u))) (Ioi 0) := by
      intro u hu
      change 0 < u at hu
      simp only [term, expInvCoeff, norm_smul, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos hu, abs_div, abs_pow,
        abs_of_pos (by positivity : (0 : ℝ) < (m.factorial : ℝ) * ((r * m).factorial : ℝ))]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, hint_m m]
    have hfac0 : ((r * m).factorial : ℝ) ≠ 0 := by positivity
    rw [pow_succ, pow_mul, inv_pow]
    field_simp [hfac0, hp_pos.ne']
  have hint_m_int (m : ℕ) : IntegrableOn (fun u : ℝ ↦ u ^ (r * m) * Real.exp (-p * u)) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hint_m m]; positivity)
  have hterm_int (m : ℕ) : IntegrableOn (term m) (Ioi 0) := by
    apply (hint_m_int m |>.const_mul (|c| ^ m / ((m.factorial : ℝ) * ((r * m).factorial : ℝ)))).mono'
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
        (continuous_const.mul ((Complex.continuous_ofReal).pow (r * m)))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      change 0 < u at hu
      simp only [term, expInvCoeff, norm_smul, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos hu, abs_div, abs_pow,
        abs_of_pos (by positivity : (0 : ℝ) < (m.factorial : ℝ) * ((r * m).factorial : ℝ))]
      linarith
  have hlintegral_ne_top : (∑' m : ℕ, ∫⁻ u in Ioi (0 : ℝ), ‖term m u‖ₑ) ≠ ⊤ := by
    have heach (m : ℕ) : (∫⁻ u in Ioi (0 : ℝ), ‖term m u‖ₑ) =
        ENNReal.ofReal ((|c| ^ m / (m.factorial : ℝ)) * p⁻¹ * (p ^ r)⁻¹ ^ m) := by
      rw [← ofReal_integral_norm_eq_lintegral_eNorm (hterm_int m), hint_norm m]
    simp_rw [heach]
    have hsum : Summable (fun m : ℕ ↦ (|c| ^ m / (m.factorial : ℝ)) * p⁻¹ * (p ^ r)⁻¹ ^ m) := by
      have h1 := (Real.summable_pow_div_factorial (|c| / p ^ r)).mul_right p⁻¹
      refine h1.congr fun m ↦ ?_
      rw [div_pow, div_eq_mul_inv]
      ring
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m ↦ by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  have hterm_val (m : ℕ) :
      (∫ u in Ioi (0 : ℝ), term m u) =
        (((c / p ^ r) ^ m / (m.factorial : ℝ) * p⁻¹ : ℝ) : ℂ) := by
    have heq : EqOn (term m)
        (fun u : ℝ ↦ expInvCoeff r c m * (((u ^ (r * m) * Real.exp (-p * u) : ℝ) : ℂ))) (Ioi 0) := by
      intro u _
      simp only [term, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_pow]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, integral_complex_ofReal,
        hint_m m, expInvCoeff, ← Complex.ofReal_mul]
    congr 1
    have hfac0 : ((r * m).factorial : ℝ) ≠ 0 := by positivity
    rw [div_pow, pow_succ, pow_mul]
    field_simp [hfac0, hp_pos.ne']
  have hswap : (∫ u in Ioi (0 : ℝ), weighted p (expInvKernel r c) u) =
      ∑' m : ℕ, ∫ u in Ioi (0 : ℝ), term m u := by
    simp_rw [hpt]
    exact integral_tsum (fun m ↦ (hterm_int m).aestronglyMeasurable) hlintegral_ne_top
  rw [hswap]
  simp_rw [hterm_val]
  rw [Complex.real_smul, ← tsum_mul_left]
  have hterm_mul (m : ℕ) :
      (p : ℂ) * (((c / p ^ r) ^ m / (m.factorial : ℝ) * p⁻¹ : ℝ) : ℂ) =
        (((c / p ^ r) ^ m / (m.factorial : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    field_simp [hp_pos.ne']
  simp_rw [hterm_mul]
  rw [← Complex.ofReal_tsum, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

/-! ### 5. Lexicographic Non-Zero-Divisor & Generalized Marked Jacobian -/

/-- On a finite linearly ordered variable set `σ`, any `g : MvPowerSeries σ R`
whose lexicographically minimal nonzero monomial has a unit coefficient is a
non-zero-divisor in `MvPowerSeries σ R` (even if `R` has zero divisors!). -/
theorem lex_nonZeroDivisor_of_unit {σ R : Type*} [LinearOrder σ] [Finite σ] [CommRing R]
    (g : MvPowerSeries σ R) (m₀ : σ →₀ ℕ)
    (hunit : IsUnit (MvPowerSeries.coeff m₀ g))
    (hmin : ∀ m : σ →₀ ℕ, MvPowerSeries.coeff m g ≠ 0 → toLex m₀ ≤ toLex m) :
    g ∈ nonZeroDivisors (MvPowerSeries σ R) := by
  classical
  have : WellFoundedLT (Lex (σ →₀ ℕ)) := Finsupp.Lex.wellFoundedLT_of_finite
  rw [mem_nonZeroDivisors_iff_right]
  intro h hhg
  by_contra hh0
  have hne : Set.Nonempty {n : Lex (σ →₀ ℕ) | MvPowerSeries.coeff (ofLex n) h ≠ 0} := by
    have hex : ∃ n : σ →₀ ℕ, MvPowerSeries.coeff n h ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hh0 (MvPowerSeries.ext hall)
    obtain ⟨n, hn⟩ := hex
    exact ⟨toLex n, hn⟩
  let n₀_lex : Lex (σ →₀ ℕ) := WellFounded.min wellFounded_lt _ hne
  have hn₀_mem : MvPowerSeries.coeff (ofLex n₀_lex) h ≠ 0 :=
    WellFounded.min_mem wellFounded_lt _ hne
  let n₀ : σ →₀ ℕ := ofLex n₀_lex
  have hn₀_min : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n h ≠ 0 → toLex n₀ ≤ toLex n := by
    intro n hn
    by_contra hlt
    exact WellFounded.not_lt_min wellFounded_lt _ (show toLex n ∈ _ from hn) (not_le.mp hlt)
  have hcoeff := congrArg (MvPowerSeries.coeff (n₀ + m₀)) hhg
  rw [map_zero, MvPowerSeries.coeff_mul] at hcoeff
  have honly : ∀ p ∈ Finset.antidiagonal (n₀ + m₀), p ≠ (n₀, m₀) →
      MvPowerSeries.coeff p.1 h * MvPowerSeries.coeff p.2 g = 0 := by
    rintro ⟨a, b⟩ hab hne_ab
    by_contra hnz
    have ha : MvPowerSeries.coeff a h ≠ 0 := left_ne_zero_of_mul hnz
    have hb : MvPowerSeries.coeff b g ≠ 0 := right_ne_zero_of_mul hnz
    have hlea : toLex n₀ ≤ toLex a := hn₀_min a ha
    have hleb : toLex m₀ ≤ toLex b := hmin b hb
    have hsum_eq : toLex a + toLex b = toLex n₀ + toLex m₀ := by
      exact congrArg toLex (Finset.mem_antidiagonal.mp hab)
    have ha_eq : toLex a = toLex n₀ := by
      by_contra hnea
      have hlta : toLex n₀ < toLex a := lt_of_le_of_ne hlea (Ne.symm hnea)
      have hlt_sum : toLex n₀ + toLex m₀ < toLex a + toLex b := add_lt_add_of_lt_of_le hlta hleb
      exact hlt_sum.ne hsum_eq.symm
    have hb_eq : toLex b = toLex m₀ := by
      rw [ha_eq] at hsum_eq
      exact add_left_cancel hsum_eq
    exact hne_ab (Prod.ext (toLex.injective ha_eq) (toLex.injective hb_eq))
  rw [Finset.sum_eq_single (n₀, m₀) honly
      (fun hnot ↦ (hnot (Finset.mem_antidiagonal.mpr rfl)).elim)] at hcoeff
  exact hn₀_mem (hunit.mul_left_eq_zero.mp hcoeff)

private theorem lower_degree_domain {K ι : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (i : ι) (P : MvPolynomial ι K) (h : 0 < P.totalDegree) :
    (pderiv i P).totalDegree < P.totalDegree := by
  classical
  rw [totalDegree_eq]
  apply lt_of_le_of_lt (Finset.sup_le fun m hm ↦ ?_) (Nat.pred_lt h.ne')
  have hn := MvPolynomial.mem_support_iff.mp hm
  rw [coeff_pderiv] at hn
  have hs := le_totalDegree (MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hn))
  change ((m + Finsupp.single i 1).sum fun _ ↦ id) ≤ _ at hs
  rw [← Finsupp.card_toMultiset, Finsupp.toMultiset_add, Finsupp.toMultiset_single] at hs
  simp at hs
  rw [Finsupp.card_toMultiset, Nat.pred_eq_sub_one]
  omega

private theorem all_partials_zero_domain {K ι : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (P : MvPolynomial ι K) (h : ∀ i, pderiv i P = 0) : P = C (P.coeff 0) := by
  classical
  apply MvPolynomial.ext
  intro m
  rw [coeff_C]
  by_cases hm : m = 0
  · subst hm; exact (ite_eq_left rfl).symm
  · rw [ite_eq_right (Ne.symm hm)]
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hm (Finsupp.ext hall)
    have h0 := congrArg (fun f : MvPolynomial ι K ↦ f.coeff (m - Finsupp.single i 1)) (h i)
    simp only [coeff_pderiv, Finsupp.sub_add_single_one_cancel hi] at h0
    have h0' : P.coeff m * (((m - Finsupp.single i 1 : ι →₀ ℕ) i : K) + 1) = 0 := h0
    have hnat : (((m - Finsupp.single i (1 : ℕ)) i : K) + 1) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero ((m - Finsupp.single i (1 : ℕ)) i)
    exact (mul_eq_zero.mp h0').resolve_right hnat

/-- **Generalized Marked Jacobian Theorem**: works over ANY `CharZero` integral
domain `K` (such as `ℂ` or `ℂ[q]`), ANY commutative ring `R` with an injective
`algebraMap K R` (such as `RayGerm`), and ANY Jacobian matrix whose determinant
is a non-zero-divisor in `MvPowerSeries σ R` (not just a unit!). -/
theorem independent_of_marked_jacobian_domain {K R σ ι : Type*}
    [CommRing K] [IsDomain K] [CharZero K] [CommRing R] [Algebra K R]
    (hinj : Function.Injective (algebraMap K R))
    [Fintype ι] [DecidableEq ι] (marks : ι → σ) (f : ι → MvPowerSeries σ R)
    (hnzd : (Matrix.of fun i j ↦ MvPowerSeries.pderiv (marks i) (f j)).det ∈
      nonZeroDivisors (MvPowerSeries σ R)) :
    AlgebraicIndependent K f := by
  classical
  let A : Matrix ι ι (MvPowerSeries σ R) := Matrix.of fun i j ↦ MvPowerSeries.pderiv (marks i) (f j)
  let ev := MvPolynomial.aeval (R := K) f
  have chain (P : MvPolynomial ι K) (i : ι) :
      MvPowerSeries.pderiv (marks i) (ev P) = ∑ j, A i j * ev (pderiv j P) := by
    induction P using MvPolynomial.induction_on with
    | C c =>
      have hC : ev (C c) = MvPowerSeries.C (algebraMap K R c) := by
        simp [ev, MvPowerSeries.algebraMap_apply]
      rw [hC, MvPowerSeries.pderiv_C]
      simp
    | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
    | mul_X p k hp =>
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp, ev, aeval_X, map_add,
        pderiv_X, Pi.single_apply]
      simp only [mul_add, Finset.sum_add_distrib, ← mul_assoc]
      simp [A, mul_comm, mul_left_comm, Finset.mul_sum]
  have stable {P : MvPolynomial ι K} (hp : ev P = 0) (j : ι) : ev (pderiv j P) = 0 := by
    have hz : A *ᵥ (fun k ↦ ev (pderiv k P)) = 0 := by
      funext i; simpa [hp, Matrix.mulVec, dotProduct] using (chain P i).symm
    exact congrFun (A.eq_zero_of_det_mem_nonZeroDivisors_of_mulVec_eq_zero hnzd hz) j
  apply algebraicIndependent_iff.mpr
  intro P
  induction P using (measure fun P : MvPolynomial ι K ↦ P.totalDegree).wf.induction with
  | h P ih =>
    intro hp
    have fromConst (hc : P = C (P.coeff 0)) : P = 0 := by
      have hh : (MvPowerSeries.C (σ := σ) (algebraMap K R (P.coeff 0)) : MvPowerSeries σ R) = 0 := by
        have h1 : ev (C (P.coeff 0)) = 0 := hc ▸ hp
        simpa [ev, MvPowerSeries.algebraMap_apply] using h1
      have h0 : algebraMap K R (P.coeff 0) = 0 := by
        have := congrArg (MvPowerSeries.coeff 0) hh
        simpa using this
      have hc0 : P.coeff 0 = 0 := hinj (h0.trans (map_zero _).symm)
      rw [hc, hc0, C_0]
    rcases Nat.eq_zero_or_pos P.totalDegree with he | he
    · exact fromConst (totalDegree_eq_zero_iff_eq_C.mp he)
    exact fromConst (all_partials_zero_domain P fun i ↦ ih _ (lower_degree_domain i P he) (stable hp i))

end
end CubicTheta.AllD
