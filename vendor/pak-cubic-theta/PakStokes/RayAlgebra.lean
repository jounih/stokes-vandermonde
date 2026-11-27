module

public import PakStokes.RealRayExtension
public import DirectionalLaplace

/-! Exact arithmetic of Laplace amplitudes on the physical ray. Integer shifts
are aligned by primitive convolution. Hence cancellation within a parity
takes place inside a single analytic kernel. -/
public section
namespace CubicTheta
open Set Filter MeasureTheory
open scoped Topology
noncomputable section

def RayDensity (F : ℝ → ℂ) := AnalyticOnNhd ℝ F (Ici 0) ∧ ExpType F

namespace RayDensity
theorem const (c : ℂ) : RayDensity (fun _ ↦ c) :=
  ⟨analyticOnNhd_const,‖c‖,0,norm_nonneg _,le_rfl,by simp⟩

theorem add {F G} (hf : RayDensity F) (hg : RayDensity G) : RayDensity (fun u ↦ F u + G u) :=
  ⟨hf.1.add hg.1,hf.2.add hg.2⟩

theorem conv {F G} (hf : RayDensity F) (hg : RayDensity G) : RayDensity (borelProduct F G) :=
  ⟨positive_convolution_analytic hf.1 hg.1,hf.2.convolution hg.2⟩

theorem integrable {F} (hf : RayDensity F) :
    ∀ᶠ x in atTop, IntegrableOn (weighted x F) (Ioi 0) := by
  obtain ⟨C,D,_,_,h⟩ := hf.2
  exact (eventually_gt_atTop D).mono fun _ hx ↦ weighted_integrable
    (hf.1.continuousOn.mono Ioi_subset_Ici_self) (fun u hu ↦ h u hu.le) hx

theorem conjugate {F} (hf : RayDensity F) : RayDensity (fun u ↦ star (F u)) := by
  obtain ⟨C,D,hC,hD,h⟩ := hf.2
  exact ⟨fun x hx ↦ (Complex.conjCLE.toContinuousLinearMap.analyticAt _).comp (hf.1 x hx),
    C,D,hC,hD,by simpa using h⟩
end RayDensity

private theorem sum_const (c : ℂ) (x : ℝ) : raySum (fun _ ↦ c) x = c := by
  simp only [raySum,integral_smul_const,integral_exp_neg_Ioi_zero,one_smul]

/-- A normalized Laplace representation with a specified outside power. -/
def AtPower (s : ℝ) (f : ℝ → ℂ) := ∃ F, RayDensity F ∧
  ∀ᶠ x : ℝ in atTop, f x = x^s • raySum F x

namespace AtPower
theorem congr {s f g} (h : AtPower s f) (eqn : f =ᶠ[atTop] g) : AtPower s g := by
  obtain ⟨F,hF,he⟩ := h
  exact ⟨F,hF,eqn.symm.trans he⟩

theorem add {s f g} (h : AtPower s f) (k : AtPower s g) : AtPower s (fun x ↦ f x+g x) := by
  obtain ⟨F,hF,he⟩ := h
  obtain ⟨G,hG,ge⟩ := k
  refine ⟨_,hF.add hG,?_⟩
  filter_upwards [he,ge,hF.integrable,hG.integrable,eventually_gt_atTop (0:ℝ)] with x hf hg fi gi hx
  rw [hf,hg,raySum_eq_weighted _ hx,raySum_eq_weighted _ hx,raySum_eq_weighted _ hx]
  rw [show weighted x (fun u ↦ F u + G u) = (fun u ↦ weighted x F u + weighted x G u) by funext u; simp only [weighted,smul_add],integral_add fi gi,smul_add,smul_add]

theorem mul {s t f g} (h : AtPower s f) (k : AtPower t g) : AtPower (s+t+1) (fun x ↦ f x*g x) := by
  obtain ⟨F,hF,he⟩ := h
  obtain ⟨G,hG,ge⟩ := k
  refine ⟨_,hF.conv hG,?_⟩
  filter_upwards [he,ge,hF.integrable,hG.integrable,eventually_gt_atTop (0:ℝ)] with x hf hg fi gi hx
  rw [hf,hg,smul_mul_assoc,mul_smul_comm,raySum_product _ _ hx fi gi,
    smul_smul,smul_smul,Real.rpow_add hx,Real.rpow_add hx,Real.rpow_one]

theorem const (c : ℂ) : AtPower 0 (fun _ ↦ c) :=
  ⟨_,RayDensity.const c,.of_forall fun x ↦ by simp [sum_const]⟩

theorem raise {s f} (h : AtPower s f) (n : ℕ) : AtPower (s+n) f := by
  induction n with
  | zero => simpa using h
  | succ n ih => simpa [Nat.cast_add,add_assoc] using (ih.mul (const 1))

theorem shift {s f} (h : AtPower s f) (t : ℝ) : AtPower (t+s) (fun x : ℝ ↦ x^t • f x) := by
  obtain ⟨F,hF,he⟩ := h
  exact ⟨F,hF,by filter_upwards [he,eventually_gt_atTop (0:ℝ)] with x he hx; rw [he,smul_smul,Real.rpow_add hx]⟩

theorem conjugate {s f} (h : AtPower s f) : AtPower s (fun x ↦ star (f x)) := by
  obtain ⟨F,hF,he⟩ := h
  refine ⟨_,hF.conjugate,?_⟩
  filter_upwards [he] with x hx
  rw [hx,star_smul]; simp only [star_trivial]
  congr 1
  change (starRingEnd ℂ) (∫ u in Ioi (0:ℝ), Real.exp (-u) • F (u/x)) = _
  rw [← integral_conj]; unfold raySum; congr 1; funext u; exact star_smul _ _
end AtPower

/-- A coset of the integer powers. -/
def PowerClass (t : ℝ) (f : ℝ → ℂ) := ∃ k : ℤ, AtPower (t+k) f

namespace PowerClass
theorem congr {s f g} (h : PowerClass s f) (eqn : f =ᶠ[atTop] g) : PowerClass s g := by
  obtain ⟨k,h⟩ := h; exact ⟨k,h.congr eqn⟩

theorem add {s f g} (h : PowerClass s f) (j : PowerClass s g) : PowerClass s (fun x ↦ f x+g x) := by
  obtain ⟨k,h⟩ := h
  obtain ⟨l,j⟩ := j
  let m := max k l
  have lift' {a : ℤ} {f} (ha : a≤m) (h : AtPower (s+a) f) : AtPower (s+m) f := by
    have eqn : a + ((m-a).toNat:ℤ) = m := by omega
    have eqr : (s+(a:ℝ))+((m-a).toNat:ℝ) = s+(m:ℝ) := by
      rw [add_assoc]; congr 1; exact_mod_cast eqn
    exact eqr ▸ h.raise (m-a).toNat
  exact ⟨m,(lift' (le_max_left ..) h).add (lift' (le_max_right ..) j)⟩

theorem mul {s t f g} (h : PowerClass s f) (j : PowerClass t g) :
    PowerClass (s+t) (fun x ↦ f x*g x) := by
  obtain ⟨k,h⟩ := h; obtain ⟨l,j⟩ := j
  refine ⟨k+l+1,?_⟩; convert h.mul j using 1; push_cast; ring

theorem reindex {s t f} (h : PowerClass s f) (k : ℤ) (eqn : s=t+k) : PowerClass t f := by
  obtain ⟨l,h⟩ := h; refine ⟨k+l,?_⟩; simpa [eqn,add_assoc] using h

theorem const (c : ℂ) : PowerClass 0 (fun _ ↦ c) := ⟨0,by simpa using AtPower.const c⟩

theorem zero (s : ℝ) : PowerClass s (fun _ ↦ 0) :=
  ⟨0,_,RayDensity.const 0,.of_forall fun x ↦ by simp [sum_const]⟩

theorem conjugate {s f} (h : PowerClass s f) : PowerClass s (fun x ↦ star (f x)) := by
  obtain ⟨k,h⟩ := h; exact ⟨k,h.conjugate⟩
end PowerClass
end
end CubicTheta
