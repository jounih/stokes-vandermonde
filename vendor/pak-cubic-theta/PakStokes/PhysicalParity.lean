module

public import PakStokes.RayAlgebra
public import PakStokes.RegularCube
import all PakStokes.RayAlgebra
import all PakStokes.LaplaceWaveJets
import all PakStokes.CubicKummerJets
import all PakStokes.PhysicalSeries
import all PakStokes.PhysicalExpression
import all PakStokes.RegularCube
import all PakStokes.WaveProducts

/-! The two parity classes of the differentiated physical cube series,
including every finite full-action fiber of a polynomial expression. -/
public section
namespace CubicTheta
open Set Filter MeasureTheory LaplaceWave
open scoped Topology
noncomputable section

def TwoParities (f : ℝ → ℂ) := ∃ a b : ℝ → ℂ, PowerClass 0 a ∧ PowerClass (1/2) b ∧
    f =ᶠ[atTop] fun x ↦ a x+b x

namespace TwoParities
theorem of_integer {f} (h : PowerClass 0 f) : TwoParities f :=
  ⟨_,_,h,PowerClass.zero _,by simp⟩
theorem of_half {f} (h : PowerClass (1/2) f) : TwoParities f :=
  ⟨_,_,PowerClass.zero _,h,by simp⟩
theorem add {f g} (hf : TwoParities f) (hg : TwoParities g) : TwoParities (fun x ↦ f x + g x) := by
  obtain ⟨a,b,ha,hb,he⟩ := hf; obtain ⟨c,d,hc,hd,hg⟩ := hg
  refine ⟨_,_,ha.add hc,hb.add hd,?_⟩
  filter_upwards [he,hg] with x he hg; rw [he,hg]; ring

theorem mul {f g} (hf : TwoParities f) (hg : TwoParities g) : TwoParities (fun x ↦ f x * g x) := by
  obtain ⟨a,b,ha,hb,he⟩ := hf; obtain ⟨c,d,hc,hd,hg⟩ := hg
  refine ⟨_,_,((ha.mul hc).reindex 0 (by norm_num)).add ((hb.mul hd).reindex 1 (by norm_num)),
    ((ha.mul hd).reindex 0 (by norm_num)).add ((hb.mul hc).reindex 0 (by norm_num)),?_⟩
  filter_upwards [he,hg] with x he hg; rw [he,hg]; ring

theorem finsetSum {ι} (S : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i ∈ S, TwoParities (f i)) :
    TwoParities (fun x ↦ ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using of_integer (PowerClass.const 0)
  | insert i S hi ih => simpa [Finset.sum_insert hi] using
      (hf i (by simp)).add (ih (fun j hj ↦ hf j (by simp [hj])))

/-- Different integer shifts of the two parities give disjoint Watson orders. -/
theorem kernels {f} (hf : TwoParities f) : ∃ F G s t, RayDensity F ∧ RayDensity G ∧
    (∀ n m : ℕ, (n:ℝ)-s ≠ (m:ℝ)-t) ∧
    ∀ᶠ x : ℝ in atTop, f x = x^s • raySum F x + x^t • raySum G x := by
  obtain ⟨a,b,⟨k,F,hF,ha⟩,⟨l,G,hG,hb⟩,he⟩ := hf
  refine ⟨F,G,0+k,1/2+l,hF,hG,?_,?_⟩
  · intro n m eqn
    have hh : 2*((n:ℤ)-k) = 2*((m:ℤ)-l)-1 := by
      exact_mod_cast (show (2:ℝ)*(n-k) = 2*(m-l)-1 by linarith)
    omega
  filter_upwards [ha,hb,he] with x ha hb he; rw [he,ha,hb]
end TwoParities

private theorem class_scale {s f} (c : ℂ) (h : PowerClass s f) :
    PowerClass s (fun x ↦ c*f x) := by simpa using (PowerClass.const c).mul h

private theorem moment_density {F : ℝ → ℂ} (hF : RayDensity F) (m : ℕ) :
    RayDensity (fun u : ℝ ↦ u^m • F u) := by
  refine ⟨fun x hx ↦ (analyticAt_id.pow m).smul (hF.1 x hx),?_⟩
  induction m with
  | zero => simpa using hF.2
  | succ m ih =>
    simpa only [pow_succ',mul_smul,Complex.real_smul] using ih.times_u

private theorem wave_class {F : ℝ → ℂ} (hF : RayDensity F) (c : ℂ) (j : ℕ) (d : ℝ) (m : ℕ) :
    PowerClass d (amplitude F c j d m) := by
  induction j generalizing d m with
  | zero =>
    refine ⟨-1,_,moment_density hF m,?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
    rw [raySum_eq_weighted _ hx,smul_smul]
    have scale : x^(d+((-1:ℤ):ℝ))*x = x^d := by
      calc _ = x^(d-1)*x^(1:ℝ) := by simp [sub_eq_add_neg]
           _ = _ := by rw [← Real.rpow_add hx]; norm_num
    rw [scale]; rfl
  | succ j ih =>
    have a := class_scale (-c) (ih d m)
    have b := class_scale (d:ℂ) ((ih (d-1) m).reindex (t := d) (-1) (by norm_num [sub_eq_add_neg]))
    have e := class_scale (-1) (ih d (m+1))
    simpa [amplitude,sub_eq_add_neg] using (a.add b).add e

namespace Physical
private theorem jet_half (j : ℕ) (i : ℕ+ ⊕ ℕ+) : PowerClass (1/2) ((physicalJet j).amplitude i) := by
  have h (n : ℕ+) := by
    let c := cubicRate action n
    have hc : 0 < c.re := rate_pos action_pos n
    have hd : RayDensity (cubicBetaKernel c) := ⟨cubicBeta_analytic hc,1,0,by norm_num,le_rfl,
      fun u hu ↦ by simpa using cubicBeta_bound hc hu⟩
    exact class_scale coefficient (class_scale (modeFactor n)
      ((wave_class hd c j (3/2) 0).reindex 1 (show (3/2:ℝ)=1/2+(1:ℤ) by norm_num)))
  cases i with
  | inl n => exact h n
  | inr n => exact (h n).conjugate

private theorem background_integer (j : ℕ) : PowerClass 0 (backgroundCoefficient j).value := by
  open BackgroundInverse in
  have hd (k : ℕ) : RayDensity (momentKernel k) := by
    obtain ⟨C,h⟩ := momentKernel_growth k
    refine ⟨momentKernel_analytic k,max C ‖momentKernel k 0‖,1,(norm_nonneg _).trans (le_max_right ..),
      zero_le_one,fun u hu ↦ ?_⟩
    rcases hu.eq_or_lt with rfl|hu
    · simp
    · simpa using (h u hu).trans (mul_le_mul_of_nonneg_right (le_max_left C _) (Real.exp_pos u).le)
  open BackgroundInverse in
  have hzero (k : ℕ) : PowerClass 0 (fun p : ℝ ↦ (p:ℂ)*rawMoment k p) :=
    ⟨0,_,hd k,by filter_upwards [eventually_gt_atTop (0:ℝ)] with p hp; simp [rawMoment_normalized k hp]⟩
  open BackgroundInverse in
  have hm (k : ℕ) : PowerClass 0 (rawMoment k) := by
    refine ⟨-1,_,hd k,?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with p hp
    rw [← rawMoment_normalized k hp]; simp only [Int.cast_neg,Int.cast_one,zero_add,Real.rpow_neg_one,Complex.real_smul,Complex.ofReal_inv]
    field_simp [hp.ne']
  open BackgroundInverse in
  cases j with
  | zero => exact (hzero 0).congr ((eventually_gt_atTop (0:ℝ)).mono fun p hp ↦ (background_raw hp).symm)
  | succ j => exact ((hzero (j+1)).add (class_scale _ (hm j))).congr (background_derivatives j).symm

namespace JetExpression
/-- Only coefficient leaves require a hypothesis. Each constant satisfies it. -/
def Admissible : JetExpression → Prop
  | .coeff a => TwoParities a.value
  | .jet _ => True
  | .add a b | .mul a b => Admissible a ∧ Admissible b

theorem admissible_background {e : JetExpression} (h : e.Admissible) : e.withBackground.Admissible := by
  induction e with
  | coeff => exact h
  | jet j => exact ⟨trivial,TwoParities.of_integer (background_integer j)⟩
  | add a b ha hb | mul a b ha hb => exact ⟨ha h.1,hb h.2⟩

theorem term_parities {e : JetExpression} (h : e.Admissible) (i : e.Index) :
    TwoParities (e.expansion.amplitude i) := by
  induction e with
  | coeff => exact h
  | jet j => exact TwoParities.of_half (jet_half j i)
  | add a b ha hb => cases i with
    | inl i => exact ha h.1 i
    | inr i => exact hb h.2 i
  | mul a b ha hb => exact (ha h.1 i.1).mul (hb h.2 i.2)

theorem group_parities {e : JetExpression} (h : e.Admissible) (k : Σ n, e.Frequency n) :
    TwoParities (e.expansion.groupAmplitude e.group k) := by
  classical
  have small : (e.group ⁻¹' {k}).Finite := (e.finite_window (e.decay k.1)).subset (by
    intro i hi; have he : e.group i = k := hi
    change (e.expansion.rate i).re ≤ _; rw [e.group_rate i,he])
  let _ := small.fintype
  unfold WaveExpansion.groupAmplitude
  simpa [WaveExpansion.groupAmplitude,tsum_fintype] using TwoParities.finsetSum Finset.univ
    (fun i : e.group ⁻¹' {k} ↦ e.expansion.amplitude i) (fun i _ ↦ term_parities h i)
end JetExpression
end Physical
end
end CubicTheta
