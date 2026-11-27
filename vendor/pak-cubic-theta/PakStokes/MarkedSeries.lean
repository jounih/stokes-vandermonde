module

public import PakStokes.ActionCoordinates
public import PakStokes.PhysicalSpectrum
public import Mathlib.RingTheory.MvPowerSeries.Basic
import all PakStokes.ActionCoordinates
import all PakStokes.PhysicalSpectrum
import all PakStokes.PhysicalSeries
import all PakStokes.PhysicalExpression
import all PakStokes.CubicKummerJets
import all PakStokes.LaplaceWaveJets
import all PakStokes.WaveProducts

/-! Mark every squarefree direction and each of its two signs. Coefficients
are germs on the physical ray. Each monomial coefficient is a finite sum. -/
public section
namespace CubicTheta.Physical
open Filter Set LaplaceWave
noncomputable section
abbrev Mark := Core ⊕ Core
abbrev Key := Mark →₀ ℕ
abbrev RayGerm := Germ (atTop : Filter ℝ) ℂ
abbrev Marked := MvPowerSeries Mark RayGerm

def keyRate (k : Key) : ℂ := fullRate
  (k.comapDomain Sum.inl Sum.inl_injective.injOn,k.comapDomain Sum.inr Sum.inr_injective.injOn)

theorem keyRate_inj : Function.Injective keyRate := by
  intro a b he
  have h := fullRate_injective he
  have := congrArg (fun p : ActionKey × ActionKey ↦ p.1.sumElim p.2) h
  simpa [Finsupp.comapDomain_sumElim_comapDomain] using this

theorem keyRate_add (a b : Key) : keyRate (a+b) = keyRate a + keyRate b := by
  unfold keyRate; rw [← fullRate_add]
  simp [Finsupp.comapDomain_add_of_injective,Sum.inl_injective,Sum.inr_injective]

namespace JetExpression
def key : (e : JetExpression) → e.Index → Key
  | .coeff _,_ => 0
  | .jet _,.inl n => (modeKey n).sumElim 0
  | .jet _,.inr n => (0 : ActionKey).sumElim (modeKey n)
  | .add a b,i => Sum.elim a.key b.key i
  | .mul a b,i => a.key i.1+b.key i.2

theorem rate_eq_key (e : JetExpression) (i : e.Index) : e.expansion.rate i = keyRate (e.key i) := by
  induction e with
  | coeff => simp [key,keyRate,fullRate,expansion,RayCoefficient.expansion]
  | jet j =>
    cases i with
    | inl n => simpa [key,keyRate,fullRate,Finsupp.comapDomain_inl_sumElim,Finsupp.comapDomain_inr_sumElim,
        expansion,physicalJet,WaveExpansion.add,WaveExpansion.scale,kummerJet,cubicJet] using rate_key n
    | inr n =>
      simpa [key,keyRate,fullRate,Finsupp.comapDomain_inl_sumElim,Finsupp.comapDomain_inr_sumElim,
        expansion,physicalJet,WaveExpansion.add,WaveExpansion.scale,WaveExpansion.conjugate,kummerJet,cubicJet,
        mul_comm] using congrArg star (rate_key n)
  | add a b ha hb => cases i with
    | inl i => exact ha i
    | inr i => exact hb i
  | mul a b ha hb => exact (congrArg₂ (·+·) (ha i.1) (hb i.2)).trans (keyRate_add ..).symm

private theorem sameGroup (e : JetExpression) (i j : e.Index) : e.group i = e.group j ↔ e.key i = e.key j := by
  constructor
  · intro h; apply keyRate_inj; rw [← e.rate_eq_key,← e.rate_eq_key,e.group_rate i,e.group_rate j,h]
  intro h
  have rates := (e.rate_eq_key i).trans ((congrArg keyRate h).trans (e.rate_eq_key j).symm)
  have idx : e.clusterIndex i = e.clusterIndex j := e.decay_strictMono.injective
    (by rw [e.decay_clusterIndex,e.decay_clusterIndex,rates])
  apply Sigma.ext idx
  exact Subtype.heq_iff_coe_eq (by change ∀ x, (∃ u, (e.expansion.rate u).re=e.decay (e.clusterIndex i) ∧ -(e.expansion.rate u).im=x) ↔ _; intro; rw [idx]; rfl) |>.mpr (congrArg (fun c : ℂ ↦ -c.im) rates)

private abbrev Fiber (e : JetExpression) (k : Key) := {i : e.Index // e.key i = k}
private noncomputable instance fiberType (e : JetExpression) (k : Key) : Fintype (Fiber e k) := by
  apply Set.Finite.fintype (s := {i : e.Index | e.key i=k})
  apply (e.finite_window (keyRate k).re).subset
  intro i hi; change (e.expansion.rate i).re ≤ _; rw [e.rate_eq_key i,show e.key i=k from hi]

def marked (e : JetExpression) : Marked := fun k ↦
  ∑ i : Fiber e k, Germ.ofFun (e.expansion.amplitude i)

theorem marked_zero (e : JetExpression)
    (h : ∀ n (j : e.Frequency n), ∀ᶠ x : ℝ in atTop, e.expansion.groupAmplitude e.group ⟨n,j⟩ x=0) :
    e.marked = 0 := by
  classical
  apply MvPowerSeries.ext; intro k
  change (∑ i : Fiber e k, Germ.ofFun (e.expansion.amplitude i)) = 0
  by_cases ex : Nonempty (Fiber e k)
  · obtain ⟨i⟩ := ex
    have sets : {j : e.Index | e.key j=k} = e.group ⁻¹' {e.group i.val} := by
      ext j; exact (i.property ▸ e.sameGroup j i.val).symm
    have hz := h (e.group i.val).1 (e.group i.val).2
    change ∀ᶠ x : ℝ in atTop, (∑' j : e.group ⁻¹' {e.group i.val}, e.expansion.amplitude j x) = 0 at hz
    rw [← sets] at hz
    change ∀ᶠ x : ℝ in atTop, (∑' j : Fiber e k, e.expansion.amplitude j x)=0 at hz
    simp only [tsum_fintype] at hz
    let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
    change (∑ j : Fiber e k, H (e.expansion.amplitude j)) = 0
    rw [← map_sum]; apply Germ.coe_eq.mpr
    filter_upwards [hz] with x hx; simpa only [Finset.sum_apply] using hx
  · let _ : IsEmpty (Fiber e k) := not_nonempty_iff.mp ex; simp

private def splitSum (a b : JetExpression) (k : Key) :
    Fiber (.add a b) k ≃ Fiber a k ⊕ Fiber b k where
  toFun i := match i with
    | ⟨.inl j,h⟩ => .inl ⟨j,h⟩
    | ⟨.inr j,h⟩ => .inr ⟨j,h⟩
  invFun i := match i with
    | .inl j => ⟨.inl j.val,j.property⟩
    | .inr j => ⟨.inr j.val,j.property⟩
  left_inv := by rintro ⟨i,hi⟩; cases i <;> rfl
  right_inv := by rintro (i|i) <;> rfl

theorem marked_add (a b : JetExpression) : (a.add b).marked = a.marked+b.marked := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [map_add]
  change (∑ i : Fiber (.add a b) k, _) = MvPowerSeries.coeff k a.marked + MvPowerSeries.coeff k b.marked
  let f : Fiber a k ⊕ Fiber b k → RayGerm := Sum.elim (fun i : Fiber a k ↦ Germ.ofFun (a.expansion.amplitude i))
    (fun i : Fiber b k ↦ Germ.ofFun (b.expansion.amplitude i))
  rw [Fintype.sum_equiv (splitSum a b k) _ f (by rintro ⟨(i|i),h⟩ <;> rfl),Fintype.sum_sum_type]
  rfl

private def splitProduct (a b : JetExpression) (k : Key) [DecidableEq Mark] :
    Fiber (.mul a b) k ≃ (Σ d : ↥(Finset.antidiagonal k), Fiber a d.val.1 × Fiber b d.val.2) where
  toFun i := ⟨⟨(a.key i.val.1,b.key i.val.2),Finset.mem_antidiagonal.mpr i.property⟩,
    ⟨i.val.1,rfl⟩,⟨i.val.2,rfl⟩⟩
  invFun := fun ⟨d,i,j⟩ ↦ ⟨(i.val,j.val),by
    change a.key i.val+b.key j.val=k
    rw [i.property,j.property]; exact Finset.mem_antidiagonal.mp d.property⟩
  left_inv := fun _ ↦ rfl
  right_inv := by
    rintro ⟨⟨⟨s,t⟩,hd⟩,⟨i,hi⟩,⟨j,hj⟩⟩
    change a.key i = s at hi; change b.key j=t at hj; subst s; subst t; rfl

theorem marked_mul (a b : JetExpression) : (a.mul b).marked = a.marked*b.marked := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [MvPowerSeries.coeff_mul,← Finset.sum_coe_sort]
  let f (i : Σ d : ↥(Finset.antidiagonal k), Fiber a d.val.1 × Fiber b d.val.2) :=
    (Germ.ofFun (a.expansion.amplitude i.2.1) : RayGerm) * Germ.ofFun (b.expansion.amplitude i.2.2)
  change (∑ i : Fiber (.mul a b) k, _) = _
  rw [Fintype.sum_equiv (splitProduct a b k) _ f (by intro i; rfl),Fintype.sum_sigma]
  apply Finset.sum_congr rfl; intro d _
  rw [Fintype.sum_prod_type]
  simp [f,marked,MvPowerSeries.coeff_apply,Finset.sum_mul,Finset.mul_sum]; exact Finset.sum_comm

theorem marked_coeff (a : RayCoefficient) :
    (JetExpression.coeff a).marked = MvPowerSeries.C (Germ.ofFun a.value) := by
  classical
  apply MvPowerSeries.ext; intro k
  rw [MvPowerSeries.coeff_C]
  by_cases hk : k=0
  · subst k; let E : Fiber (.coeff a) 0 ≃ Unit := ⟨fun i ↦ i.val,fun i ↦ ⟨i,rfl⟩,fun _ ↦ rfl,fun _ ↦ rfl⟩
    change (∑ i : Fiber (.coeff a) 0, _) = _
    rw [Fintype.sum_equiv E _ (fun _ ↦ (Germ.ofFun a.value : RayGerm)) (by intro _; rfl)]; simp
  · let _ : IsEmpty (Fiber (.coeff a) k) := ⟨fun i ↦ hk i.property.symm⟩
    simp [marked,MvPowerSeries.coeff_apply,hk]
end JetExpression
end
end CubicTheta.Physical
