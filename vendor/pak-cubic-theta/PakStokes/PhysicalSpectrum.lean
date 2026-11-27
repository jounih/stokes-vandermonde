module

public import PakStokes.PhysicalExpression
public import Mathlib.Order.OrderIsoNat
public import Mathlib.Data.Set.Card
import all PakStokes.PhysicalExpression
import all PakStokes.PhysicalSeries
import all PakStokes.CubicKummerJets
import all PakStokes.LaplaceWaveJets
import all PakStokes.WaveProducts

/-! Enumeration of the actual complex actions of a polynomial in physical jets. -/
public section
namespace CubicTheta.Physical
open Set LaplaceWave
noncomputable section

private theorem finiteModes (R : ℝ) : {n : ℕ+ | (cubicRate action n).re ≤ R}.Finite := by
  obtain ⟨N,hN⟩ := exists_nat_gt (R/action.re)
  refine ((Set.finite_le_nat N).preimage PNat.coe_injective.injOn).subset ?_
  intro n hn
  change (n:ℕ) ≤ N
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast n.property
  have powle : (n:ℝ) ≤ (n:ℝ)^(3/2:ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1:ℝ)≤3/2)
  change (cubicRate action n).re ≤ R at hn
  simp [cubicRate] at hn
  exact_mod_cast ((le_div_iff₀ action_pos).mpr ((mul_le_mul_of_nonneg_right powle action_pos.le).trans hn)).trans hN.le

private theorem finiteSumIndices {α β : Type*} (f : α → ℝ) (g : β → ℝ) (R : ℝ)
    (hf : {a | f a ≤ R}.Finite) (hg : {b | g b ≤ R}.Finite) :
    {i : α ⊕ β | Sum.elim f g i ≤ R}.Finite := by
  refine ((hf.image Sum.inl).union (hg.image Sum.inr)).subset ?_
  rintro (i|j) h
  · exact Or.inl ⟨i,h,rfl⟩
  · exact Or.inr ⟨j,h,rfl⟩

/-- Each bounded real-action window contains finitely many original tuples,
including their multiplicity before any grouping. -/
theorem JetExpression.finite_window (e : JetExpression) (R : ℝ) :
    {i | (e.expansion.rate i).re ≤ R}.Finite := by
  induction e with
  | coeff a => change Set.Finite {i : Unit | (0:ℝ) ≤ R}; exact Set.toFinite _
  | jet j =>
    apply (finiteSumIndices _ _ R (finiteModes R) (finiteModes R)).subset
    rintro (i|j) h <;> exact h
  | add a b ha hb =>
    apply (finiteSumIndices _ _ R ha hb).subset
    rintro (i|j) h <;> exact h
  | mul a b ha hb =>
    refine (ha.prod hb).subset ?_
    rintro ⟨i,j⟩ h
    change (a.expansion.rate i).re + (b.expansion.rate j).re ≤ R at h
    exact ⟨(le_add_of_nonneg_right (b.expansion.re_nonneg j)).trans h,
      (le_add_of_nonneg_left (a.expansion.re_nonneg i)).trans h⟩

/-- Pad a possibly finite spectrum with the nonnegative integers. Empty
frequency clusters at these auxiliary rates have no terms. -/
private def padded (e : JetExpression) :=
  range (fun i ↦ (e.expansion.rate i).re) ∪ range (Nat.cast : ℕ → ℝ)

private theorem padded_finite (e : JetExpression) (R : ℝ) :
    ((padded e) ∩ Iic R).Finite := by
  obtain ⟨N,hN⟩ := exists_nat_gt R
  refine (((e.finite_window R).image (fun i ↦ (e.expansion.rate i).re)).union
    ((Set.finite_le_nat N).image (Nat.cast : ℕ → ℝ))).subset ?_
  rintro x ⟨(⟨i,rfl⟩|⟨n,rfl⟩),hx⟩
  · exact Or.inl ⟨i,hx,rfl⟩
  · exact Or.inr ⟨n,by exact_mod_cast (show (n:ℝ) ≤ N from hx.trans hN.le),rfl⟩

private def enumerate (e : JetExpression) : ℕ ≃o padded e := by
  classical
  let S := padded e
  let rank (x : S) := (S ∩ Iic (x:ℝ)).ncard
  have inc : StrictMono rank := by
    intro x y h
    apply Set.ncard_lt_ncard _ (padded_finite e _)
    exact Set.ssubset_iff_subset_ne.mpr ⟨inter_subset_inter_right _ (Iic_subset_Iic.mpr h.le),
      fun eqn ↦ (not_le.mpr h) ((eqn ▸ (show (y:ℝ) ∈ S ∩ Iic (y:ℝ) from ⟨y.property,le_rfl⟩) : (y:ℝ) ∈ S ∩ Iic (x:ℝ))).2⟩
  let iso : S ≃o range rank := inc.orderIso rank
  haveI : Infinite S := Infinite.of_injective
    (fun n : ℕ ↦ (⟨n, Or.inr ⟨n,rfl⟩⟩ : S)) (fun _ _ h ↦ Nat.cast_injective (congrArg Subtype.val h))
  letI : Infinite (range rank) := Infinite.of_injective _ iso.injective
  exact (Nat.Subtype.orderIsoOfNat _).trans iso.symm

namespace JetExpression

def decay (e : JetExpression) (n : ℕ) : ℝ := enumerate e n

theorem decay_strictMono (e : JetExpression) : StrictMono e.decay :=
  fun _ _ h ↦ (enumerate e).strictMono h

def clusterIndex (e : JetExpression) (i : e.Index) : ℕ :=
  (enumerate e).symm ⟨(e.expansion.rate i).re,Or.inl ⟨i,rfl⟩⟩

theorem decay_clusterIndex (e : JetExpression) (i : e.Index) :
    e.decay (e.clusterIndex i) = (e.expansion.rate i).re := by
  simp [decay,clusterIndex]

abbrev Frequency (e : JetExpression) (n : ℕ) :=
  {y : ℝ // ∃ i : e.Index, (e.expansion.rate i).re = e.decay n ∧ -(e.expansion.rate i).im = y}

noncomputable instance (e : JetExpression) (n : ℕ) : Fintype (e.Frequency n) := by
  change Fintype (↑({y : ℝ | ∃ i : e.Index, (e.expansion.rate i).re = e.decay n ∧ -(e.expansion.rate i).im = y} : Set ℝ))
  apply Set.Finite.fintype
  refine ((e.finite_window (e.decay n)).image (fun i ↦ -(e.expansion.rate i).im)).subset ?_
  rintro y ⟨i,hi,rfl⟩
  exact ⟨i,hi.le,rfl⟩

def group (e : JetExpression) (i : e.Index) : Σ n, e.Frequency n :=
  ⟨e.clusterIndex i,⟨-(e.expansion.rate i).im,i,(e.decay_clusterIndex i).symm,rfl⟩⟩

theorem group_rate (e : JetExpression) (i : e.Index) :
    e.expansion.rate i = ⟨e.decay (e.group i).1,-((e.group i).2:ℝ)⟩ := by
  apply Complex.ext
  · exact (e.decay_clusterIndex i).symm
  · simp [group]

end JetExpression
end
end CubicTheta.Physical
