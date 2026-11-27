module

public import PakStokes.PhysicalSeries
import all PakStokes.WaveProducts

/-! Polynomial expressions evaluated at ordinary derivatives of the physical
cube residual. A coefficient has action zero and an eventual polynomial bound.
The indices of a product retain the full tuple of original physical modes. -/
public section
namespace CubicTheta.Physical
open Filter
noncomputable section

structure RayCoefficient where
  value : ℝ → ℂ
  budget : ℝ
  loss : ℕ
  nonneg : 0 ≤ budget
  bound : ∀ᶠ x : ℝ in atTop, ‖value x‖ ≤ budget*x^loss

def RayCoefficient.expansion (a : RayCoefficient) : WaveExpansion Unit where
  rate := fun _ ↦ 0
  amplitude := fun _ ↦ a.value
  budget := fun _ ↦ a.budget
  loss := a.loss
  re_nonneg := by simp
  budget_nonneg := fun _ ↦ a.nonneg
  summable_budget := hasSum_fintype _ |>.summable
  bound := by simpa using a.bound

inductive JetExpression where
  | coeff (a : RayCoefficient)
  | jet (j : ℕ)
  | add (left right : JetExpression)
  | mul (left right : JetExpression)

namespace JetExpression

def Index : JetExpression → Type
  | .coeff _ => Unit
  | .jet _ => ℕ+ ⊕ ℕ+
  | .add a b => a.Index ⊕ b.Index
  | .mul a b => a.Index × b.Index

def expansion : (e : JetExpression) → WaveExpansion e.Index
  | .coeff a => a.expansion
  | .jet j => physicalJet j
  | .add a b => a.expansion.add b.expansion
  | .mul a b => a.expansion.mul b.expansion

def eval : JetExpression → ℝ → ℂ
  | .coeff a => a.value
  | .jet j => iteratedDeriv j cubeResidual
  | .add a b => fun x ↦ a.eval x + b.eval x
  | .mul a b => fun x ↦ a.eval x * b.eval x

theorem expansion_value (e : JetExpression) : e.expansion.value =ᶠ[atTop] e.eval := by
  induction e with
  | coeff a =>
    apply Filter.Eventually.of_forall
    intro x
    change a.expansion.value x = a.value x
    simp [RayCoefficient.expansion,WaveExpansion.value,WaveExpansion.term]
  | jet j => exact (cubeResidual_derivatives j).symm
  | add a b ha hb =>
    filter_upwards [a.expansion.value_add b.expansion,ha,hb] with x he h₁ h₂
    exact he.trans (congrArg₂ (·+·) h₁ h₂)
  | mul a b ha hb =>
    filter_upwards [a.expansion.value_mul b.expansion,ha,hb] with x he h₁ h₂
    exact he.trans (congrArg₂ (·*·) h₁ h₂)

end JetExpression
end
end CubicTheta.Physical
