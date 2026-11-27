module

public import CubicActions
public import PakStokes.PhysicalSeries
public import Mathlib.Data.Nat.Squarefree
import all CubicActions
import all PakStokes.PhysicalSeries
import all PakStokes.PhysicalKummer
import all PakStokes.LaplaceWaveJets

/-! Exact arithmetic of full complex physical actions. Each sign has its own
nonnegative integral coordinates on the squarefree indices. -/
public section
namespace CubicTheta.Physical
open Complex LaplaceWave
noncomputable section

abbrev Core := {d : ℕ // Squarefree d}
abbrev ActionKey := Core →₀ ℕ

private theorem factor (n : ℕ+) : ∃ d : Core, ∃ k : ℕ, 0 < k ∧ k^2*d.val = n.val := by
  obtain ⟨d,k,_,hk,he,hd⟩ := Nat.sq_mul_squarefree_of_pos n.property
  exact ⟨⟨d,hd⟩,k,hk,he⟩

def core (n : ℕ+) : Core := (factor n).choose
def root (n : ℕ+) : ℕ := (factor n).choose_spec.choose
theorem root_pos (n : ℕ+) : 0 < root n := (factor n).choose_spec.choose_spec.1
theorem root_sq_core (n : ℕ+) : (root n)^2*(core n).val = n.val := (factor n).choose_spec.choose_spec.2

def modeKey (n : ℕ+) : ActionKey := Finsupp.single (core n) ((root n)^3)

def readKey : ActionKey →+ ℝ :=
  Finsupp.liftAddHom (fun d : Core ↦ multiplesHom ℝ (cubicAction d.val))

theorem readKey_injective : Function.Injective readKey := by
  let rat (k : ActionKey) : Core →₀ ℚ := k.mapRange Nat.cast (by simp)
  let L := Finsupp.linearCombination ℚ (fun d : Core ↦ cubicAction d.val)
  have repr (k : ActionKey) : L (rat k) = readKey k := by
    induction k using Finsupp.induction with
    | zero => simp [rat,L]
    | single_add d v f _ _ ih =>
      have ha : rat (Finsupp.single d v+f) = Finsupp.single d (v:ℚ)+rat f := by
        classical
        ext i; by_cases hi : d=i <;> simp [rat,hi]
      rw [ha,map_add,ih,map_add]; congr 1
      simp [L,readKey,Algebra.smul_def]
  intro a b he
  have eqn := squarefree_actions_independent.finsuppLinearCombination_injective ((repr a).trans (he.trans (repr b).symm))
  ext i; exact_mod_cast (show (a i:ℚ) = (b i:ℚ) from DFunLike.congr_fun eqn i)

theorem read_mode (n : ℕ+) : readKey (modeKey n) = cubicAction n.val := by
  simp only [readKey,modeKey,Finsupp.liftAddHom_apply_single]
  change ((root n)^3) • cubicAction (core n).val = _
  rw [← root_sq_core n,cubicAction,cubicAction]
  push_cast
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)]
  simp [nsmul_eq_mul]; ring

theorem rate_key (n : ℕ+) : cubicRate action n = (readKey (modeKey n):ℂ)*action := by
  rw [read_mode]
  unfold cubicRate cubicAction
  rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add (by exact_mod_cast n.property),Real.rpow_one,← Real.sqrt_eq_rpow]

def fullRate (k : ActionKey × ActionKey) : ℂ :=
  (readKey k.1:ℂ)*action + (readKey k.2:ℂ)*star action

/-- Coincidence of the full physical rates is exactly equality of both
squarefree coordinate vectors. This applies to repeated as well as distinct targets. -/
theorem fullRate_injective : Function.Injective fullRate := by
  have im : action.im = -action.re := by simp [action,radialAction,Complex.mul_re,Complex.mul_im]; ring
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [fullRate,Complex.add_re,Complex.mul_re,Complex.add_im,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im,Complex.star_def,im,
    zero_mul,sub_zero,add_zero] at hr hi
  apply Prod.ext <;> apply readKey_injective <;> apply mul_right_cancel₀ action_pos.ne' <;> linarith

theorem fullRate_add (a b : ActionKey × ActionKey) : fullRate (a+b) = fullRate a + fullRate b := by
  simp [fullRate,add_mul]; ring

/-- A unit coordinate can be supplied only by its fundamental wave. -/
theorem modeKey_le_squarefree {n : ℕ+} (T : Finset Core)
    (h : modeKey n ≤ ∑ d ∈ T, Finsupp.single d 1) : root n = 1 ∧ core n ∈ T := by
  classical
  have he := h (core n)
  simp only [modeKey,Finsupp.single_eq_same,Finsupp.finsetSum_apply,Finsupp.single_apply] at he
  by_cases hc : core n ∈ T
  · simp [hc] at he
    exact ⟨by nlinarith [root_pos n],hc⟩
  · simp [hc] at he; have := root_pos n; omega
end
end CubicTheta.Physical
