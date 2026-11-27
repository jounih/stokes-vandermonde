module

public import PakStokes.MarkedJacobian
public import PakStokes.MarkedSeries
public import PakStokes.RegularCube
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Vandermonde
import all PakStokes.MarkedSeries
import all PakStokes.ActionCoordinates
import all PakStokes.RegularCube
import all PakStokes.PhysicalExpression
import all PakStokes.PhysicalSeries
import all PakStokes.PhysicalKummer
import all PakStokes.PhysicalAiry
import all PakStokes.CubicKummerJets
import all PakStokes.LaplaceWaveJets
import all PakStokes.WaveProducts

/-! The linear coefficients of the marked jets are the single fundamental
Airy waves. Their eventual Vandermonde determinant is a unit of the germ ring. -/
public section
namespace CubicTheta.Physical
open Filter Matrix Complex LaplaceWave JetExpression
open scoped Topology
noncomputable section

instance germComplexAlgebra : Algebra ℂ RayGerm :=
  ((Germ.coeRingHom (atTop : Filter ℝ)).comp (Pi.constRingHom ℝ ℂ)).toAlgebra

def markedJet (j : ℕ) := (JetExpression.jet j).withBackground.marked

private def positiveCore (d : Core) : ℕ+ := ⟨d.val,Nat.pos_of_ne_zero d.property.ne_zero⟩

private theorem key_core (d : Core) : modeKey (positiveCore d) = Finsupp.single d 1 := by
  let n := positiveCore d
  have he := root_sq_core n
  have sq : root n * root n ∣ d.val := ⟨_,by simpa [sq,n,positiveCore] using he.symm⟩
  have r := Nat.isUnit_iff.mp (d.property _ sq)
  rw [r,one_pow,one_mul] at he
  have eqc : core n = d := Subtype.ext he
  change modeKey n = _
  simp [modeKey,r,eqc]

private theorem mode_unique (n : ℕ+) {d : Core} (hk : modeKey n = Finsupp.single d 1) :
    n = positiveCore d := by
  have hle : modeKey n ≤ ∑ c ∈ ({d} : Finset Core), Finsupp.single c 1 := by classical simp [hk]
  obtain ⟨r,hc⟩ := modeKey_le_squarefree _ hle
  have hval : core n = d := by simpa using hc
  apply Subtype.ext
  change n.val=d.val
  simpa only [r,one_pow,one_mul,hval] using (root_sq_core n).symm

private theorem first_jet (j : ℕ) (d : Core) :
    MvPowerSeries.coeff (Finsupp.single (Sum.inl d) 1) (markedJet j) =
      Germ.ofFun ((physicalJet j).amplitude (.inl (positiveCore d))) := by
  classical
  let k : Key := Finsupp.single (Sum.inl d) 1
  let e := JetExpression.jet j
  have hne : k ≠ 0 := Finsupp.single_ne_zero.mpr one_ne_zero
  change MvPowerSeries.coeff k ((e.add (.coeff (backgroundCoefficient j))).marked) = _
  rw [marked_add,marked_coeff,map_add,MvPowerSeries.coeff_C]; simp only [hne,ite_false,add_zero]
  let I : Fiber e k := ⟨Sum.inl (positiveCore d),by change (modeKey _).sumElim 0 = k; simp [key_core,k]⟩
  have only (x : Fiber e k) : x=I := by
    apply Subtype.ext; obtain ⟨i,hi⟩ := x
    change e.key i=k at hi
    rcases i with n|n
    · change (modeKey n).sumElim 0=k at hi
      have eqn : modeKey n = Finsupp.single d 1 := by
        apply DFunLike.ext; intro c
        simpa [k,Finsupp.single_apply] using DFunLike.congr_fun hi (.inl c)
      exact congrArg Sum.inl (mode_unique n eqn)
    · change (0 : ActionKey).sumElim (modeKey n)=k at hi
      simpa [k] using DFunLike.congr_fun hi (.inl d)
  change (∑ x : Fiber e k, _) = _
  rw [Finset.sum_eq_single I (fun x _ hn ↦ (hn (only x)).elim) (by simp)]
  rfl

private theorem pref_ne (n : ℕ+) : coefficient * modeFactor n ≠ 0 := by
  have hh : h ≠ 0 := fun he ↦ by have := congrArg Complex.im he; norm_num [h] at this
  have ha : (alphaConst:ℂ) ≠ 0 := by exact_mod_cast alphaPos.ne'
  have hp := Real.rpow_pos_of_pos lengthPos (-(1/4:ℝ))
  have np : 0 < (n:ℝ) := by exact_mod_cast n.property
  unfold coefficient modeFactor
  apply mul_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos np _).ne')
  apply mul_ne_zero _ (Complex.ofReal_ne_zero.mpr hp.ne')
  apply mul_ne_zero _ airyWaveConstant_ne_zero
  apply div_ne_zero _ ha
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) hh

private theorem scaled_jet (n : ℕ+) (j : ℕ) :
    Tendsto (fun p : ℝ ↦ ((p^(-(1/2:ℝ)):ℝ):ℂ)*(physicalJet j).amplitude (.inl n) p)
      atTop (𝓝 ((coefficient*modeFactor n)*(-cubicRate action n)^j)) := by
  let c := cubicRate action n
  have hc : 0<c.re := rate_pos action_pos n
  have a := cubicBeta_analytic hc
  have lim := amplitude_limit (a.continuousOn.mono Set.Ioi_subset_Ici_self) (a 0 le_rfl).continuousAt
    (fun u hu ↦ cubicBeta_bound hc hu.le) c j (3/2) 0
  have normed : Tendsto (fun x : ℝ ↦ ((x^(-(1/2:ℝ)):ℝ):ℂ)*amplitude (cubicBetaKernel c) c j (3/2) 0 x)
      atTop (𝓝 ((-c)^j)) := by
    norm_num [cubicBeta_zero,Complex.real_smul] at lim ⊢
    exact lim
  simpa only [physicalJet,WaveExpansion.add,Sum.elim_inl,WaveExpansion.scale,kummerJet,cubicJet,
    c,mul_assoc,mul_left_comm,mul_comm] using normed.const_mul (coefficient*modeFactor n)

private theorem matrix_unit {J : ℕ} (node : Fin J → Core) (inj : Function.Injective node) :
    IsUnit (Matrix.of fun i (j : Fin J) ↦
      MvPowerSeries.coeff (Finsupp.single (Sum.inl (node i)) 1) (markedJet j.val)).det := by
  classical
  let n (i : Fin J) := positiveCore (node i)
  let rate (i : Fin J) := -cubicRate action (n i)
  have hn : Function.Injective rate := by
    intro i j he; apply inj
    have hr : cubicRate action (n i) = cubicRate action (n j) := neg_injective he
    rw [rate_key,rate_key] at hr
    have hz : action ≠ 0 := fun h ↦ by have := action_pos; simp [h] at this
    have hh := readKey_injective (Complex.ofReal_injective (mul_right_cancel₀ hz hr))
    simp only [n,key_core] at hh
    by_contra hij
    have := DFunLike.congr_fun hh (node i); simp [hij] at this
  let V := Matrix.vandermonde rate
  let L := Matrix.of fun i j ↦ (coefficient*modeFactor (n i))*V i j
  have hnz : L.det ≠ 0 := by
    unfold L; rw [det_mul_column]; exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pref_ne _)
      (Matrix.det_vandermonde_ne_zero_iff.mpr hn)
  let M (p : ℝ) := Matrix.of fun i (j : Fin J) ↦ (physicalJet j.val).amplitude (.inl (n i)) p
  let scale (p : ℝ) := ((p^(-(1/2:ℝ)):ℝ):ℂ)
  have lim : Tendsto (fun p ↦ scale p • M p) atTop (𝓝 L) := by
    apply tendsto_pi_nhds.mpr; intro i; apply tendsto_pi_nhds.mpr; intro j
    exact scaled_jet (n i) j.val
  have nonzero := ((continuous_id.matrix_det.tendsto L).comp lim).eventually (isOpen_ne.mem_nhds hnz)
  have detNZ : ∀ᶠ p in atTop, (M p).det ≠ 0 := by
    filter_upwards [nonzero] with p hp
    change (scale p • M p).det ≠ 0 at hp
    rw [Matrix.det_smul] at hp; exact right_ne_zero_of_mul hp
  let H := Germ.coeRingHom (atTop : Filter ℝ) (R := ℂ)
  let N : Matrix (Fin J) (Fin J) (ℝ → ℂ) := Matrix.of fun i j p ↦ M p i j
  have point (p : ℝ) : N.det p = (M p).det := (Pi.evalRingHom _ p).map_det N
  have hu : IsUnit (H N.det) := by
    apply isUnit_iff_exists_inv.mpr; refine ⟨H (fun p ↦ (N.det p)⁻¹),?_⟩
    apply Germ.coe_eq.mpr
    filter_upwards [detNZ] with p hp; change N.det p * (N.det p)⁻¹=1; simp [point,hp]
  rw [H.map_det] at hu
  simp_rw [first_jet]
  have eqm : (Matrix.of fun i (j : Fin J) ↦ (Germ.ofFun ((physicalJet j.val).amplitude (.inl (positiveCore (node i)))) : RayGerm)) = H.mapMatrix N := by ext i j; rfl
  rwa [eqm]

theorem independent_marked_jets (J : ℕ) :
    AlgebraicIndependent ℂ (fun i : Fin J ↦ markedJet i.val) := by
  let node (i : Fin J) : Core := ⟨Nat.nth Nat.Prime i.val,(Nat.prime_nth_prime _).squarefree⟩
  have inj : Function.Injective node := fun i j h ↦ Fin.ext
    ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective (congrArg Subtype.val h))
  exact independent_of_marked_jacobian (fun i ↦ Sum.inl (node i)) _ (matrix_unit node inj)
end
end CubicTheta.Physical
