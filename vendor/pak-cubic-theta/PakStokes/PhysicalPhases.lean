module

public import PakStokes.WaveProducts
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Distinct oscillations at one real decay rate on the physical ray. A
translation eliminates one frequency without losing the selected frequency. -/
public section
namespace CubicTheta
open Complex Filter Finset
open scoped Topology
noncomputable section

def oscillation (b x : ℝ) := Complex.exp (↑(b*x)*I)

@[simp] theorem norm_oscillation (b x : ℝ) : ‖oscillation b x‖ = 1 := by
  simp [oscillation,Complex.norm_exp]

theorem oscillation_add (b x h : ℝ) :
    oscillation b (x+h) = oscillation b h * oscillation b x := by
  simp [oscillation,mul_add,Complex.exp_add,mul_comm]

private theorem distinct_shift {a b : ℝ} (hne : a ≠ b) :
    ∃ h : ℝ, oscillation a h ≠ oscillation b h := by
  let h := Real.pi/(a-b)
  have hh : (a-b)*h = Real.pi := by dsimp [h]; field_simp [sub_ne_zero.mpr hne]
  have eqn : oscillation a h = -oscillation b h := by
    unfold oscillation
    rw [show a*h = Real.pi+b*h by nlinarith [hh]]
    push_cast
    rw [add_mul,Complex.exp_add,Complex.exp_pi_mul_I,neg_one_mul]
  refine ⟨h,fun he ↦ ?_⟩
  have hz : oscillation b h = 0 := by linear_combination (eqn-he)/2
  exact Complex.exp_ne_zero _ hz

/-- A finite trigonometric polynomial tending to zero has zero coefficients.
Only the selected frequency must be distinct from each of the others. -/
theorem oscillatory_coefficient_zero {ι : Type*} [DecidableEq ι] (target : ι)
    (b : ι → ℝ) (s : Finset ι) (apart : ∀ i ∈ s, b target ≠ b i)
    (c : ι → ℂ) (lim : Tendsto (fun x : ℝ ↦ c target*oscillation (b target) x +
      ∑ i ∈ s, c i*oscillation (b i) x) atTop (𝓝 0)) : c target = 0 := by
  induction s using Finset.induction_on generalizing c with
  | empty =>
    simpa [norm_mul] using lim.norm
  | @insert i s hi ih =>
    obtain ⟨h,hn⟩ := distinct_shift (apart i (mem_insert_self ..))
    let d (j : ι) := c j * (oscillation (b j) h - oscillation (b i) h)
    have translate : Tendsto (fun x : ℝ ↦ x+h) atTop atTop := by
      apply tendsto_atTop.2; intro y; filter_upwards [eventually_ge_atTop (y-h)] with x hx; linarith
    have diff := (lim.comp translate).sub (lim.const_mul (oscillation (b i) h))
    have reduced : Tendsto (fun x : ℝ ↦ d target * oscillation (b target) x +
        ∑ j ∈ s, d j * oscillation (b j) x) atTop (𝓝 0) := by
      rw [mul_zero,sub_zero] at diff
      apply diff.congr
      intro x
      simp only [Function.comp_apply,sum_insert hi,oscillation_add,mul_add,mul_sum]
      have inner (j : ι) : c j*(oscillation (b j) h*oscillation (b j) x) -
          oscillation (b i) h*(c j*oscillation (b j) x) = d j*oscillation (b j) x := by
        dsimp [d]; ring
      rw [show ∑ j ∈ s, d j*oscillation (b j) x = _ from
        (sum_congr rfl fun j _ ↦ inner j).symm, sum_sub_distrib]
      dsimp [d]; ring
    exact (mul_eq_zero.mp (ih (fun j hj ↦ apart j (mem_insert_of_mem hj)) d reduced)).resolve_right
      (sub_ne_zero.mpr hn)

/-- An all-orders flat sum over a finite frequency cluster forces every
amplitude with an ordinary first power asymptotic (or a zero germ) to vanish. -/
theorem physical_cluster_flat {ι : Type*} (s : Finset ι) (b : ι → ℝ)
    (inject : Set.InjOn b (s : Set ι)) (a : ι → ℝ → ℂ)
    (asymp : ∀ i ∈ s, (∀ᶠ x : ℝ in atTop, a i x = 0) ∨ ∃ v : ℝ, ∃ z : ℂ, z ≠ 0 ∧
      Tendsto (fun x : ℝ ↦ x^v • a i x) atTop (𝓝 z))
    (flat : ∀ u : ℝ, Tendsto (fun x : ℝ ↦ x^u • ∑ i ∈ s, oscillation (b i) x*a i x)
      atTop (𝓝 0)) : ∀ i ∈ s, ∀ᶠ x : ℝ in atTop, a i x = 0 := by
  classical
  let active := s.filter fun i ↦ ¬∀ᶠ x : ℝ in atTop, a i x = 0
  by_contra! bad
  obtain ⟨i,hi,hn⟩ := bad
  have hne : active.Nonempty := ⟨i,mem_filter.mpr ⟨hi,fun h ↦ (hn.and_eventually h).exists.elim (fun _ h ↦ h.1 h.2)⟩⟩
  have hA j (hj : j ∈ active) := (asymp j (mem_filter.mp hj).1).resolve_left (mem_filter.mp hj).2
  choose v z nz lead using hA
  let power (j : ι) := if hj : j ∈ active then v j hj else 0
  obtain ⟨k,hk,hmin⟩ := active.exists_min_image power hne
  let coeff (j : ι) := if hj : j ∈ active then if power j = power k then z j hj else 0 else 0
  have hkz : coeff k ≠ 0 := by simpa [coeff,hk] using nz k hk
  have each (j : ι) (hj : j ∈ s) :
      Tendsto (fun x : ℝ ↦ x^(power k) • a j x) atTop (𝓝 (coeff j)) := by
    by_cases ha : j ∈ active
    · have l : Tendsto (fun x : ℝ ↦ x^(power j) • a j x) atTop (𝓝 (z j ha)) := by
        simpa only [power,dite_eq_left ha] using lead j ha
      by_cases same : power j = power k
      · simpa [coeff,ha,same] using l
      have lt := lt_of_le_of_ne (hmin j ha) (Ne.symm same)
      have dec : Tendsto (fun x : ℝ ↦ x^(power k-power j)) atTop (𝓝 0) := by
        simpa [neg_sub] using tendsto_rpow_neg_atTop (sub_pos.mpr lt)
      have h := dec.smul l
      rw [zero_smul] at h
      apply (show coeff j = 0 by simp [coeff,ha,same]) ▸ h.congr'
      filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
      rw [smul_smul,← Real.rpow_add hx,sub_add_cancel]
    · have hz : ∀ᶠ x : ℝ in atTop, a j x = 0 := by simpa [active,hj] using ha
      simp only [coeff,dite_eq_right ha]
      apply tendsto_const_nhds.congr'; filter_upwards [hz] with x hx; simp [hx]
  have err (j : ι) (hj : j ∈ s) : Tendsto (fun x : ℝ ↦
      oscillation (b j) x*(x^(power k) • a j x - coeff j)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa [norm_mul] using (((each j hj).sub_const (coeff j)).norm)
  have lim := (flat (power k)).sub (tendsto_finsetSum s err)
  simp only [sum_const_zero,sub_zero] at lim
  have poly : Tendsto (fun x : ℝ ↦ ∑ j ∈ s, coeff j*oscillation (b j) x) atTop (𝓝 0) := by
    apply lim.congr
    intro x
    simp only [Finset.smul_sum,← sum_sub_distrib,← mul_smul_comm]
    apply sum_congr rfl; intro j _
    simp [Complex.real_smul]; ring
  have ks := (mem_filter.mp hk).1
  apply hkz
  apply oscillatory_coefficient_zero k b (s.erase k) (fun j hj h ↦
    (ne_of_mem_erase hj) ((inject ks (mem_of_mem_erase hj) h).symm)) coeff
  apply poly.congr; intro x
  exact (add_sum_erase _ (fun j ↦ coeff j*oscillation (b j) x) ks).symm

/-- Real decay gives an ordered outer series. Within each decay rate, translation
separates the finitely many distinct imaginary frequencies. -/
theorem separate_physical_products {ι : Type*} {κ : ℕ → Type*} [∀ n, Fintype (κ n)]
    (a : WaveExpansion ι) (g : ι → Σ n, κ n) (w : ℕ → ℝ) (b : ∀ n, κ n → ℝ)
    (hr : ∀ i, a.rate i = ⟨w (g i).1,-b (g i).1 (g i).2⟩)
    (order : StrictMono w) (apart : ∀ n, Function.Injective (b n))
    (zero : ∀ᶠ x : ℝ in atTop, a.value x = 0)
    (asymp : ∀ k, (∀ᶠ x : ℝ in atTop, a.groupAmplitude g k x = 0) ∨
      ∃ v : ℝ, ∃ z : ℂ, z ≠ 0 ∧ Tendsto
        (fun x : ℝ ↦ x^v • a.groupAmplitude g k x) atTop (𝓝 z)) :
    ∀ n (j : κ n), ∀ᶠ x : ℝ in atTop, a.groupAmplitude g ⟨n,j⟩ x = 0 := by
  classical
  let r (k : Σ n, κ n) : ℂ := ⟨w k.1,-b k.1 k.2⟩
  let cluster (n : ℕ) (x : ℝ) := ∑ j : κ n, oscillation (b n j) x * a.groupAmplitude g ⟨n,j⟩ x
  let B (n : ℕ) := ∑ j : κ n, a.groupBudget g ⟨n,j⟩
  have budget : Summable B := by simpa [B,tsum_fintype] using (a.grouped_budget g).sigma
  have major : ∀ᶠ x : ℝ in atTop, ∀ n, ‖cluster n x‖ ≤ B n * Real.exp (w n*1) * x^(a.loss:ℝ) := by
    filter_upwards [a.grouped_bound g r hr] with x hx n
    unfold cluster B
    simp only [Finset.sum_mul,mul_one,Real.rpow_natCast]
    apply (norm_sum_le _ _).trans (sum_le_sum ?_)
    intro j _
    simpa [norm_mul,r] using hx ⟨n,j⟩
  have zeroSum : ∀ᶠ x : ℝ in atTop, HasSum (fun n ↦ Real.exp (-w n*x) • cluster n x) 0 := by
    filter_upwards [a.grouped_hasSum g r hr,zero] with x hx hz
    rw [hz] at hx
    apply hx.sigma
    intro n
    convert! hasSum_fintype (fun j : κ n ↦ Complex.exp (-r ⟨n,j⟩ * x) * a.groupAmplitude g ⟨n,j⟩ x) using 1
    unfold cluster
    rw [Finset.smul_sum]
    apply sum_congr rfl
    intro j _
    simp only [Complex.real_smul,oscillation,← mul_assoc,Complex.ofReal_exp,← Complex.exp_add]
    congr 2
    apply Complex.ext <;> simp [r,Complex.mul_re,Complex.mul_im]
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    have earlier (m : ℕ) (hm : m < n) : ∀ᶠ x : ℝ in atTop, cluster m x = 0 := by
      filter_upwards [eventually_all.2 (ih m hm)] with x hx
      simp [cluster,hx]
    exact fun j ↦ physical_cluster_flat univ (b n) (apart n).injOn
      (fun k ↦ a.groupAmplitude g ⟨n,k⟩) (fun k _ ↦ asymp ⟨n,k⟩)
      (flat_of_earlier_zero w order cluster B budget a.loss 1 major zeroSum n earlier) j (mem_univ j)

end
end CubicTheta
