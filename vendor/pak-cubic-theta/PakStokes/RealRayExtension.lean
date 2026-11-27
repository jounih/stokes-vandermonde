module

public import KernelAnalytic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Real-analytic complex-valued kernels on the positive ray admit compatible
holomorphic extensions on an open neighborhood stable under radial contraction.
This supplies the domain needed by the existing convolution theorem. -/
public section
namespace CubicTheta
open Complex Set Filter Metric
open scoped Topology
noncomputable section

private theorem disk_extension {F : ℝ → ℂ} {x : ℝ} (hf : AnalyticAt ℝ F x) :
    ∃ (r : ℝ) (g : ℂ → ℂ), 0<r ∧ AnalyticOnNhd ℂ g (ball (x:ℂ) r) ∧
      ∀ y : ℝ, (y:ℂ) ∈ ball (x:ℂ) r → g y = F y := by
  obtain ⟨p,R,hp⟩ := hf
  obtain ⟨s,hs,hsR⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hs' : 0 < (s:ℝ) := by exact_mod_cast (ENNReal.coe_pos.mp hs)
  let f (n : ℕ) (z : ℂ) := (z-x)^n*p.coeff n
  have budget := p.summable_norm_mul_pow (hsR.trans_le hp.r_le)
  have bound (n : ℕ) (z : ℂ) (hz : z ∈ ball (x:ℂ) s) :
      ‖f n z‖ ≤ ‖p n‖*(s:ℝ)^n := by
    change ‖(z-(x:ℂ))^n*p.coeff n‖ ≤ _
    rw [norm_mul,norm_pow,FormalMultilinearSeries.norm_apply_eq_norm_coef,mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (by simpa [dist_eq_norm] using (mem_ball.mp hz).le) n) (norm_nonneg _)
  refine ⟨s,fun z ↦ ∑' n, f n z,hs',(Complex.differentiableOn_tsum_of_summable_norm budget
    (fun n ↦ by unfold f; fun_prop) isOpen_ball bound).analyticOnNhd isOpen_ball,?_⟩
  intro y hy
  have hr : ‖y-x‖₊ < s := by exact_mod_cast (show ‖y-x‖ < (s:ℝ) by simpa [dist_eq_norm,← Complex.ofReal_sub] using mem_ball.mp hy)
  have hmem : y-x ∈ eball (0:ℝ) R := by
    rw [mem_eball,edist_zero_right]; exact (ENNReal.coe_lt_coe.mpr hr).trans hsR
  simpa [f,FormalMultilinearSeries.apply_eq_pow_smul_coeff,Complex.real_smul] using! (hp.hasSum hmem).tsum_eq

private theorem disk_agree {F : ℝ → ℂ} {a b : ℝ} {r s : ℝ} {g h : ℂ → ℂ}
    (ga : AnalyticOnNhd ℂ g (ball (a:ℂ) r)) (ha : AnalyticOnNhd ℂ h (ball (b:ℂ) s))
    (gr : ∀ u : ℝ, (u:ℂ) ∈ ball (a:ℂ) r → g u = F u)
    (hr : ∀ u : ℝ, (u:ℂ) ∈ ball (b:ℂ) s → h u = F u) :
    EqOn g h (ball (a:ℂ) r ∩ ball (b:ℂ) s) := by
  intro z hz
  let U := ball (a:ℂ) r ∩ ball (b:ℂ) s
  have proj (c : ℝ) : dist (z.re:ℂ) (c:ℂ) ≤ dist z (c:ℂ) := by
    simpa [dist_eq_norm,← Complex.ofReal_sub,Real.norm_eq_abs] using Complex.abs_re_le_norm (z-c)
  have center : (z.re:ℂ) ∈ U := ⟨(proj a).trans_lt hz.1,(proj b).trans_lt hz.2⟩
  have nb := Complex.continuous_ofReal.continuousAt.preimage_mem_nhds
    ((isOpen_ball.inter isOpen_ball).mem_nhds center)
  have eqreal : ∀ᶠ u : ℝ in 𝓝[≠] z.re, g (u:ℂ) = h u :=
    Filter.mem_of_superset (nhdsWithin_le_nhds nb) <| fun u hu ↦ (gr u hu.1).trans (hr u hu.2).symm
  have transport : Tendsto Complex.ofReal (𝓝[≠] z.re) (𝓝[≠] (z.re:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds,
      Filter.mem_of_superset self_mem_nhdsWithin fun _ hu ↦ fun he ↦ hu (Complex.ofReal_injective he)⟩
  exact (ga.mono inter_subset_left).eqOn_of_preconnected_of_frequently_eq (ha.mono inter_subset_right)
    (((convex_ball (a:ℂ) r).inter (convex_ball (b:ℂ) s)).isPreconnected) center
    (transport.frequently eqreal.frequently) hz

/-- The extension agrees on the entire real line. Off its open domain its
complex values are immaterial. -/
theorem real_ray_extension {F : ℝ → ℂ} (hF : AnalyticOnNhd ℝ F (Ici 0)) :
    ∃ (G : ℂ → ℂ) (U : Set ℂ), IsOpen U ∧ AnalyticOnNhd ℂ G U ∧
      (∀ t : ℝ, 0≤t → (t:ℂ) ∈ U) ∧
      (∀ z ∈ U, ∀ t ∈ Icc (0:ℝ) 1, (t:ℂ)*z ∈ U) ∧ ∀ t : ℝ, G t = F t := by
  classical
  choose r g pos anal eqn using fun x : Ici (0:ℝ) ↦ disk_extension (hF x x.property)
  let B (x : Ici (0:ℝ)) := ball ((x:ℝ):ℂ) (r x)
  let V := ⋃ x, B x
  let G (z : ℂ) := if h : ∃ x, z ∈ B x then g h.choose z else F z.re
  have agree (x : Ici (0:ℝ)) : EqOn G (g x) (B x) := by
    intro z hz
    have he : ∃ i, z ∈ B i := ⟨x,hz⟩
    simp only [G,dite_eq_left he]
    exact disk_agree (anal _) (anal _) (eqn _) (eqn _) ⟨he.choose_spec,hz⟩
  have vopen : IsOpen V := isOpen_iUnion fun _ ↦ isOpen_ball
  have holo : AnalyticOnNhd ℂ G V := by
    intro z hz; obtain ⟨x,hx⟩ := mem_iUnion.mp hz
    exact (anal x z hx).congr (Filter.mem_of_superset (isOpen_ball.mem_nhds hx) fun _ h ↦ (agree x h).symm)
  have realV (t : ℝ) (ht : 0≤t) : (t:ℂ) ∈ V := mem_iUnion.mpr ⟨⟨t,ht⟩,mem_ball_self (pos _)⟩
  let U := {z : ℂ | ∀ t ∈ Icc (0:ℝ) 1, (t:ℂ)*z ∈ V}
  have uopen : IsOpen U := by
    rw [isOpen_iff_mem_nhds]; intro z hz
    let W := (fun a : ℝ × ℂ ↦ (a.1:ℂ)*a.2) ⁻¹' V
    have wo : IsOpen W := vopen.preimage (by fun_prop)
    have hsub : (Icc (0:ℝ) 1) ×ˢ ({z} : Set ℂ) ⊆ W := by
      rintro ⟨t,u⟩ ⟨ht,hu⟩; rcases Set.mem_singleton_iff.mp hu with rfl; exact hz t ht
    obtain ⟨A,C,_,co,ha,hc,hac⟩ := generalized_tube_lemma isCompact_Icc isCompact_singleton wo hsub
    exact Filter.mem_of_superset (co.mem_nhds (hc (mem_singleton _))) fun u hu t ht ↦ hac (show (t,u) ∈ A ×ˢ C from ⟨ha ht,hu⟩)
  refine ⟨G,U,uopen,holo.mono (fun z hz ↦ by simpa using hz 1 (by simp)),?_,?_,?_⟩
  · intro t ht a ha; simpa only [← ofReal_mul] using realV (a*t) (mul_nonneg ha.1 ht)
  · intro z hz t ht a ha; rw [← mul_assoc,← ofReal_mul]; exact hz _ ⟨mul_nonneg ha.1 ht.1,
        (mul_le_mul_of_nonneg_left ht.2 ha.1).trans (by simpa using ha.2)⟩
  · intro t; dsimp only [G]; split
    next h => exact eqn _ _ h.choose_spec
    next => simp

theorem positive_convolution_analytic {F G : ℝ → ℂ}
    (hF : AnalyticOnNhd ℝ F (Ici 0)) (hG : AnalyticOnNhd ℝ G (Ici 0)) :
    AnalyticOnNhd ℝ (borelProduct F G) (Ici 0) := by
  obtain ⟨f,U,ho,ha,hr,hs,hf⟩ := real_ray_extension hF
  obtain ⟨g,V,jo,ja,jr,js,hg⟩ := real_ray_extension hG
  simpa only [hf,hg] using borelProduct_analytic (U := U ∩ V) (ho.inter jo)
    (fun z hz t ht ↦ ⟨hs _ hz.1 _ ht,js _ hz.2 _ ht⟩)
    (fun x hx ↦ ⟨hr x hx,jr x hx⟩) (ha.mono inter_subset_left) (ja.mono inter_subset_right)

end
end CubicTheta
