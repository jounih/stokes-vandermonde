module

public import PakPrimes.NthPrimeCriterion
public import PakPrimes.MainTheorem

/-! Quantitative inversion of the all-orders prime number theorem at the prime indices. -/

public section
noncomputable section
namespace PakPrimes.NthPrime
open Set Filter Real MeasureTheory
open scoped Topology

theorem count_index (n : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  rw [Nat.primeCounting_eq_primeCounting'_succ, Nat.primeCounting', Nat.count_succ]
  simp only [Nat.prime_nth_prime, ite_true]
  exact congrArg (· + 1) (Nat.primeCounting'_nth_eq n)

/-- The all-orders prime-counting error remains valid at the exact prime indices
with normalization by the index and its logarithm. -/
theorem li_at_prime_index (hpnt : Main.PNTAllOrders) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      |Main.li (Nat.nth Nat.Prime n) - (n + 1 : ℝ)| ≤
        C * (n + 1 : ℝ) / (log (n + 1 : ℝ)) ^ M := by
  obtain ⟨C, hC, herr⟩ := hpnt (M+1)
  have l2 : 0 < log 2 := log_pos (by norm_num)
  refine ⟨C / log 2, div_pos hC l2, ?_⟩
  have ht : Tendsto (fun n : ℕ => (Nat.nth Nat.Prime n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  filter_upwards [ht.eventually herr, eventually_ge_atTop 2] with n he hn
  let p := Nat.nth Nat.Prime n
  have hp : n + 2 ≤ p := Nat.add_two_le_nth_prime n
  have hidx : Nat.primeCounting p = n + 1 := count_index n
  change |(Nat.primeCounting ⌊(p : ℝ)⌋₊ : ℝ) - Main.li p| ≤ _ at he
  rw [Nat.floor_natCast, hidx, Nat.cast_add, Nat.cast_one, abs_sub_comm] at he
  have h4 : 4 ≤ p := by omega
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hpn : (n + 1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (show n+1 ≤ p by omega)
  have hin : (0 : ℝ) < Real.log (n+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n+1 by omega))
  have hlogle := Real.log_le_log (by positivity : 0 < (n+1 : ℝ)) hpn
  have hcheb := Chebyshev.pi_ge_of_four_le h4
  rw [hidx, Nat.cast_add, Nat.cast_one] at hcheb
  have hbound : (p : ℝ) / Real.log p ≤ (n + 1 : ℝ) / Real.log 2 := by
    rw [div_le_div_iff₀ hlog l2]
    exact (div_le_iff₀ hlog).mp hcheb
  apply he.trans
  calc
    C * (p : ℝ) / (log (p : ℝ)) ^ (M+1)
      = C * ((p : ℝ) / log p) / (log (p : ℝ)) ^ M := by rw [pow_succ]; ring
    _ ≤ C * ((n+1 : ℝ) / log 2) / (log (n+1 : ℝ)) ^ M := by gcongr
    _ = (C / log 2) * (n + 1 : ℝ) / (log (n+1 : ℝ))^M := by ring

private theorem liIntegrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun v : ℝ => (log v)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro x hx
  have h : 1 < x := by linarith [hx.1]
  exact ((continuousAt_log (by linarith : x ≠ 0)).inv₀ (log_pos h).ne').continuousWithinAt

private theorem li_spacing {a b B : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hb : b ≤ B) :
    b - a ≤ log B * (Main.li b - Main.li a) := by
  have lB : 0 < log B := log_pos (by linarith)
  have eqn := intervalIntegral.integral_add_adjacent_intervals (liIntegrable (by norm_num) ha)
    (liIntegrable ha hab)
  change Main.li a + _ = Main.li b at eqn
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab
    (intervalIntegrable_const (c := (log B)⁻¹)) (liIntegrable ha hab)
    (fun x hx => inv_anti₀ (log_pos (show 1 < x by linarith [hx.1]))
      (log_le_log (by linarith [hx.1]) (hx.2.trans hb)))
  rw [intervalIntegral.integral_const, smul_eq_mul, ← div_eq_mul_inv] at hi
  have := (div_le_iff₀ lB).mp hi
  nlinarith [eqn]

theorem inverseLi_exists (v : ℝ) (hv : 0 ≤ v) :
    ∃ x ∈ Icc (2:ℝ) ((4 * (v+1))^2), Main.li x = v := by
  let B : ℝ := (4 * (v+1))^2
  have hB : 2 ≤ B := by dsimp [B]; nlinarith [sq_nonneg v]
  have hlog : log B ≤ 8 * (v+1) := by
    dsimp [B]; rw [log_pow]; norm_num
    linarith [log_le_sub_one_of_pos (show 0 < 4 * (v+1) by positivity)]
  have hlogpos : 0 < log B := log_pos (by linarith)
  have l2 : Main.li 2 = 0 := by simp [Main.li]
  have hgap := li_spacing (a := 2) (b := B) (B := B) (by norm_num) hB le_rfl
  rw [l2, sub_zero] at hgap
  have hvB : v ≤ Main.li B := by
    by_contra! h
    have hsmall := mul_lt_mul_of_pos_left h hlogpos
    have hbig := mul_le_mul_of_nonneg_right hlog hv
    dsimp [B] at hgap
    nlinarith
  have hcont : ContinuousOn Main.li (Icc 2 B) := by
    change ContinuousOn (fun b => ∫ t : ℝ in (2 : ℝ)..b, (log t)⁻¹) (Icc 2 B)
    simpa only [uIcc_of_le hB] using
      (intervalIntegral.continuousOn_primitive_interval' (liIntegrable (by norm_num) hB) left_mem_uIcc)
  exact intermediate_value_Icc hB hcont (show v ∈ Icc (Main.li 2) (Main.li B) by
    rw [l2]; exact ⟨hv, hvB⟩)

/-- The positive branch of inverse li. Only nonnegative arguments are used. -/
@[expose] def inverseLi (v : ℝ) : ℝ :=
  if hv : 0 ≤ v then (inverseLi_exists v hv).choose else 2

theorem inverseLi_spec {v : ℝ} (hv : 0 ≤ v) :
    inverseLi v ∈ Icc 2 ((4*(v+1))^2) ∧ Main.li (inverseLi v) = v := by
  simpa only [inverseLi, dite_eq_left hv] using (inverseLi_exists v hv).choose_spec

private theorem inverse_spacing {a b B : ℝ} (ha : a ∈ Icc 2 B) (hb : b ∈ Icc 2 B) :
    |a-b| ≤ log B * |Main.li a - Main.li b| := by
  have hlog : 0 ≤ log B := log_nonneg (by linarith [ha.1, ha.2])
  rcases le_total a b with hab | hba
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hab)]
    have hh : Main.li b - Main.li a ≤ |Main.li a - Main.li b| := by
      simpa only [neg_sub] using neg_le_abs (Main.li a - Main.li b)
    exact (li_spacing ha.1 hab hb.2).trans (mul_le_mul_of_nonneg_left hh hlog)
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    exact (li_spacing hb.1 hba ha.2).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hlog)

/-- Primes differ from the positive inverse logarithmic integral by less than every
inverse logarithmic order relative to their index. -/
theorem nth_prime_inverseLi_allOrders (hpnt : Main.PNTAllOrders) (M : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      |(Nat.nth Nat.Prime n : ℝ) - inverseLi (n+1 : ℝ)| ≤
        C * (n+1 : ℝ) / (log (n+1 : ℝ))^M := by
  obtain ⟨C, hC, happrox⟩ := li_at_prime_index hpnt (M+1)
  refine ⟨8*C, by positivity, ?_⟩
  filter_upwards [happrox, eventually_ge_atTop 2] with n he hn
  let v : ℝ := n + 1
  let p : ℝ := Nat.nth Nat.Prime n
  let B : ℝ := (4*(v+1))^2
  have hv : 2 ≤ v := by dsimp [v]; exact_mod_cast (show 2 ≤ n+1 by omega)
  have hi := inverseLi_spec (v := v) (by linarith)
  have hpos : 0 < log v := log_pos (by linarith)
  have hpB : p ∈ Icc 2 B := by
    constructor
    · dsimp [p]; exact_mod_cast (show 2 ≤ Nat.nth Nat.Prime n by linarith [Nat.add_two_le_nth_prime n])
    · have h0 : p ≤ (4 * v)^2 := by dsimp [p,v]; exact_mod_cast nth_prime_quadratic_bound n
      dsimp [B]
      nlinarith
  have lB : log B ≤ 8 * log v := by
    have hh : 4*(v+1) ≤ v^4 := by
      have hv2 : 0 ≤ v^2-4 := by nlinarith [sq_nonneg (v-2)]
      nlinarith [mul_nonneg hv2 (sq_nonneg v), sq_nonneg (v-1)]
    dsimp [B]; rw [log_pow]
    have hl := log_le_log (show 0 < 4*(v+1) by positivity) hh
    rw [log_pow] at hl
    norm_num at hl ⊢
    linarith
  have hinv := inverse_spacing hpB hi.1
  rw [hi.2] at hinv
  apply hinv.trans
  change |Main.li p-v| ≤ C * v / (log v)^(M+1) at he
  calc
    log B * |Main.li p - v| ≤ (8 * log v) * (C * v / (log v) ^ (M+1)) := by gcongr
    _ = (8*C)*v / (log v)^M := by rw [pow_succ]; field_simp

/-- The chosen positive inverse has the exact derivative used in the formal pencil
calculation. -/
theorem inverseLi_hasDerivAt {v : ℝ} (hv : 0 < v) :
    HasDerivAt inverseLi (log (inverseLi v)) v := by
  let B := (4*(v+2))^2
  have hB : 2 < B := by dsimp [B]; nlinarith [sq_nonneg v]
  have hlog : 0 < log B := log_pos (by linarith)
  have hcont : ContinuousAt inverseLi v := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨min (min v 1) (ε / log B), lt_min (lt_min hv zero_lt_one) (div_pos hε hlog), ?_⟩
    intro w hw
    rw [Real.dist_eq] at hw ⊢
    have hm := lt_min_iff.mp hw
    obtain ⟨hwv, hw1⟩ := lt_min_iff.mp hm.1
    have hw0 : 0 ≤ w := by have := (abs_lt.mp hwv).1; linarith
    have hw2 : w ≤ v+1 := by have := (abs_lt.mp hw1).2; linarith
    obtain ⟨hbv, ev⟩ := inverseLi_spec hv.le
    obtain ⟨hbw, ew⟩ := inverseLi_spec hw0
    have l : (4*(v+1))^2 ≤ B := by dsimp [B]; nlinarith
    have lw : (4*(w+1))^2 ≤ B := by
      dsimp [B]
      exact pow_le_pow_left₀ (by positivity) (by linarith : 4*(w+1) ≤ 4*(v+2)) 2
    have hdiff := inverse_spacing (ha := ⟨hbw.1, hbw.2.trans lw⟩)
      (hb := ⟨hbv.1, hbv.2.trans l⟩)
    rw [ew, ev] at hdiff
    exact hdiff.trans_lt (by rw [mul_comm]; exact (lt_div_iff₀ hlog).mp hm.2)
  have hleft := (inverseLi_spec hv.le).1.1
  have hpos : 1 < inverseLi v := by linarith
  have hd : HasDerivAt Main.li (log (inverseLi v))⁻¹ (inverseLi v) :=
    intervalIntegral.integral_hasDerivAt_right (liIntegrable (by norm_num) hleft)
      Real.measurable_log.inv.stronglyMeasurable.stronglyMeasurableAtFilter
      ((continuousAt_log (by linarith : inverseLi v ≠ 0)).inv₀ (log_pos hpos).ne')
  have hfg : ∀ᶠ w in 𝓝 v, Main.li (inverseLi w) = w :=
    (eventually_gt_nhds hv).mono fun w hw => (inverseLi_spec hw.le).2
  simpa using hd.of_local_left_inverse hcont (inv_ne_zero (log_pos hpos).ne') hfg

/-- The normalized smooth nth-prime source in the logarithmic variable. -/
@[expose] def smoothPrimeSource (u : ℝ) : ℝ := exp (-u) * inverseLi (exp u)

/-- Exact ODE underlying the formal inversion in the frozen-parameter pencil. -/
theorem smoothPrimeSource_equation (u : ℝ) :
    smoothPrimeSource u + deriv smoothPrimeSource u = u + log (smoothPrimeSource u) := by
  have hneg : HasDerivAt (fun v : ℝ => exp (-v)) (-exp (-u)) u := by
    simpa using (hasDerivAt_id u).neg.exp
  have hD := hneg.mul ((inverseLi_hasDerivAt (exp_pos u)).comp u (hasDerivAt_exp u))
  have hd : HasDerivAt smoothPrimeSource
      (-exp (-u) * inverseLi (exp u) + exp (-u) * (log (inverseLi (exp u)) * exp u)) u := by
    change HasDerivAt (fun v : ℝ => exp (-v) * inverseLi (exp v)) _ u
    exact hD
  have hi : 0 < inverseLi (exp u) := by linarith [(inverseLi_spec (exp_pos u).le).1.1]
  rw [hd.deriv, smoothPrimeSource, log_mul (exp_ne_zero _) hi.ne', log_exp, exp_neg]
  field_simp
  ring

/-- Removing the Borel gamma multiplier gives an explicitly differentially algebraic
control: the actual normalized inverse-li function satisfies an autonomous polynomial ODE. -/
theorem smoothPrimeSource_autonomous (u : ℝ) :
    smoothPrimeSource u * deriv (deriv smoothPrimeSource) u +
      smoothPrimeSource u * deriv smoothPrimeSource u - smoothPrimeSource u -
      deriv smoothPrimeSource u = 0 := by
  have hi : 0 < inverseLi (exp u) := by linarith [(inverseLi_spec (exp_pos u).le).1.1]
  have hf : DifferentiableAt ℝ smoothPrimeSource u := by
    change DifferentiableAt ℝ (fun v : ℝ => exp (-v) * inverseLi (exp v)) u
    exact (differentiableAt_id.neg.exp).mul
      ((inverseLi_hasDerivAt (exp_pos u)).differentiableAt.comp u (differentiableAt_exp))
  have hn : smoothPrimeSource u ≠ 0 := mul_ne_zero (exp_ne_zero _) hi.ne'
  have heq : deriv smoothPrimeSource = fun v => v + log (smoothPrimeSource v) - smoothPrimeSource v := by
    funext v
    linarith [smoothPrimeSource_equation v]
  have hd2 := ((hasDerivAt_id u).add (hf.hasDerivAt.log hn)).sub hf.hasDerivAt
  have h2 : deriv (deriv smoothPrimeSource) u =
      1 + deriv smoothPrimeSource u / smoothPrimeSource u - deriv smoothPrimeSource u := by
    conv_lhs => rw [heq]
    exact hd2.deriv
  rw [h2]
  field_simp
  ring

end PakPrimes.NthPrime
end
