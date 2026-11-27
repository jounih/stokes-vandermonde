module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Int.GCD
public import Mathlib.Tactic

/-! # Dyson Rank-Mod-`N` Folded-Cycle Shadow Graph Theorem (All Moduli `N ≥ 2`)

Unconditional Lean 4 formalization from Mathlib (zero placeholders, standard assumptions only)
of the all-moduli Dyson rank shadow-rank theorem for every modulus `N ≥ 2`:

1. **Bringmann–Ono Trigonometric Identity** (`dyson_shadow_trig_identity`):
   $$2 \sin\!\left(\frac{\pi h}{N}\right) \sin\!\left(\frac{(6n+1)\pi h}{N}\right)
     = \cos\!\left(\frac{2\pi(3n)h}{N}\right) - \cos\!\left(\frac{2\pi(3n+1)h}{N}\right)$$
   for all `n, h : ℤ` and `N : ℕ` (with `N ≥ 1`), and invariance of `\cos(2π z h / N)` under
   the folding map `foldMod N hN : ℤ → Fin (N / 2 + 1)` (`cos_two_pi_mul_foldMod`).
2. **Folded-Cycle Shadow Graph & Exact Component Count** (`dysonFoldedGraph`):
   For every `N ≥ 2`, the folded vertex set `Fin (N / 2 + 1)` with edges connecting `[3n]` and
   `[3n + 1]` (`n : ℤ`) has:
   - exact component labeling `dysonCompId N : Fin (N / 2 + 1) → Fin (dysonNumComponents N)`,
     equal to `0` when `¬ 3 ∣ N` and `(v + 1) / 3` when `3 ∣ N`;
   - exact component count `dysonFoldedGraph_connectedComponent_card`:
     `1` when `¬ 3 ∣ N`, and `N / 6 + 1` (equivalently `(N / 3) / 2 + 1`) when `3 ∣ N`;
   - every vertex has a distinct neighbor (`dysonFoldedGraph_exists_adj`), so every connected
     component has cardinality at least `2`.
3. **Exact Linear Rank Formula over Any Field `K`** (`dysonShadowRank_eq`):
   $$\operatorname{finrank}_K \bigl(\operatorname{span}_K \{e_{[3n]} - e_{[3n+1]} : n \in \mathbb{Z}\}\bigr)
     = \begin{cases} N / 2, & \neg(3 \mid N), \\ N / 3, & 3 \mid N. \end{cases}$$
4. **Exact Shadow-Cancellation Characterization & Non-Vanishing of Single Residues**:
   - A folded weight vector `w : Fin (N / 2 + 1) → K` has zero shadow (`w([3n]) = w([3n+1])` for
     all `n : ℤ`) iff `w` is constant on every connected component
     (`mem_shadowKernel_iff_const_on_components` and `mem_shadowKernel_iff_const_on_reachable`).
   - Every individual folded residue indicator `Pi.single v 1` has nonzero shadow
     (`single_vertex_not_mem_shadowKernel`).
   - Explicit `N = 6` verification (`dysonShadowRank_six`, `dysonSix_triple_zero_shadow`):
     `r_6 = 2` with the two lifted triples `{5, 0, 1}` and `{2, 3, 4}` having zero shadow.
5. **Real & Complex Trigonometric Sine-Product Matrix Rank** (`dysonTrigShadowRank_eq`):
   Using discrete cosine orthogonality (`dct_linearIndependent`), the actual real span of the
   Bringmann–Ono sine-product rows `h ↦ 2 sin(π h / N) sin((6n+1) π h / N)` (`h ∈ Fin N`)
   has exact `ℝ`-dimension `if 3 ∣ N then N / 3 else N / 2`.
-/

namespace CubicTheta.AllD

public section

open Real Finset

/-! ### 1. Exact Bringmann–Ono Trigonometric Identity -/

/-- Elementary product-to-difference identity:
`2 sin(x) sin((6n + 1) x) = cos(6 n x) - cos((6n + 2) x)`. -/
theorem two_sin_mul_sin_six_add_one (n : ℤ) (x : ℝ) :
    2 * Real.sin x * Real.sin ((6 * (n : ℝ) + 1) * x) =
      Real.cos (2 * (3 * (n : ℝ)) * x) - Real.cos (2 * (3 * (n : ℝ) + 1) * x) := by
  have h1 : 2 * (3 * (n : ℝ)) * x = (6 * (n : ℝ) + 1) * x - x := by ring
  have h2 : 2 * (3 * (n : ℝ) + 1) * x = (6 * (n : ℝ) + 1) * x + x := by ring
  rw [h1, h2, Real.cos_sub, Real.cos_add]
  ring

/-- Bringmann–Ono shadow trigonometric identity for arbitrary modulus `N`, twist `h`, and mode `n`:
`2 sin(π h / N) sin((6n + 1) π h / N) = cos(2π (3n) h / N) - cos(2π (3n + 1) h / N)`. -/
theorem dyson_shadow_trig_identity (N : ℕ) (n h : ℤ) :
    2 * Real.sin (Real.pi * (h : ℝ) / (N : ℝ)) *
        Real.sin ((6 * (n : ℝ) + 1) * Real.pi * (h : ℝ) / (N : ℝ)) =
      Real.cos (2 * Real.pi * ((3 * n : ℤ) : ℝ) * (h : ℝ) / (N : ℝ)) -
        Real.cos (2 * Real.pi * ((3 * n + 1 : ℤ) : ℝ) * (h : ℝ) / (N : ℝ)) := by
  have hmain := two_sin_mul_sin_six_add_one n (Real.pi * (h : ℝ) / (N : ℝ))
  have ha : (6 * (n : ℝ) + 1) * Real.pi * (h : ℝ) / (N : ℝ) =
      (6 * (n : ℝ) + 1) * (Real.pi * (h : ℝ) / (N : ℝ)) := by ring
  have hb : 2 * Real.pi * ((3 * n : ℤ) : ℝ) * (h : ℝ) / (N : ℝ) =
      2 * (3 * (n : ℝ)) * (Real.pi * (h : ℝ) / (N : ℝ)) := by push_cast; ring
  have hc : 2 * Real.pi * ((3 * n + 1 : ℤ) : ℝ) * (h : ℝ) / (N : ℝ) =
      2 * (3 * (n : ℝ) + 1) * (Real.pi * (h : ℝ) / (N : ℝ)) := by push_cast; ring
  rw [ha, hb, hc]
  exact hmain

/-! ### 2. Folding Map `foldMod : ℤ → Fin (N / 2 + 1)` & Cosine Invariance -/

/-- Folding an integer modulo `N` onto the sign-quotient vertex set `{0, 1, ..., ⌊N/2⌋}`. -/
def foldMod (N : ℕ) (hN : 0 < N) (z : ℤ) : Fin (N / 2 + 1) :=
  let r : ℕ := (z % (N : ℤ)).toNat
  ⟨min r (N - r), by
    have hr_lt : r < N := by
      have hpos : (0 : ℤ) < (N : ℤ) := Int.natCast_pos.mpr hN
      have hlt : z % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos z hpos
      have hnn : 0 ≤ z % (N : ℤ) := Int.emod_nonneg z (ne_of_gt hpos)
      omega
    omega⟩

private lemma foldMod_val (N : ℕ) (hN : 0 < N) (z : ℤ) :
    (foldMod N hN z : ℕ) = min (z % (N : ℤ)).toNat (N - (z % (N : ℤ)).toNat) := rfl

/-- `foldMod N hN` depends only on `z % N`. -/
theorem foldMod_eq_of_emod_eq {N : ℕ} (hN : 0 < N) {a b : ℤ}
    (h : a % (N : ℤ) = b % (N : ℤ)) :
    foldMod N hN a = foldMod N hN b := by
  ext
  simp [foldMod_val, h]

/-- `foldMod N hN` is periodic with period `N`. -/
theorem foldMod_add_mul (N : ℕ) (hN : 0 < N) (z k : ℤ) :
    foldMod N hN (z + k * (N : ℤ)) = foldMod N hN z :=
  foldMod_eq_of_emod_eq hN (Int.add_mul_emod_self_right z k (N : ℤ))

/-- `foldMod N hN` is invariant under negation: `[-z] = [z]`. -/
theorem foldMod_neg (N : ℕ) (hN : 0 < N) (z : ℤ) :
    foldMod N hN (-z) = foldMod N hN z := by
  ext
  simp only [foldMod_val]
  have hNpos : (0 : ℤ) < (N : ℤ) := Int.natCast_pos.mpr hN
  have hnn : 0 ≤ z % (N : ℤ) := Int.emod_nonneg z (ne_of_gt hNpos)
  have hlt : z % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos z hNpos
  set r : ℤ := z % (N : ℤ)
  have hr_eq : z = (N : ℤ) * (z / (N : ℤ)) + r := (Int.mul_ediv_add_emod z (N : ℤ)).symm
  by_cases hr0 : r = 0
  · have hneg : (-z) % (N : ℤ) = 0 := by
      have h1 : -z = (-(z / (N : ℤ))) * (N : ℤ) := by linarith
      rw [h1, Int.mul_emod_left]
    simp [hneg, hr0]
  · have hr_pos : 0 < r := lt_of_le_of_ne hnn (Ne.symm hr0)
    have hneg : (-z) % (N : ℤ) = (N : ℤ) - r := by
      have h1 : -z = ((N : ℤ) - r) + (-(z / (N : ℤ)) - 1) * (N : ℤ) := by linarith
      rw [h1, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hneg]
    have hto1 : ((N : ℤ) - r).toNat = N - r.toNat := by omega
    rw [hto1]
    have hto2 : N - (N - r.toNat) = r.toNat := by omega
    rw [hto2, min_comm]

/-- `foldMod` fixes every vertex `v ∈ Fin (N / 2 + 1)`. -/
theorem foldMod_of_fin (N : ℕ) (hN : 0 < N) (v : Fin (N / 2 + 1)) :
    foldMod N hN (v : ℤ) = v := by
  ext
  simp only [foldMod_val]
  have hv_le : (v : ℕ) ≤ N / 2 := Nat.lt_succ_iff.mp v.isLt
  have hmod : ((v : ℕ) : ℤ) % (N : ℤ) = ((v : ℕ) : ℤ) :=
    Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)
  rw [hmod, Int.toNat_natCast]
  omega

/-- For any `z : ℤ`, either `z ≡ foldMod z (mod N)` or `z ≡ -foldMod z (mod N)`. -/
theorem foldMod_eq_or_neg_mod (N : ℕ) (hN : 0 < N) (z : ℤ) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∃ q : ℤ, z = s * ((foldMod N hN z : ℕ) : ℤ) + q * (N : ℤ) := by
  have hNpos : (0 : ℤ) < (N : ℤ) := Int.natCast_pos.mpr hN
  have hnn : 0 ≤ z % (N : ℤ) := Int.emod_nonneg z (ne_of_gt hNpos)
  have hlt : z % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos z hNpos
  set r : ℕ := (z % (N : ℤ)).toNat
  have hr_cast : (r : ℤ) = z % (N : ℤ) := Int.toNat_of_nonneg hnn
  have hz_eq : z = (r : ℤ) + (z / (N : ℤ)) * (N : ℤ) := by
    have := Int.mul_ediv_add_emod z (N : ℤ)
    linarith
  have hfold : (foldMod N hN z : ℕ) = min r (N - r) := rfl
  by_cases hle : r ≤ N - r
  · refine ⟨1, Or.inl rfl, z / (N : ℤ), ?_⟩
    rw [hfold, min_eq_left hle, one_mul]
    exact hz_eq
  · refine ⟨-1, Or.inr rfl, z / (N : ℤ) + 1, ?_⟩
    have hge : N - r ≤ r := by omega
    rw [hfold, min_eq_right hge]
    have hsub : ((N - r : ℕ) : ℤ) = (N : ℤ) - (r : ℤ) := by omega
    rw [hsub]
    linarith

/-- Cosine values `\cos(2π z h / N)` depend only on the folded vertex `foldMod N hN z`. -/
theorem cos_two_pi_mul_foldMod (N : ℕ) (hN : 0 < N) (z h : ℤ) :
    Real.cos (2 * Real.pi * (z : ℝ) * (h : ℝ) / (N : ℝ)) =
      Real.cos (2 * Real.pi * ((foldMod N hN z : ℕ) : ℝ) * (h : ℝ) / (N : ℝ)) := by
  obtain ⟨s, hs, q, hz⟩ := foldMod_eq_or_neg_mod N hN z
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hzR : (z : ℝ) = (s : ℝ) * ((foldMod N hN z : ℕ) : ℝ) + (q : ℝ) * (N : ℝ) := by
    exact_mod_cast hz
  have harg : 2 * Real.pi * (z : ℝ) * (h : ℝ) / (N : ℝ) =
      (s : ℝ) * (2 * Real.pi * ((foldMod N hN z : ℕ) : ℝ) * (h : ℝ) / (N : ℝ)) +
        ((q * h : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [hzR]
    push_cast
    field_simp [hNne]
  rw [harg, Real.cos_add_int_mul_two_pi]
  rcases hs with rfl | rfl
  · simp
  · simp [Real.cos_neg]

/-! ### 3. Component Count, Explicit Component Map & Folded-Cycle Graph -/

/-- Exact number of connected components of the Dyson folded-cycle shadow graph:
`1` when `¬ (3 ∣ N)`, and `N / 6 + 1` (equivalently `(N / 3) / 2 + 1`) when `3 ∣ N`. -/
def dysonNumComponents (N : ℕ) : ℕ :=
  if 3 ∣ N then N / 6 + 1 else 1

/-- Exact Dyson shadow rank formula: `N / 3` when `3 ∣ N`, and `N / 2` when `¬ (3 ∣ N)`. -/
def dysonShadowRank (N : ℕ) : ℕ :=
  if 3 ∣ N then N / 3 else N / 2

/-- Vertex count minus component count equals `dysonShadowRank N` for every `N : ℕ`. -/
theorem dyson_vertices_sub_components (N : ℕ) :
    N / 2 + 1 - dysonNumComponents N = dysonShadowRank N := by
  unfold dysonNumComponents dysonShadowRank
  split_ifs with h3
  · rcases h3 with ⟨m, rfl⟩
    omega
  · omega

/-- Component count equals `(N / 3) / 2 + 1` when `3 ∣ N`. -/
theorem dysonNumComponents_of_dvd {N : ℕ} (h3 : 3 ∣ N) :
    dysonNumComponents N = (N / 3) / 2 + 1 := by
  simp only [dysonNumComponents, h3, ↓reduceIte]
  omega

/-- Component count equals `1` when `¬ (3 ∣ N)`. -/
theorem dysonNumComponents_of_not_dvd {N : ℕ} (h3 : ¬ 3 ∣ N) :
    dysonNumComponents N = 1 := by
  simp only [dysonNumComponents, h3, ↓reduceIte]

/-- Explicit component label for every folded vertex `v ∈ Fin (N / 2 + 1)`:
`0` when `¬ 3 ∣ N`, and `(v + 1) / 3` when `3 ∣ N`. -/
def dysonCompId (N : ℕ) (v : Fin (N / 2 + 1)) : Fin (dysonNumComponents N) :=
  if h3 : 3 ∣ N then
    ⟨((v : ℕ) + 1) / 3, by
      simp only [dysonNumComponents, h3, ↓reduceIte]
      rcases h3 with ⟨m, rfl⟩
      have hv : (v : ℕ) ≤ (3 * m) / 2 := Nat.lt_succ_iff.mp v.isLt
      omega⟩
  else
    ⟨0, by simp only [dysonNumComponents, h3, ↓reduceIte]; omega⟩

/-- Canonical root vertex in each component: `0` when `¬ 3 ∣ N`, and `3 * c` when `3 ∣ N`. -/
def dysonCompRoot (N : ℕ) (c : Fin (dysonNumComponents N)) : Fin (N / 2 + 1) :=
  if h3 : 3 ∣ N then
    ⟨3 * (c : ℕ), by
      have hc : (c : ℕ) < dysonNumComponents N := c.isLt
      simp only [dysonNumComponents, h3, ↓reduceIte] at hc
      rcases h3 with ⟨m, rfl⟩
      omega⟩
  else
    ⟨0, Nat.succ_pos _⟩

/-- Every canonical component root maps back to its component label. -/
theorem dysonCompId_compRoot (N : ℕ) (c : Fin (dysonNumComponents N)) :
    dysonCompId N (dysonCompRoot N c) = c := by
  ext
  unfold dysonCompId dysonCompRoot
  split_ifs with h3
  · dsimp only
    omega
  · have hc : (c : ℕ) < dysonNumComponents N := c.isLt
    simp only [dysonNumComponents, h3, ↓reduceIte] at hc
    dsimp only
    omega

/-- Every shadow edge `{[3n], [3n + 1]}` connects two vertices in the SAME component. -/
theorem dysonCompId_three_mul_eq (N : ℕ) (hN : 0 < N) (n : ℤ) :
    dysonCompId N (foldMod N hN (3 * n)) = dysonCompId N (foldMod N hN (3 * n + 1)) := by
  ext
  unfold dysonCompId
  split_ifs with h3
  · dsimp only
    rcases h3 with ⟨m, rfl⟩
    have hm : 0 < m := by omega
    have hNpos : (0 : ℤ) < ((3 * m : ℕ) : ℤ) := by omega
    set r : ℤ := (3 * n) % ((3 * m : ℕ) : ℤ)
    have hr_nn : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hNpos)
    have hr_lt : r < ((3 * m : ℕ) : ℤ) := Int.emod_lt_of_pos _ hNpos
    have h3_dvd_r : (3 : ℤ) ∣ r := by
      have hdiv : (3 : ℤ) ∣ (3 * n) - ((3 * m : ℕ) : ℤ) * ((3 * n) / ((3 * m : ℕ) : ℤ)) := by
        refine ⟨n - (m : ℤ) * ((3 * n) / ((3 * m : ℕ) : ℤ)), ?_⟩
        push_cast; ring
      have heq : r = (3 * n) - ((3 * m : ℕ) : ℤ) * ((3 * n) / ((3 * m : ℕ) : ℤ)) := by
        have := Int.mul_ediv_add_emod (3 * n) ((3 * m : ℕ) : ℤ)
        linarith
      rwa [heq]
    rcases h3_dvd_r with ⟨j, hj⟩
    have hj_nn : 0 ≤ j := by omega
    have hj_lt : j < (m : ℤ) := by omega
    have hr1 : (3 * n + 1) % ((3 * m : ℕ) : ℤ) = r + 1 := by
      have h1 : 3 * n + 1 = (r + 1) + ((3 * n) / ((3 * m : ℕ) : ℤ)) * ((3 * m : ℕ) : ℤ) := by
        have := Int.mul_ediv_add_emod (3 * n) ((3 * m : ℕ) : ℤ)
        linarith
      rw [h1, Int.add_mul_emod_self_right, Int.emod_eq_of_lt (by omega) (by omega)]
    simp only [foldMod_val, hr1]
    have hr_toNat : r.toNat = 3 * j.toNat := by omega
    have hr1_toNat : (r + 1).toNat = 3 * j.toNat + 1 := by omega
    rw [hr_toNat, hr1_toNat]
    omega
  · rfl

/-- The undirected Dyson folded-cycle shadow graph on `Fin (N / 2 + 1)`:
two distinct folded vertices `u, v` are adjacent iff `{u, v} = {[3n], [3n + 1]}` for some `n : ℤ`. -/
def dysonFoldedGraph (N : ℕ) (hN : 0 < N) : SimpleGraph (Fin (N / 2 + 1)) where
  Adj u v :=
    u ≠ v ∧ ∃ n : ℤ,
      (foldMod N hN (3 * n) = u ∧ foldMod N hN (3 * n + 1) = v) ∨
      (foldMod N hN (3 * n) = v ∧ foldMod N hN (3 * n + 1) = u)
  symm := ⟨fun _ _ h ↦ by
    rcases h with ⟨hne, n, h | h⟩
    · exact ⟨hne.symm, n, Or.inr h⟩
    · exact ⟨hne.symm, n, Or.inl h⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- When `¬ (3 ∣ N)`, every consecutive pair `(v, v + 1)` in `Fin (N / 2 + 1)` is realized by a
single Bringmann–Ono shadow edge `([3n], [3n + 1])`. -/
theorem exists_shadow_edge_consecutive {N : ℕ} (hN : 0 < N) (h3 : ¬ 3 ∣ N)
    {k : ℕ} (hk : k + 1 ≤ N / 2) :
    ∃ n : ℤ,
      foldMod N hN (3 * n) = ⟨k, by omega⟩ ∧
      foldMod N hN (3 * n + 1) = ⟨k + 1, by omega⟩ := by
  have hcop : Nat.Coprime 3 N := (Nat.prime_three.coprime_iff_not_dvd).mpr h3
  have hbez : (1 : ℤ) = (3 : ℤ) * Nat.gcdA 3 N + (N : ℤ) * Nat.gcdB 3 N := by
    have h := Nat.gcd_eq_gcd_ab 3 N
    rw [hcop.gcd_eq_one] at h
    simpa using h
  refine ⟨Nat.gcdA 3 N * (k : ℤ), ?_, ?_⟩
  · have h1 : 3 * (Nat.gcdA 3 N * (k : ℤ)) =
        ((k : ℕ) : ℤ) + (-(Nat.gcdB 3 N * (k : ℤ))) * (N : ℤ) := by
      have : (3 : ℤ) * Nat.gcdA 3 N = 1 - (N : ℤ) * Nat.gcdB 3 N := by linarith
      calc
        3 * (Nat.gcdA 3 N * (k : ℤ)) = (3 * Nat.gcdA 3 N) * (k : ℤ) := by ring
        _ = (1 - (N : ℤ) * Nat.gcdB 3 N) * (k : ℤ) := by rw [this]
        _ = ((k : ℕ) : ℤ) + (-(Nat.gcdB 3 N * (k : ℤ))) * (N : ℤ) := by ring
    rw [h1, foldMod_add_mul]
    exact foldMod_of_fin N hN ⟨k, by omega⟩
  · have h2 : 3 * (Nat.gcdA 3 N * (k : ℤ)) + 1 =
        (((k + 1 : ℕ) : ℤ)) + (-(Nat.gcdB 3 N * (k : ℤ))) * (N : ℤ) := by
      have : (3 : ℤ) * Nat.gcdA 3 N = 1 - (N : ℤ) * Nat.gcdB 3 N := by linarith
      push_cast
      calc
        3 * (Nat.gcdA 3 N * (k : ℤ)) + 1 = (3 * Nat.gcdA 3 N) * (k : ℤ) + 1 := by ring
        _ = (1 - (N : ℤ) * Nat.gcdB 3 N) * (k : ℤ) + 1 := by rw [this]
        _ = (k : ℤ) + 1 + (-(Nat.gcdB 3 N * (k : ℤ))) * (N : ℤ) := by ring
    rw [h2, foldMod_add_mul]
    exact foldMod_of_fin N hN ⟨k + 1, by omega⟩

/-- When `3 ∣ N`, every non-root vertex `v` is directly connected to its component root `3 * c`
by either edge `n = c` (for `v = 3c + 1`) or edge `n = -c` (for `v = 3c - 1`). -/
theorem exists_shadow_edge_to_root_of_dvd {N : ℕ} (hN : 0 < N) (h3 : 3 ∣ N)
    (v : Fin (N / 2 + 1)) (hne : v ≠ dysonCompRoot N (dysonCompId N v)) :
    ∃ n : ℤ,
      foldMod N hN (3 * n) = dysonCompRoot N (dysonCompId N v) ∧
      foldMod N hN (3 * n + 1) = v := by
  set c : Fin (dysonNumComponents N) := dysonCompId N v
  have hc_val : (c : ℕ) = ((v : ℕ) + 1) / 3 := by
    simp [c, dysonCompId, h3]
  have hroot_val : (dysonCompRoot N c : ℕ) = 3 * (c : ℕ) := by
    simp [dysonCompRoot, h3]
  have hv_ne_root : (v : ℕ) ≠ 3 * (c : ℕ) := by
    intro h
    apply hne
    ext
    omega
  have hv_cases : (v : ℕ) = 3 * (c : ℕ) + 1 ∨ (v : ℕ) + 1 = 3 * (c : ℕ) := by
    omega
  rcases hv_cases with hplus | hminus
  · refine ⟨(c : ℤ), ?_, ?_⟩
    · have h1 : (3 * (c : ℤ)) = ((dysonCompRoot N c : ℕ) : ℤ) := by
        rw [hroot_val]; push_cast; ring
      rw [h1]
      exact foldMod_of_fin N hN (dysonCompRoot N c)
    · have h2 : (3 * (c : ℤ) + 1) = ((v : ℕ) : ℤ) := by
        rw [hplus]; push_cast; ring
      rw [h2]
      exact foldMod_of_fin N hN v
  · refine ⟨-(c : ℤ), ?_, ?_⟩
    · have h1 : 3 * (-(c : ℤ)) = -((dysonCompRoot N c : ℕ) : ℤ) := by
        rw [hroot_val]; push_cast; ring
      rw [h1, foldMod_neg]
      exact foldMod_of_fin N hN (dysonCompRoot N c)
    · have h2 : 3 * (-(c : ℤ)) + 1 = -((v : ℕ) : ℤ) := by
        have : (3 * (c : ℕ) : ℤ) = ((v : ℕ) : ℤ) + 1 := by exact_mod_cast hminus.symm
        linarith
      rw [h2, foldMod_neg]
      exact foldMod_of_fin N hN v

/-- Every vertex `v` is reachable from its canonical component root in `dysonFoldedGraph N hN`. -/
theorem dysonFoldedGraph_reachable_root {N : ℕ} (hN : 0 < N) (v : Fin (N / 2 + 1)) :
    (dysonFoldedGraph N hN).Reachable (dysonCompRoot N (dysonCompId N v)) v := by
  by_cases h3 : 3 ∣ N
  · by_cases hEq : v = dysonCompRoot N (dysonCompId N v)
    · rw [← hEq]
    · obtain ⟨n, h1, h2⟩ := exists_shadow_edge_to_root_of_dvd hN h3 v hEq
      exact SimpleGraph.Adj.reachable ⟨Ne.symm hEq, n, Or.inl ⟨h1, h2⟩⟩
  · have hroot0 : dysonCompRoot N (dysonCompId N v) = ⟨0, Nat.succ_pos _⟩ := by
      ext; simp [dysonCompRoot, h3]
    rw [hroot0]
    clear hroot0
    rcases v with ⟨k, hk⟩
    induction k with
    | zero => exact SimpleGraph.Reachable.refl _
    | succ m ih =>
      have hm_lt : m < N / 2 + 1 := by omega
      have hreach_m := ih hm_lt
      obtain ⟨n, h1, h2⟩ := exists_shadow_edge_consecutive hN h3 (k := m) (by omega)
      have hadj : (dysonFoldedGraph N hN).Adj ⟨m, hm_lt⟩ ⟨m + 1, hk⟩ :=
        ⟨by simp, n, Or.inl ⟨h1, h2⟩⟩
      exact hreach_m.trans hadj.reachable

/-- Two vertices lie in the same connected component of `dysonFoldedGraph N hN` if and only if
they have the same `dysonCompId`. -/
theorem dysonFoldedGraph_reachable_iff {N : ℕ} (hN : 0 < N) (u v : Fin (N / 2 + 1)) :
    (dysonFoldedGraph N hN).Reachable u v ↔ dysonCompId N u = dysonCompId N v := by
  constructor
  · intro h
    obtain ⟨w⟩ := h
    induction w with
    | nil => rfl
    | @cons a b c hab _ ih =>
      have hcomp_ab : dysonCompId N a = dysonCompId N b := by
        rcases hab with ⟨_, n, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
        · exact dysonCompId_three_mul_eq N hN n
        · exact (dysonCompId_three_mul_eq N hN n).symm
      exact hcomp_ab.trans ih
  · intro hcomp
    have hu := dysonFoldedGraph_reachable_root hN u
    have hv := dysonFoldedGraph_reachable_root hN v
    rw [hcomp] at hu
    exact hu.symm.trans hv

/-- Exact equivalence between connected components of `dysonFoldedGraph N hN` and
`Fin (dysonNumComponents N)`. -/
noncomputable def dysonConnectedComponentEquiv (N : ℕ) (hN : 0 < N) :
    (dysonFoldedGraph N hN).ConnectedComponent ≃ Fin (dysonNumComponents N) :=
  Equiv.ofBijective
    (SimpleGraph.ConnectedComponent.lift (dysonCompId N)
      (fun u v huv _ ↦ (dysonFoldedGraph_reachable_iff hN u v).mp ⟨huv⟩))
    ⟨by
      intro a b hab
      refine SimpleGraph.ConnectedComponent.ind (fun u ↦ ?_) a hab
      refine SimpleGraph.ConnectedComponent.ind (fun v huv ↦ ?_) b
      exact SimpleGraph.ConnectedComponent.eq.mpr ((dysonFoldedGraph_reachable_iff hN u v).mpr huv),
     by
      intro c
      exact ⟨(dysonFoldedGraph N hN).connectedComponentMk (dysonCompRoot N c),
        dysonCompId_compRoot N c⟩⟩

/-- Exact connected-components count of `dysonFoldedGraph N hN`:
`1` when `¬ (3 ∣ N)`, and `N / 6 + 1` (equivalently `(N / 3) / 2 + 1`) when `3 ∣ N`. -/
theorem dysonFoldedGraph_connectedComponent_card {N : ℕ} (hN : 0 < N) :
    Nat.card (dysonFoldedGraph N hN).ConnectedComponent = dysonNumComponents N := by
  rw [Nat.card_congr (dysonConnectedComponentEquiv N hN), Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- For every `N ≥ 2` and every folded vertex `u ∈ Fin (N / 2 + 1)`, there exists a distinct
neighbor `v ≠ u` adjacent to `u` in `dysonFoldedGraph N hN` (so every component has size ≥ 2). -/
theorem dysonFoldedGraph_exists_adj {N : ℕ} (hN : 2 ≤ N) (u : Fin (N / 2 + 1)) :
    ∃ v : Fin (N / 2 + 1), (dysonFoldedGraph N (by omega)).Adj u v := by
  have hpos : 0 < N := by omega
  by_cases h3 : 3 ∣ N
  · by_cases hEq : u = dysonCompRoot N (dysonCompId N u)
    · set c := dysonCompId N u
      have hroot_val : (dysonCompRoot N c : ℕ) = 3 * (c : ℕ) := by
        simp [dysonCompRoot, h3]
      by_cases hc0 : (c : ℕ) = 0
      · -- Root `0` is adjacent to `1` via `n = 0` (since `N ≥ 3`, `1 ≤ N / 2`).
        have h1_lt : 1 < N / 2 + 1 := by omega
        refine ⟨⟨1, h1_lt⟩, ?_⟩
        have hu0 : u = ⟨0, Nat.succ_pos _⟩ := by
          ext; rw [hEq, hroot_val, hc0]
        rw [hu0]
        refine ⟨by simp, 0, Or.inl ⟨?_, ?_⟩⟩
        · simpa using foldMod_of_fin N hpos ⟨0, Nat.succ_pos _⟩
        · simpa using foldMod_of_fin N hpos ⟨1, h1_lt⟩
      · -- Root `3c` (`c ≥ 1`) is adjacent to `3c - 1` via `n = -c`.
        have hv_lt : 3 * (c : ℕ) - 1 < N / 2 + 1 := by
          have := (dysonCompRoot N c).isLt
          omega
        let v : Fin (N / 2 + 1) := ⟨3 * (c : ℕ) - 1, hv_lt⟩
        have hv_comp : dysonCompId N v = c := by
          ext; simp [dysonCompId, h3, v]; omega
        have hv_ne : v ≠ dysonCompRoot N (dysonCompId N v) := by
          intro h
          have hv_eq := congrArg Fin.val h
          rw [hv_comp, hroot_val] at hv_eq
          dsimp [v] at hv_eq
          omega
        obtain ⟨n, h1, h2⟩ := exists_shadow_edge_to_root_of_dvd hpos h3 v hv_ne
        rw [hv_comp] at h1
        rw [← hEq] at h1
        refine ⟨v, ?_, n, Or.inl ⟨h1, h2⟩⟩
        intro huv
        rw [hEq, ← hv_comp] at huv
        exact hv_ne huv.symm
    · obtain ⟨n, h1, h2⟩ := exists_shadow_edge_to_root_of_dvd hpos h3 u hEq
      exact ⟨dysonCompRoot N (dysonCompId N u), hEq, n, Or.inr ⟨h1, h2⟩⟩
  · -- `¬ 3 ∣ N` and `N ≥ 2`: `N / 2 ≥ 1`, so either `u + 1 ≤ N / 2` or `u ≥ 1`.
    rcases u with ⟨k, hk⟩
    by_cases hk0 : k = 0
    · subst hk0
      obtain ⟨n, h1, h2⟩ := exists_shadow_edge_consecutive hpos h3 (k := 0) (by omega)
      exact ⟨⟨1, by omega⟩, by simp, n, Or.inl ⟨h1, h2⟩⟩
    · obtain ⟨n, h1, h2⟩ := exists_shadow_edge_consecutive hpos h3 (k := k - 1) (by omega)
      have hkm : k - 1 + 1 = k := by omega
      refine ⟨⟨k - 1, by omega⟩, ?_, n, Or.inr ⟨h1, ?_⟩⟩
      · intro h; have := congrArg Fin.val h; dsimp at this; omega
      · convert h2 using 1; ext; exact hkm.symm

/-! ### 4. Exact Linear Rank Formula & Shadow-Cancellation Kernel over Any Field `K` -/

section LinearAlgebra

variable (K : Type*) [Field K]

/-- The `n`-th Bringmann–Ono shadow row vector `e_{[3n]} - e_{[3n+1]}` in `Fin (N / 2 + 1) → K`. -/
noncomputable def shadowEdge (N : ℕ) (hN : 0 < N) (n : ℤ) : Fin (N / 2 + 1) → K :=
  Pi.single (foldMod N hN (3 * n)) (1 : K) - Pi.single (foldMod N hN (3 * n + 1)) (1 : K)

/-- The `K`-linear span of all Bringmann–Ono shadow row vectors `{e_{[3n]} - e_{[3n+1]} : n ∈ ℤ}`. -/
noncomputable def shadowRowSpan (N : ℕ) (hN : 0 < N) : Submodule K (Fin (N / 2 + 1) → K) :=
  Submodule.span K (Set.range (shadowEdge K N hN))

/-- Component-sum linear map `Φ : (Fin (N / 2 + 1) → K) →ₗ[K] (Fin (dysonNumComponents N) → K)`
summing coordinates over each connected component of `dysonFoldedGraph N hN`. -/
def componentSumMap (N : ℕ) :
    (Fin (N / 2 + 1) → K) →ₗ[K] (Fin (dysonNumComponents N) → K) where
  toFun x c := ∑ v ∈ Finset.univ.filter (fun v ↦ dysonCompId N v = c), x v
  map_add' x y := by
    ext c; simp [Finset.sum_add_distrib]
  map_smul' a x := by
    ext c; simp [Finset.mul_sum]

/-- `componentSumMap K N` is surjective (witnessed by canonical component roots). -/
theorem componentSumMap_surjective (N : ℕ) :
    Function.Surjective (componentSumMap K N) := by
  intro y
  refine ⟨fun v ↦ ∑ c : Fin (dysonNumComponents N),
    (Pi.single (M := fun _ ↦ K) (dysonCompRoot N c) (y c)) v, ?_⟩
  ext c₀
  simp only [componentSumMap, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single c₀]
  · have hmem : dysonCompRoot N c₀ ∈ Finset.univ.filter (fun v ↦ dysonCompId N v = c₀) := by
      simp [dysonCompId_compRoot]
    rw [Finset.sum_eq_single (dysonCompRoot N c₀)]
    · simp
    · intro v _ hne; simp [Pi.single_eq_of_ne hne]
    · intro hnot; exact absurd hmem hnot
  · intro c _ hcne
    apply Finset.sum_eq_zero
    intro v hv
    have hv_ne : v ≠ dysonCompRoot N c := by
      intro heq
      have h1 : dysonCompId N v = c₀ := (Finset.mem_filter.mp hv).2
      rw [heq, dysonCompId_compRoot] at h1
      exact hcne h1
    simp [Pi.single_eq_of_ne hv_ne]
  · intro hnot; exact absurd (Finset.mem_univ c₀) hnot

private lemma single_sub_single_root_mem_shadowRowSpan (N : ℕ) (hN : 0 < N)
    (v : Fin (N / 2 + 1)) :
    Pi.single v (1 : K) - Pi.single (dysonCompRoot N (dysonCompId N v)) (1 : K) ∈
      shadowRowSpan K N hN := by
  by_cases h3 : 3 ∣ N
  · by_cases hEq : v = dysonCompRoot N (dysonCompId N v)
    · rw [← hEq, sub_self]; exact Submodule.zero_mem _
    · obtain ⟨n, h1, h2⟩ := exists_shadow_edge_to_root_of_dvd hN h3 v hEq
      have hmem : shadowEdge K N hN n ∈ shadowRowSpan K N hN :=
        Submodule.subset_span ⟨n, rfl⟩
      have hneg := Submodule.neg_mem _ hmem
      have hrew : -shadowEdge K N hN n =
          Pi.single v (1 : K) - Pi.single (dysonCompRoot N (dysonCompId N v)) (1 : K) := by
        simp [shadowEdge, h1, h2]
      rwa [← hrew]
  · have hroot0 : dysonCompRoot N (dysonCompId N v) = ⟨0, Nat.succ_pos _⟩ := by
      ext; simp [dysonCompRoot, h3]
    rw [hroot0]
    clear hroot0
    rcases v with ⟨k, hk⟩
    induction k with
    | zero =>
      rw [sub_self]; exact Submodule.zero_mem _
    | succ m ih =>
      have hm_lt : m < N / 2 + 1 := by omega
      have hprev := ih hm_lt
      obtain ⟨n, h1, h2⟩ := exists_shadow_edge_consecutive hN h3 (k := m) (by omega)
      have hedge : shadowEdge K N hN n ∈ shadowRowSpan K N hN :=
        Submodule.subset_span ⟨n, rfl⟩
      have hstep : Pi.single (⟨m + 1, hk⟩ : Fin (N / 2 + 1)) (1 : K) -
          Pi.single (⟨m, hm_lt⟩ : Fin (N / 2 + 1)) (1 : K) ∈ shadowRowSpan K N hN := by
        have hneg := Submodule.neg_mem _ hedge
        have hrew : -shadowEdge K N hN n =
            Pi.single (⟨m + 1, hk⟩ : Fin (N / 2 + 1)) (1 : K) -
              Pi.single (⟨m, hm_lt⟩ : Fin (N / 2 + 1)) (1 : K) := by
          simp [shadowEdge, h1, h2]
        rwa [← hrew]
      have hadd := Submodule.add_mem _ hstep hprev
      have htel : (Pi.single (M := fun _ ↦ K) (⟨m + 1, hk⟩ : Fin (N / 2 + 1)) (1 : K) -
          Pi.single (M := fun _ ↦ K) (⟨m, hm_lt⟩ : Fin (N / 2 + 1)) (1 : K)) +
          (Pi.single (M := fun _ ↦ K) (⟨m, hm_lt⟩ : Fin (N / 2 + 1)) (1 : K) -
            Pi.single (M := fun _ ↦ K) (⟨0, Nat.succ_pos _⟩ : Fin (N / 2 + 1)) (1 : K)) =
          Pi.single (M := fun _ ↦ K) (⟨m + 1, hk⟩ : Fin (N / 2 + 1)) (1 : K) -
            Pi.single (M := fun _ ↦ K) (⟨0, Nat.succ_pos _⟩ : Fin (N / 2 + 1)) (1 : K) := by
        abel
      rwa [← htel]

/-- Exact subspace characterization: `shadowRowSpan K N hN` is precisely the kernel of the
component-sum linear map `componentSumMap K N`. -/
theorem shadowRowSpan_eq_ker_componentSumMap (N : ℕ) (hN : 0 < N) :
    shadowRowSpan K N hN = LinearMap.ker (componentSumMap K N) := by
  apply le_antisymm
  · rw [shadowRowSpan, Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    ext c
    simp only [componentSumMap, shadowEdge, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
      Finset.sum_sub_distrib, Pi.zero_apply]
    have hcomp := dysonCompId_three_mul_eq N hN n
    have hsum_single : ∀ u : Fin (N / 2 + 1),
        ∑ v ∈ Finset.univ.filter (fun v ↦ dysonCompId N v = c), Pi.single u (1 : K) v =
          if dysonCompId N u = c then (1 : K) else 0 := by
      intro u
      by_cases hu : dysonCompId N u = c
      · simp only [hu, ↓reduceIte]
        rw [Finset.sum_eq_single u]
        · simp
        · intro v _ hne; simp [Pi.single_eq_of_ne hne]
        · intro hnot; exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ u, hu⟩) hnot
      · simp only [hu, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro v hv
        have hne : v ≠ u := fun h ↦ hu (h ▸ (Finset.mem_filter.mp hv).2)
        simp [Pi.single_eq_of_ne hne]
    rw [hsum_single, hsum_single, hcomp, sub_self]
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have hdecomp : x = ∑ v : Fin (N / 2 + 1),
        x v • (Pi.single v (1 : K) - Pi.single (dysonCompRoot N (dysonCompId N v)) (1 : K)) := by
      ext u
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
        Finset.sum_sub_distrib]
      have h1 : ∑ v : Fin (N / 2 + 1), x v * (Pi.single (M := fun _ ↦ K) v (1 : K)) u = x u := by
        rw [Finset.sum_eq_single u]
        · simp
        · intro v _ hne; simp [Pi.single_eq_of_ne (Ne.symm hne)]
        · intro hnot; exact absurd (Finset.mem_univ u) hnot
      have h2 : ∑ v : Fin (N / 2 + 1),
          x v * (Pi.single (M := fun _ ↦ K) (dysonCompRoot N (dysonCompId N v)) (1 : K)) u = 0 := by
        by_cases hroot : u = dysonCompRoot N (dysonCompId N u)
        · have hterm : ∀ v : Fin (N / 2 + 1),
              x v * (Pi.single (M := fun _ ↦ K) (dysonCompRoot N (dysonCompId N v)) (1 : K)) u =
                if dysonCompId N v = dysonCompId N u then x v else 0 := by
            intro v
            by_cases hc : dysonCompId N v = dysonCompId N u
            · simp only [hc, ↓reduceIte, ← hroot]; simp
            · simp only [hc, ↓reduceIte]
              have hne : u ≠ dysonCompRoot N (dysonCompId N v) := by
                intro heq
                have := congrArg (dysonCompId N) heq
                rw [dysonCompId_compRoot] at this
                exact hc this.symm
              simp [Pi.single_eq_of_ne hne]
          simp_rw [hterm]
          rw [← Finset.sum_filter]
          have hxc := congrFun hx (dysonCompId N u)
          simpa [componentSumMap] using hxc
        · apply Finset.sum_eq_zero
          intro v _
          have hne : u ≠ dysonCompRoot N (dysonCompId N v) := by
            intro heq
            have hc := congrArg (dysonCompId N) heq
            rw [dysonCompId_compRoot] at hc
            exact hroot (hc ▸ heq)
          simp [Pi.single_eq_of_ne hne]
      rw [h1, h2, sub_zero]
    rw [hdecomp]
    exact Submodule.sum_mem _ (fun v _ ↦
      Submodule.smul_mem _ _ (single_sub_single_root_mem_shadowRowSpan K N hN v))

/-- **Exact All-Moduli Dyson Shadow Rank Formula** over ANY field `K`:
for every modulus `N ≥ 2` (in fact every `N ≥ 1`),
`finrank K (shadowRowSpan K N hN) = if 3 ∣ N then N / 3 else N / 2`. -/
theorem dysonShadowRank_eq (N : ℕ) (hN : 0 < N) :
    Module.finrank K (shadowRowSpan K N hN) = dysonShadowRank N := by
  rw [shadowRowSpan_eq_ker_componentSumMap K N hN]
  have hrm := LinearMap.finrank_range_add_finrank_ker (componentSumMap K N)
  have hrange : LinearMap.range (componentSumMap K N) = ⊤ :=
    LinearMap.range_eq_top.mpr (componentSumMap_surjective K N)
  rw [hrange, finrank_top, Module.finrank_pi, Module.finrank_pi,
    Fintype.card_fin, Fintype.card_fin] at hrm
  have hsub := dyson_vertices_sub_components N
  omega

/-- The shadow-cancellation kernel: weight vectors `w : Fin (N / 2 + 1) → K` orthogonal to every
Bringmann–Ono shadow row `e_{[3n]} - e_{[3n+1]}` (i.e., `w([3n]) = w([3n+1])` for all `n : ℤ`). -/
def shadowKernel (N : ℕ) (hN : 0 < N) : Submodule K (Fin (N / 2 + 1) → K) where
  carrier := {w | ∀ n : ℤ, w (foldMod N hN (3 * n)) = w (foldMod N hN (3 * n + 1))}
  add_mem' {x y} hx hy n := by simp [hx n, hy n]
  zero_mem' _ := rfl
  smul_mem' a {x} hx n := by simp [hx n]

/-- Pairing a weight vector `w` against `shadowEdge K N hN n` equals `w([3n]) - w([3n+1])`. -/
theorem dotProduct_shadowEdge (N : ℕ) (hN : 0 < N) (w : Fin (N / 2 + 1) → K) (n : ℤ) :
    ∑ v : Fin (N / 2 + 1), w v * shadowEdge K N hN n v =
      w (foldMod N hN (3 * n)) - w (foldMod N hN (3 * n + 1)) := by
  simp only [shadowEdge, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hsingle : ∀ u : Fin (N / 2 + 1),
      ∑ v : Fin (N / 2 + 1), w v * (Pi.single (M := fun _ ↦ K) u (1 : K)) v = w u := by
    intro u
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hne; simp [Pi.single_eq_of_ne hne]
    · intro hnot; exact absurd (Finset.mem_univ u) hnot
  rw [hsingle, hsingle]

/-- A weight vector lies in `shadowKernel K N hN` iff it is orthogonal to every `shadowEdge`. -/
theorem mem_shadowKernel_iff_dotProduct_zero (N : ℕ) (hN : 0 < N) (w : Fin (N / 2 + 1) → K) :
    w ∈ shadowKernel K N hN ↔
      ∀ n : ℤ, ∑ v : Fin (N / 2 + 1), w v * shadowEdge K N hN n v = 0 := by
  simp only [shadowKernel, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq, dotProduct_shadowEdge, sub_eq_zero]

/-- **Exact Shadow-Cancellation Characterization (by `dysonCompId`):**
a folded weight vector has zero shadow iff it is constant on each connected component. -/
theorem mem_shadowKernel_iff_const_on_components (N : ℕ) (hN : 0 < N)
    (w : Fin (N / 2 + 1) → K) :
    w ∈ shadowKernel K N hN ↔
      ∀ u v : Fin (N / 2 + 1), dysonCompId N u = dysonCompId N v → w u = w v := by
  constructor
  · intro hw u v hcomp
    have htoRoot : ∀ x : Fin (N / 2 + 1),
        w x = w (dysonCompRoot N (dysonCompId N x)) := by
      intro x
      by_cases h3 : 3 ∣ N
      · by_cases hEq : x = dysonCompRoot N (dysonCompId N x)
        · rw [← hEq]
        · obtain ⟨n, h1, h2⟩ := exists_shadow_edge_to_root_of_dvd hN h3 x hEq
          have hn := hw n
          rw [h1, h2] at hn
          exact hn.symm
      · have hroot0 : dysonCompRoot N (dysonCompId N x) = ⟨0, Nat.succ_pos _⟩ := by
          ext; simp [dysonCompRoot, h3]
        rw [hroot0]
        clear hroot0
        rcases x with ⟨k, hk⟩
        induction k with
        | zero => rfl
        | succ m ih =>
          obtain ⟨n, h1, h2⟩ := exists_shadow_edge_consecutive hN h3 (k := m) (by omega)
          have hn := hw n
          rw [h1, h2] at hn
          exact hn.symm.trans (ih (by omega))
    rw [htoRoot u, htoRoot v, hcomp]
  · intro hconst n
    exact hconst _ _ (dysonCompId_three_mul_eq N hN n)

/-- **Exact Shadow-Cancellation Characterization (graph-theoretic form):**
a folded weight vector has zero shadow iff it is constant on connected components of
`dysonFoldedGraph N hN`. -/
theorem mem_shadowKernel_iff_const_on_reachable (N : ℕ) (hN : 0 < N)
    (w : Fin (N / 2 + 1) → K) :
    w ∈ shadowKernel K N hN ↔
      ∀ u v : Fin (N / 2 + 1), (dysonFoldedGraph N hN).Reachable u v → w u = w v := by
  rw [mem_shadowKernel_iff_const_on_components]
  constructor
  · intro h u v hreach
    exact h u v ((dysonFoldedGraph_reachable_iff hN u v).mp hreach)
  · intro h u v hcomp
    exact h u v ((dysonFoldedGraph_reachable_iff hN u v).mpr hcomp)

/-- Exact dimension of the shadow-cancellation kernel equals `dysonNumComponents N`. -/
theorem finrank_shadowKernel_eq (N : ℕ) (hN : 0 < N) :
    Module.finrank K (shadowKernel K N hN) = dysonNumComponents N := by
  let pull : (Fin (dysonNumComponents N) → K) →ₗ[K] (Fin (N / 2 + 1) → K) :=
    { toFun := fun f v ↦ f (dysonCompId N v)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hinj : Function.Injective pull := by
    intro f g hfg
    ext c
    have h := congrFun hfg (dysonCompRoot N c)
    simpa [pull, dysonCompId_compRoot] using h
  have hrange : LinearMap.range pull = shadowKernel K N hN := by
    ext w
    rw [LinearMap.mem_range, mem_shadowKernel_iff_const_on_components]
    constructor
    · rintro ⟨f, rfl⟩ u v hcomp
      simp [pull, hcomp]
    · intro hconst
      refine ⟨fun c ↦ w (dysonCompRoot N c), ?_⟩
      ext v
      exact hconst _ _ (dysonCompId_compRoot N (dysonCompId N v))
  rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi, Fintype.card_fin]

/-- **Every individual folded residue has NONZERO shadow** for every modulus `N ≥ 2`. -/
theorem single_vertex_not_mem_shadowKernel {N : ℕ} (hN : 2 ≤ N) (v : Fin (N / 2 + 1)) :
    Pi.single v (1 : K) ∉ shadowKernel K N (by omega) := by
  intro hmem
  rw [mem_shadowKernel_iff_const_on_reachable] at hmem
  obtain ⟨u, hadj⟩ := dysonFoldedGraph_exists_adj hN v
  have heq := hmem v u hadj.reachable
  have hne : u ≠ v := hadj.ne.symm
  simp [Pi.single_eq_same, Pi.single_eq_of_ne hne] at heq

/-- Concrete `N = 6` verification: exact shadow rank `r_6 = 2` with `2` connected components. -/
theorem dysonShadowRank_six :
    Module.finrank K (shadowRowSpan K 6 (by omega)) = 2 ∧ dysonNumComponents 6 = 2 := by
  constructor
  · rw [dysonShadowRank_eq K 6 (by omega)]
    decide
  · decide

/-- Concrete `N = 6` zero-shadow triples: the indicators of `{0, 1}` (lifted to `{5, 0, 1}`) and
`{2, 3}` (lifted to `{2, 3, 4}`) both cancel the shadow identically. -/
theorem dysonSix_triple_zero_shadow :
    (fun v : Fin 4 ↦ if (v : ℕ) ≤ 1 then (1 : K) else 0) ∈ shadowKernel K 6 (by omega) ∧
    (fun v : Fin 4 ↦ if 2 ≤ (v : ℕ) then (1 : K) else 0) ∈ shadowKernel K 6 (by omega) := by
  constructor <;>
  · rw [mem_shadowKernel_iff_const_on_components]
    intro u v hcomp
    have hval := congrArg Fin.val hcomp
    simp only [dysonCompId, show (3 : ℕ) ∣ 6 by decide, ↓reduceDIte] at hval
    have hu := u.isLt
    have hv := v.isLt
    split_ifs <;> first | rfl | omega

end LinearAlgebra

/-! ### 5. Discrete Cosine Orthogonality & Real Trigonometric Sine-Product Shadow Rank -/

/-- Complex geometric sum of `N`-th roots of unity vanishes for non-multiples of `N`. -/
private lemma sum_cexp_two_pi_mul_eq_zero {N : ℕ} (hN : 0 < N) {k : ℤ}
    (hk : ¬ ((N : ℤ) ∣ k)) :
    ∑ h : Fin N, Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((h : ℕ) : ℂ) / (N : ℂ)) = 0 := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ))
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hz_ne_one : z ≠ 1 := by
    intro hz1
    rw [Complex.exp_eq_one_iff] at hz1
    rcases hz1 with ⟨m, hm⟩
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hdiv : (k : ℂ) / (N : ℂ) = (m : ℂ) := by
      apply mul_left_cancel₀ h2pi
      calc
        2 * Real.pi * Complex.I * ((k : ℂ) / (N : ℂ))
            = 2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ) := by ring
        _ = (m : ℂ) * (2 * Real.pi * Complex.I) := hm
        _ = 2 * Real.pi * Complex.I * (m : ℂ) := by ring
    have hkmC : (k : ℂ) = (N : ℂ) * (m : ℂ) := by
      have := congrArg (· * (N : ℂ)) hdiv
      field_simp [hNne] at this
      exact this
    have hkm : k = (N : ℤ) * m := by exact_mod_cast hkmC
    exact hk ⟨m, hkm⟩
  have hzN : z ^ N = 1 := by
    rw [← Complex.exp_nat_mul]
    have harg : (N : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / (N : ℂ)) =
        (k : ℂ) * (2 * Real.pi * Complex.I) := by
      field_simp [hNne]
    rw [harg]
    exact Complex.exp_int_mul_two_pi_mul_I k
  have hterm : ∀ h : Fin N,
      Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * ((h : ℕ) : ℂ) / (N : ℂ)) = z ^ (h : ℕ) := by
    intro h
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun h : ℕ ↦ z ^ h)]
  have hgeom := mul_geom_sum z N
  rw [hzN, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hz_ne_one)

/-- Real discrete cosine sum vanishes for non-multiples of `N`. -/
private lemma sum_cos_two_pi_mul_eq_zero {N : ℕ} (hN : 0 < N) {k : ℤ}
    (hk : ¬ ((N : ℤ) ∣ k)) :
    ∑ h : Fin N, Real.cos (2 * Real.pi * (k : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) = 0 := by
  have hre := congrArg Complex.re (sum_cexp_two_pi_mul_eq_zero hN hk)
  rw [Complex.re_sum, Complex.zero_re] at hre
  rw [← hre]
  apply Finset.sum_congr rfl
  intro h _
  have harg : 2 * Real.pi * Complex.I * (k : ℂ) * ((h : ℕ) : ℂ) / (N : ℂ) =
      (((2 * Real.pi * (k : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_ofReal_mul_I_re]

/-- Discrete cosine orthogonality on `Fin (N / 2 + 1)`: distinct folded frequencies `v ≠ w` are
orthogonal over `h ∈ Fin N`. -/
theorem dct_orthogonality {N : ℕ} (hN : 0 < N) {v w : Fin (N / 2 + 1)} (hne : v ≠ w) :
    ∑ h : Fin N,
      Real.cos (2 * Real.pi * ((v : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) *
      Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) = 0 := by
  have hprod : ∀ h : Fin N,
      Real.cos (2 * Real.pi * ((v : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) *
      Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) =
      (1 / 2 : ℝ) * (Real.cos (2 * Real.pi * (((v : ℕ) - (w : ℕ) : ℤ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) +
        Real.cos (2 * Real.pi * (((v : ℕ) + (w : ℕ) : ℤ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ))) := by
    intro h
    have h1 : 2 * Real.pi * (((v : ℕ) - (w : ℕ) : ℤ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ) =
        2 * Real.pi * ((v : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ) -
        2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ) := by push_cast; ring
    have h2 : 2 * Real.pi * (((v : ℕ) + (w : ℕ) : ℤ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ) =
        2 * Real.pi * ((v : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ) +
        2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ) := by push_cast; ring
    rw [h1, h2, Real.cos_sub, Real.cos_add]
    ring
  simp_rw [hprod, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hv_le : (v : ℕ) ≤ N / 2 := Nat.lt_succ_iff.mp v.isLt
  have hw_le : (w : ℕ) ≤ N / 2 := Nat.lt_succ_iff.mp w.isLt
  have hvw_ne : (v : ℕ) ≠ (w : ℕ) := fun h ↦ hne (Fin.ext h)
  have hndvd_sub : ¬ ((N : ℤ) ∣ ((v : ℕ) : ℤ) - ((w : ℕ) : ℤ)) := by
    rintro ⟨q, hq⟩
    have hlt : ((v : ℕ) : ℤ) - ((w : ℕ) : ℤ) < (N : ℤ) := by omega
    have hgt : -(N : ℤ) < ((v : ℕ) : ℤ) - ((w : ℕ) : ℤ) := by omega
    have : q = 0 ∨ q ≥ 1 ∨ q ≤ -1 := by omega
    rcases this with rfl | hge | hle
    · omega
    · nlinarith
    · nlinarith
  have hndvd_add : ¬ ((N : ℤ) ∣ ((v : ℕ) : ℤ) + ((w : ℕ) : ℤ)) := by
    rintro ⟨q, hq⟩
    have hlt : ((v : ℕ) : ℤ) + ((w : ℕ) : ℤ) < (N : ℤ) := by omega
    have hpos : 0 < ((v : ℕ) : ℤ) + ((w : ℕ) : ℤ) := by omega
    have : q ≤ 0 ∨ q ≥ 1 := by omega
    rcases this with hle | hge
    · nlinarith
    · nlinarith
  rw [sum_cos_two_pi_mul_eq_zero hN hndvd_sub, sum_cos_two_pi_mul_eq_zero hN hndvd_add,
    add_zero, mul_zero]

/-- Discrete cosine evaluation map sending a folded vector `x : Fin (N / 2 + 1) → ℝ` to
`h ↦ ∑ v, x v * cos(2π v h / N)`. -/
noncomputable def dctMap (N : ℕ) : (Fin (N / 2 + 1) → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun x h := ∑ v : Fin (N / 2 + 1),
    x v * Real.cos (2 * Real.pi * ((v : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ))
  map_add' x y := by
    ext h; simp [add_mul, Finset.sum_add_distrib]
  map_smul' a x := by
    ext h; simp [mul_assoc, Finset.mul_sum]

/-- `dctMap N` is injective for every `N ≥ 1` (by discrete cosine orthogonality). -/
theorem dctMap_injective {N : ℕ} (hN : 0 < N) : Function.Injective (dctMap N) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  ext w
  have hsum0 : ∑ h : Fin N, dctMap N x h *
      Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) = 0 := by
    simp [hx]
  simp only [dctMap, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul] at hsum0
  rw [Finset.sum_comm] at hsum0
  have hfactor : ∀ v : Fin (N / 2 + 1),
      ∑ h : Fin N, x v * Real.cos (2 * Real.pi * ((v : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) *
          Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) =
        x v * ∑ h : Fin N,
          Real.cos (2 * Real.pi * ((v : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) *
          Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) := by
    intro v
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _; ring
  simp_rw [hfactor] at hsum0
  rw [Finset.sum_eq_single w] at hsum0
  · have hpos : 0 < ∑ h : Fin N,
        Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) *
        Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) := by
      have h0_mem : (⟨0, hN⟩ : Fin N) ∈ Finset.univ := Finset.mem_univ _
      have hnonneg : ∀ h ∈ (Finset.univ : Finset (Fin N)),
          0 ≤ Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) *
              Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) :=
        fun h _ ↦ mul_self_nonneg _
      have hge := Finset.single_le_sum hnonneg h0_mem
      have h0val : Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / (N : ℝ)) *
          Real.cos (2 * Real.pi * ((w : ℕ) : ℝ) * ((0 : ℕ) : ℝ) / (N : ℝ)) = 1 := by
        simp
      linarith
    exact (mul_eq_zero.mp hsum0).resolve_right (ne_of_gt hpos)
  · intro v _ hne
    rw [dct_orthogonality hN hne, mul_zero]
  · intro hnot; exact absurd (Finset.mem_univ w) hnot

/-- The `n`-th real Bringmann–Ono sine-product shadow row vector on twists `h ∈ Fin N`:
`h ↦ 2 sin(π h / N) sin((6n + 1) π h / N)`. -/
noncomputable def dysonTrigShadowRow (N : ℕ) (n : ℤ) : Fin N → ℝ :=
  fun h ↦ 2 * Real.sin (Real.pi * ((h : ℕ) : ℝ) / (N : ℝ)) *
    Real.sin ((6 * (n : ℝ) + 1) * Real.pi * ((h : ℕ) : ℝ) / (N : ℝ))

/-- `dctMap N` maps the algebraic edge difference `shadowEdge ℝ N hN n` directly onto the
Bringmann–Ono trigonometric shadow row `dysonTrigShadowRow N n`. -/
theorem dctMap_shadowEdge (N : ℕ) (hN : 0 < N) (n : ℤ) :
    dctMap N (shadowEdge ℝ N hN n) = dysonTrigShadowRow N n := by
  ext h
  simp only [dctMap, shadowEdge, dysonTrigShadowRow, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hsingle : ∀ u : Fin (N / 2 + 1),
      ∑ v : Fin (N / 2 + 1),
        (Pi.single (M := fun _ ↦ ℝ) u (1 : ℝ)) v *
          Real.cos (2 * Real.pi * ((v : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) =
      Real.cos (2 * Real.pi * ((u : ℕ) : ℝ) * ((h : ℕ) : ℝ) / (N : ℝ)) := by
    intro u
    rw [Finset.sum_eq_single u]
    · simp
    · intro v _ hne; simp [Pi.single_eq_of_ne hne]
    · intro hnot; exact absurd (Finset.mem_univ u) hnot
  have hc1 := cos_two_pi_mul_foldMod N hN (3 * n) ((h : ℕ) : ℤ)
  have hc2 := cos_two_pi_mul_foldMod N hN (3 * n + 1) ((h : ℕ) : ℤ)
  push_cast at hc1 hc2
  rw [hsingle, hsingle, ← hc1, ← hc2]
  have htrig := dyson_shadow_trig_identity N n ((h : ℕ) : ℤ)
  simpa using htrig.symm

/-- **Exact Real Trigonometric Bringmann–Ono Shadow Rank Theorem** for EVERY modulus `N ≥ 1`:
the real linear span of the sine-product shadow rows
`{h ↦ 2 sin(π h / N) sin((6n + 1) π h / N) : n ∈ ℤ}` on `Fin N` has exact dimension
`N / 3` when `3 ∣ N` and `N / 2` when `¬ (3 ∣ N)`. -/
theorem dysonTrigShadowRank_eq (N : ℕ) (hN : 0 < N) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (dysonTrigShadowRow N))) =
      dysonShadowRank N := by
  let f : shadowRowSpan ℝ N hN →ₗ[ℝ] (Fin N → ℝ) :=
    (dctMap N).comp (shadowRowSpan ℝ N hN).subtype
  have hfinj : Function.Injective f := (dctMap_injective hN).comp Subtype.val_injective
  have hrange : LinearMap.range f = Submodule.span ℝ (Set.range (dysonTrigShadowRow N)) := by
    have himg : Submodule.map (dctMap N) (shadowRowSpan ℝ N hN) =
        Submodule.span ℝ (Set.range (dysonTrigShadowRow N)) := by
      rw [shadowRowSpan, Submodule.map_span]
      congr 1
      ext y
      constructor
      · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
        exact ⟨n, (dctMap_shadowEdge N hN n).symm⟩
      · rintro ⟨n, rfl⟩
        exact ⟨shadowEdge ℝ N hN n, ⟨n, rfl⟩, dctMap_shadowEdge N hN n⟩
    rw [← himg]
    ext y
    simp [f]
  rw [← hrange, LinearMap.finrank_range_of_inj hfinj]
  exact dysonShadowRank_eq ℝ N hN

end

end CubicTheta.AllD
