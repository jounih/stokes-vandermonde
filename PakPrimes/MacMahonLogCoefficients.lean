module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.PowerSeries.Derivative

public section

namespace PakPrimes.DivisorAndMacMahon

open scoped BigOperators

noncomputable section

/-- Generating series for the sum of the squares of the positive divisors. -/
@[expose] def macmahonDivisorSeries : PowerSeries ℂ :=
  PowerSeries.mk fun d => if d = 0 then 0 else ∑ k ∈ Nat.divisors d, (k : ℂ) ^ 2

/-- The geometric series in powers of `X^(n+1)`. -/
@[expose] def EulerGeometric (n : ℕ) : PowerSeries ℂ :=
  PowerSeries.mk fun d => if n + 1 ∣ d then 1 else 0

@[simp] theorem constantCoeff_EulerGeometric (n : ℕ) :
    PowerSeries.constantCoeff (EulerGeometric n) = 1 := by
  simp [EulerGeometric]

/-- The Euler logarithmic derivative of a finite set of MacMahon factors. -/
@[expose] def finiteEulerLog (S : Finset ℕ) : PowerSeries ℂ :=
  ∑ i ∈ S, PowerSeries.C (((i + 1 : ℕ) : ℂ) ^ 2) * (EulerGeometric i - 1)

/-- Including the first `d` factors suffices to obtain the exact degree-`d` coefficient. -/
theorem coeff_finiteEulerLog (d : ℕ) (S : Finset ℕ) (h : Finset.range d ⊆ S) :
    PowerSeries.coeff d (finiteEulerLog S) = PowerSeries.coeff d macmahonDivisorSeries := by
  classical
  by_cases hd : d = 0
  · subst d
    simp [finiteEulerLog, macmahonDivisorSeries, PowerSeries.coeff_zero_eq_constantCoeff]
  simp only [finiteEulerLog, map_sum, PowerSeries.coeff_C_mul, map_sub, EulerGeometric,
    PowerSeries.coeff_mk, PowerSeries.coeff_one, hd, ite_false, sub_zero, mul_ite, mul_one,
    mul_zero, macmahonDivisorSeries]
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun i _ => i + 1) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro i hi
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hi).2, hd⟩
  · intro i hi j hj hij
    omega
  · intro j hj
    obtain ⟨hdvd, _⟩ := Nat.mem_divisors.mp hj
    have hjpos := Nat.pos_of_mem_divisors hj
    have hjle := Nat.le_of_dvd (Nat.pos_of_ne_zero hd) hdvd
    have hsucc : j - 1 + 1 = j := by omega
    refine ⟨j - 1, Finset.mem_filter.mpr ⟨h (Finset.mem_range.mpr (by omega)), ?_⟩, hsucc⟩
    simpa only [hsucc] using hdvd

end

end PakPrimes.DivisorAndMacMahon
