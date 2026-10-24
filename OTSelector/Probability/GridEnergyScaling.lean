import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Physical side length cancels the sublinear mass exponent in a local
matching energy bound. Summing over a grid charges its volume rather than
the number of cells. The identities include null cells and zero density. -/

open scoped BigOperators
noncomputable section
namespace OTSelector.Probability

/-- The physical squared-side prefactor exactly restores volume at the
matching exponent, including zero side length or zero density. -/
theorem side_sq_mul_density_volume_rpow (q : ℕ) (hq : 2 < q)
    {density side : ℝ} (hdensity : 0 ≤ density) (hside : 0 ≤ side) :
    side ^ 2 * (density * side ^ q) ^ (1 - 2 / (q : ℝ)) =
      density ^ (1 - 2 / (q : ℝ)) * side ^ q := by
  have hq0 : q ≠ 0 := by omega
  have hqreal : (q : ℝ) ≠ 0 := by exact_mod_cast hq0
  by_cases hs : side = 0
  · simp [hs, zero_pow hq0]
  have hspos : 0 < side := lt_of_le_of_ne hside (Ne.symm hs)
  have hpower : (side ^ q) ^ (1 - 2 / (q : ℝ)) =
      side ^ ((q : ℝ) * (1 - 2 / (q : ℝ))) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hside]
  have hexponent : (2 : ℝ) + (q : ℝ) * (1 - 2 / (q : ℝ)) = (q : ℝ) := by
    field_simp
    ring
  rw [Real.mul_rpow hdensity (pow_nonneg hside q), hpower]
  calc
    side ^ 2 * (density ^ (1 - 2 / (q : ℝ)) *
        side ^ ((q : ℝ) * (1 - 2 / (q : ℝ)))) =
      density ^ (1 - 2 / (q : ℝ)) *
        (side ^ (2 : ℝ) * side ^ ((q : ℝ) * (1 - 2 / (q : ℝ)))) := by
          rw [Real.rpow_two]
          ring
    _ = density ^ (1 - 2 / (q : ℝ)) * side ^ q := by
      rw [← Real.rpow_add hspos, hexponent, Real.rpow_natCast]

/-- A true density bound on one original cell controls its physical local
energy by that cell's full-box volume. No positive cell mass is required. -/
theorem side_sq_mul_mass_rpow_le_volume (q : ℕ) (hq : 2 < q)
    {density side mass : ℝ} (hdensity : 0 ≤ density) (hside : 0 ≤ side)
    (hmass : 0 ≤ mass) (hbound : mass ≤ density * side ^ q) :
    side ^ 2 * mass ^ (1 - 2 / (q : ℝ)) ≤
      density ^ (1 - 2 / (q : ℝ)) * side ^ q := by
  have hqreal : (2 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hexponent : 0 ≤ 1 - 2 / (q : ℝ) := by
    have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
    have hdiv : 2 / (q : ℝ) < 1 := (div_lt_one hqpos).mpr hqreal
    linarith
  calc
    side ^ 2 * mass ^ (1 - 2 / (q : ℝ)) ≤
        side ^ 2 * (density * side ^ q) ^ (1 - 2 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hmass hbound hexponent) (sq_nonneg _)
    _ = density ^ (1 - 2 / (q : ℝ)) * side ^ q :=
      side_sq_mul_density_volume_rpow q hq hdensity hside

/-- Summing original local energy bounds charges the full-box grid volume;
the estimate contains no factor counting its spatial cells. -/
theorem sum_side_sq_mul_mass_rpow_le_volume {I : Type*}
    (cells : Finset I) (q : ℕ) (hq : 2 < q)
    (density : ℝ) (hdensity : 0 ≤ density) (side mass : I → ℝ)
    (hside : ∀ i ∈ cells, 0 ≤ side i) (hmass : ∀ i ∈ cells, 0 ≤ mass i)
    (hbound : ∀ i ∈ cells, mass i ≤ density * side i ^ q) :
    (∑ i ∈ cells, side i ^ 2 * mass i ^ (1 - 2 / (q : ℝ))) ≤
      density ^ (1 - 2 / (q : ℝ)) * ∑ i ∈ cells, side i ^ q := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi ↦
    side_sq_mul_mass_rpow_le_volume q hq hdensity (hside i hi) (hmass i hi) (hbound i hi)

end OTSelector.Probability
