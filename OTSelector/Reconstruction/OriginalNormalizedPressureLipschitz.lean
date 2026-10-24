import OTSelector.Reconstruction.FinslerPopulationAtlasPressure

/-! The true physical probe Lipschitz constant survives original population
normalization exactly, including arbitrarily small or zero Haar density. -/
open MeasureTheory
open scoped NNReal
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Exact original population density normalization removes the density
from probe differences; a positive lower density bound is unnecessary. -/
theorem abs_normalized_pressure_sub_le
    {theta q : ℝ} (htheta : 0 ≤ theta) (hq : 0 < q)
    {I : ℝ → ℝ} {G : ℝ≥0} (hI : LipschitzWith G I) (t u : ℝ) :
    |theta ^ (-2 / q) * I (t * theta ^ (2 / q)) -
      theta ^ (-2 / q) * I (u * theta ^ (2 / q))| ≤ (G : ℝ) * |t-u| := by
  have hdist := hI.dist_le_mul (t * theta ^ (2/q)) (u * theta ^ (2/q))
  simp only [Real.dist_eq] at hdist
  rw [← mul_sub,abs_mul,abs_of_nonneg (Real.rpow_nonneg htheta _)]
  calc
    _ ≤ theta ^ (-2/q) * ((G : ℝ) *
        |t * theta ^ (2/q) - u * theta ^ (2/q)|) :=
      mul_le_mul_of_nonneg_left hdist (Real.rpow_nonneg htheta _)
    _ = (G : ℝ) * (theta ^ (-2/q) * |(t-u) * theta ^ (2/q)|) := by
      rw [← sub_mul]
      ring
    _ ≤ (G : ℝ) * |t-u| := mul_le_mul_of_nonneg_left
      (abs_probe_mul_inverse_rpow_le (t := t-u) htheta hq) G.coe_nonneg

/-- The common physical probe norm is also the Lipschitz constant of every
population-normalized pressure; no intensity upper or lower bound occurs. -/
theorem lipschitz_normalized_pressure
    {theta q : ℝ} (htheta : 0 ≤ theta) (hq : 0 < q)
    {I : ℝ → ℝ} {G : ℝ≥0} (hI : LipschitzWith G I) :
    LipschitzWith G (fun t ↦ theta ^ (-2/q) * I (t * theta ^ (2/q))) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  simpa only [Real.dist_eq] using abs_normalized_pressure_sub_le htheta hq hI t u

/-- Nonnegative original zero-tilt pressure gives the uniform physical probe
lower bound after exact original population normalization. -/
theorem normalized_pressure_lower_bound
    {theta q : ℝ} (htheta : 0 ≤ theta) (hq : 0 < q)
    {I : ℝ → ℝ} {G : ℝ≥0} (hI : LipschitzWith G I) (hzero : 0 ≤ I 0) (t : ℝ) :
    -(|t| * (G : ℝ)) ≤ theta ^ (-2/q) * I (t * theta ^ (2/q)) := by
  have h := abs_normalized_pressure_sub_le htheta hq hI t 0
  simp only [zero_mul,sub_zero] at h
  have hbase : 0 ≤ theta ^ (-2/q) * I 0 :=
    mul_nonneg (Real.rpow_nonneg htheta _) hzero
  have hl := (abs_le.mp h).1
  linarith only [hbase,hl]

end OTSelector.Reconstruction
