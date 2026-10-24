import OTSelector.Probability.StationaryWeightedAverage
import OTSelector.Reconstruction.StationaryFaceBoxMeanErgodic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral

/-! Weighted spatial averages of genuine strongly continuous isometric orbits. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {ι : Type*} [Fintype ι]



variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (U : (ι → ℝ) → H ≃ₗᵢ[ℝ] H) (hcont : ∀ x, Continuous (fun v ↦ U v x))
  {w : (ι → ℝ) → ℝ} (hw : Integrable w volume)
include hcont hw













variable (hadd : ∀ a b x, U a (U b x) = U (a + b) x)
include hadd







omit hcont hw hadd



/-- A fixed continuous test on the actual unit face cube has vanishing
weighted Bochner averages for every diverging real scale, even with arbitrary
scale-dependent spatial offsets. No weighted limit or mixing premise enters. -/
theorem tendsto_stationaryContinuousFaceTestAverage_zero
    {G : Type*} [AddCommGroup G] [Module ℝ G]
    (V : G → H ≃ₗᵢ[ℝ] H) (haddV : ∀ a b x, V a (V b x) = V (a + b) x)
    (L : (ι → ℝ) →ₗ[ℝ] G)
    (hcontV : ∀ x, Continuous (fun v ↦ V (L v) x))
    {ψ : (ι → ℝ) → ℝ} (hψ : ContinuousOn ψ (haarRootCube ι 1))
    {x : H} (hx : (translationFixedSubspace V L.range).starProjection x = 0)
    (offset : ℝ → G) :
    Tendsto (fun R : ℝ ↦ ∫ y in haarRootCube ι 1,
      ψ y • V (offset R + L (R • y)) x) atTop (𝓝 0) := by
  have hw : Integrable ((haarRootCube ι 1).indicator ψ) volume :=
    hψ.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hlim := tendsto_stationaryWeightedFaceAverage_zero V haddV L hcontV hw hx offset
  apply hlim.congr'
  filter_upwards [] with R
  rw [← integral_indicator (s := haarRootCube ι 1) measurableSet_Icc]
  congr 1
  funext y
  by_cases hy : y ∈ haarRootCube ι 1 <;> simp [hy]

end OTSelector.Reconstruction
