import OTSelector.Reconstruction.OriginalCubeTraceCompactnessFaceCoordinates
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates

/-! The original raw-cube derivative energy is the original physical gradient L² norm. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

private instance originalRawUnitCubeVolumeFinite {q : ℕ} :
    IsFiniteMeasure (volume.restrict (Icc (0 : Fin q → ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne

/-- The original raw unit-cube coordinate-gradient energy of an original bundled smooth test
is exactly its physical gradient's true Hilbert L² norm squared, with actual unit-cube volume. -/
theorem originalRawUnitCubeGradientEnergy_eq_smoothPhysicalGradientLtwo_norm_sq {q : ℕ}
    (K : Compacts (Fin q → ℝ)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) :
    originalRawUnitCubeGradientEnergy φ =
      ‖smoothPhysicalGradientLtwo K (volume.restrict (Icc (0 : Fin q → ℝ) 1)) φ‖^2 := by
  let μ : Measure (Fin q → ℝ) := volume.restrict (Icc 0 1)
  have hint (k : Fin q) : Integrable
      (fun x ↦ (fderiv ℝ φ x (Pi.single k 1))^2) μ := by
    apply ContinuousOn.integrableOn_Icc
    exact (((φ.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).continuousOn
  calc
    _ = ∫ x, ∑ k : Fin q, (fderiv ℝ φ x (Pi.single k 1))^2 ∂μ := by
      exact (integral_finsetSum Finset.univ (fun k _ ↦ hint k)).symm
    _ = ∫ x, ‖smoothPhysicalGradientLtwo K μ φ x‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [smoothPhysicalGradientLtwo_ae K μ φ] with x hx
      rw [hx, EuclideanSpace.real_norm_sq_eq]
      rfl
    _ = _ := (physicalFlux_norm_sq μ (smoothPhysicalGradientLtwo K μ φ)).symm

end OTSelector.Reconstruction
