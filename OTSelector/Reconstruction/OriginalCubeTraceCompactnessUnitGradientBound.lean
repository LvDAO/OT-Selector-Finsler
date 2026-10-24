import OTSelector.Reconstruction.OriginalCubeTraceCompactnessAllFaces
import OTSelector.Reconstruction.OriginalCubeTraceCompactnessGradientLtwo

/-! Actual common raw-cube boundary trace bound in the existing physical gradient L² norm. -/
open Set Function MeasureTheory TopologicalSpace
open scoped ENNReal Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

private instance originalUnitGradientBoundVolumeFinite {q : ℕ} :
    IsFiniteMeasure (volume.restrict (Icc (0 : Fin q → ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne

/-- All actual unit-cube faces at once obey the physical gradient norm bound used by the
original weak Neumann consumer, for every original smooth test with zero cube mean. The
constant is the square root of the same genuine common face-data quadratic bound. -/
theorem smooth_rawUnitCube_all_faces_pairing_abs_le_smoothPhysicalGradientLtwo {r : ℕ}
    {g : Fin (r + 1) × Fin 2 → (Fin r → ℝ) → ℝ}
    (hg : ∀ j, MemLp (g j) 2 (volume.restrict (Icc (fun _ : Fin r ↦ (0 : ℝ)) (fun _ ↦ 1))))
    (K : Compacts (Fin (r + 1) → ℝ)) (φ : 𝓓_{K}(Fin (r + 1) → ℝ, ℝ))
    (hmean : (∫ x in Icc (0 : Fin (r + 1) → ℝ) 1, φ x) = 0) :
    |originalRawUnitCubeBoundaryPairing g φ| ≤
      Real.sqrt (originalRawUnitCubeBoundaryTraceDualBound g) *
        ‖smoothPhysicalGradientLtwo K
          (volume.restrict (Icc (0 : Fin (r + 1) → ℝ) 1)) φ‖ := by
  have hs := smooth_rawUnitCube_all_faces_pairing_sq_le hg
    (φ.contDiff.of_le (by norm_num)) hmean
  rw [originalRawUnitCubeGradientEnergy_eq_smoothPhysicalGradientLtwo_norm_sq] at hs
  have hB := originalRawUnitCubeBoundaryTraceDualBound_nonneg g
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hB] using hs

end OTSelector.Reconstruction
