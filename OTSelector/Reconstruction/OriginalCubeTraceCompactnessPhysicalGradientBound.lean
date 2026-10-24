import OTSelector.Reconstruction.OriginalCubeTraceCompactnessLiteralPhysicalCurrent
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates

/-! The literal physical current trace bound in the existing original Neumann gradient norm. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal Distributions BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- The actual centered orthogonal cube has finite original physical volume. -/
theorem isFiniteMeasure_originalCenteredPhysicalCubeVolume {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ) :
    IsFiniteMeasure (volume.restrict (originalCenteredPhysicalCubeRegion b R)) := by
  apply isFiniteMeasure_restrict.mpr
  exact (isCompact_Icc.image (orthonormalPhysicalCubeMap b).continuous).measure_lt_top.ne

attribute [instance] isFiniteMeasure_originalCenteredPhysicalCubeVolume

/-- The actual full physical derivative energy is exactly the original smooth gradient's
Hilbert norm squared under original volume restricted to the same physical cube. -/
theorem originalCenteredPhysicalCubeGradientEnergy_eq_smoothPhysicalGradientLtwo_norm_sq {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (K : Compacts (Fin q → ℝ)) (φ : 𝓓_{K}(Fin q → ℝ, ℝ)) :
    (∑ k : Fin q, ∫ z in originalCenteredPhysicalCubeRegion b R,
      (fderiv ℝ φ z (Pi.single k 1))^2) =
      ‖smoothPhysicalGradientLtwo K
        (volume.restrict (originalCenteredPhysicalCubeRegion b R)) φ‖^2 := by
  let μ : Measure (Fin q → ℝ) := volume.restrict (originalCenteredPhysicalCubeRegion b R)
  have hcompact : IsCompact (originalCenteredPhysicalCubeRegion b R) :=
    isCompact_Icc.image (orthonormalPhysicalCubeMap b).continuous
  have hint (k : Fin q) : Integrable (fun z ↦ (fderiv ℝ φ z (Pi.single k 1))^2) μ :=
    (((φ.contDiff.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).continuousOn.integrableOn_compact hcompact
  calc
    _ = ∫ z, ∑ k : Fin q, (fderiv ℝ φ z (Pi.single k 1))^2 ∂μ :=
      (integral_finsetSum Finset.univ (fun k _ ↦ hint k)).symm
    _ = ∫ z, ‖smoothPhysicalGradientLtwo K μ φ z‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [smoothPhysicalGradientLtwo_ae K μ φ] with z hz
      rw [hz, EuclideanSpace.real_norm_sq_eq]
      rfl
    _ = _ := (physicalFlux_norm_sq μ (smoothPhysicalGradientLtwo K μ φ)).symm

local instance originalPhysicalGradientBoundColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

/-- One full-measure original scene set controls every original smooth zero-mean physical
cube test in precisely the physical L2 gradient norm used by the weak Neumann consumer.
The coefficient is the square root of the same actual measurable integrable common bound. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_originalCurrent_physicalCube_pairing_abs_le_gradientLtwo
    {r : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin (r + 1) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (r + 1) α β kin g)
    (b : OrthonormalBasis (Fin (r + 1)) ℝ (EuclideanSpace ℝ (Fin (r + 1))))
    (j : LegalMarkedOptimalInputScene (r + 1) → Fin (r + 1) → ℝ)
    (hj : ∀ k, MemLp (fun s ↦ j s k) 2 (Q.law : Measure _))
    (hm : Measurable j) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ s ∂(Q.law : Measure _), ∀ (K : Compacts (Fin (r + 1) → ℝ))
      (φ : 𝓓_{K}(Fin (r + 1) → ℝ, ℝ)),
      (∫ z in originalCenteredPhysicalCubeRegion b R, φ z) = 0 →
      |originalPhysicalCubeVectorBoundaryPairing b
        (fun z ↦ j (legalMarkedInputSceneReroot (r + 1) z s)) R φ| ≤
        Real.sqrt (Q.scenePhysicalCubeTraceDualBound b
          (fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
            (originalEuclideanNormalReadout (b i))) R s) *
          ‖smoothPhysicalGradientLtwo K
            (volume.restrict (originalCenteredPhysicalCubeRegion b R)) φ‖ := by
  let x := fun i ↦ originalLinearCurrentReadoutLtwo (Q.law : Measure _) j hj
    (originalEuclideanNormalReadout (b i))
  filter_upwards [Q.ae_all_smooth_originalCurrent_physicalCube_pairing_sq_le b j hj hm hR] with s hs
  intro K φ hmean
  have hh := hs φ (φ.contDiff.of_le (by norm_num)) hmean
  rw [originalCenteredPhysicalCubeGradientEnergy_eq_smoothPhysicalGradientLtwo_norm_sq] at hh
  have hB := Q.scenePhysicalCubeTraceDualBound_nonneg b x hR.le s
  dsimp only [x] at hB
  apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [sq_abs, mul_pow, Real.sq_sqrt hB] using hh

end OTSelector.Reconstruction
