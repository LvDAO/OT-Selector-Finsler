import OTSelector.Reconstruction.OriginalLegalScreeningPressureFrame
import OTSelector.Reconstruction.OriginalReversePressurePoissonLimit
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficVolume

/-! Literal original-frame finite Poisson values and their exact pressure normalization. -/
open Set Function MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {q : ℕ}

/-- The volume used by the actual chosen-frame experiment is the genuine
physical side length to the spatial dimension. -/
theorem originalScreening_frame_volume
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {R : ℝ} (hR : 0 ≤ R) :
    volume.real (originalCenteredPhysicalCubeRegion b (2*R)) = (2*R)^q := by
  rw [measureReal_def,volume_originalOrientedTraffic_cube,← measureReal_def,
    volume_real_haarRootCube (Fin q) hR,Fintype.card_fin]

/-- The literal full original array expectation reads pressure for exactly
the kinetic coefficient in its physical frame, at the true Poisson intensity. -/
theorem originalScreeningFullValue_normalized_mean_eq_pressure
    (hq : 0 < q) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a d (fun i ↦ c*v i) = c^2*kin a d v)
    (g : ℝ → ℝ → ℝ) {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R) (τ : ℝ) :
    (∫ cloud, originalScreeningFullValue b R kin g τ cloud
      ∂twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal (ρ*volume.real (originalCenteredPhysicalCubeRegion b (2*R))))) /
      volume.real (originalCenteredPhysicalCubeRegion b (2*R)) =
        ρ^(1-2/(q : ℝ)) * legalMarkedScalePressure q id id α β
          (originalScreeningFrameKinetic b kin) g
          ((2*R)*ρ^(1/(q : ℝ))) (τ*ρ^(2/(q : ℝ))) := by
  rw [originalScreening_frame_volume b hR.le]
  rw [integral_congr_ae (ae_originalScreeningFullValue_eq_legalMarkedTilted_frame
    α β _ hq b hR.le kin hhom g τ)]
  exact originalRawScaleTilted_normalized_mean_eq_pressure hq α β
    (originalScreeningFrameKinetic b kin) g hρ (by positivity) τ

/-- A true eventual upper bound for the original full-array expectation
implies the exactly normalized pressure bound in the same physical frame. -/
theorem originalPressure_frame_le_of_actualFullValue_mean_bound
    (hq : 0 < q) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hhom : ∀ a d (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a d (fun i ↦ c*v i) = c^2*kin a d v)
    (g : ℝ → ℝ → ℝ) {ρ τ p bound : ℝ} (hρ : 0 < ρ)
    (hp : Tendsto (fun side : ℝ ↦ legalMarkedScalePressure q id id α β
      (originalScreeningFrameKinetic b kin) g side (τ*ρ^(2/(q : ℝ)))) atTop (𝓝 p))
    (hmean : ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop,
      (∫ cloud, originalScreeningFullValue b R kin g τ cloud
        ∂twoMarkedCloudLaw q ℝ ℝ α β
          (Real.toNNReal (ρ*volume.real (originalCenteredPhysicalCubeRegion b (2*R))))) /
        volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤ bound+ε) :
    p ≤ ρ^(-(1-2/(q : ℝ)))*bound := by
  apply originalPressure_le_of_actualPoisson_mean_bound hq α β
    (originalScreeningFrameKinetic b kin) g hρ hp
  intro ε hε
  filter_upwards [hmean ε hε,eventually_gt_atTop (0 : ℝ)] with R hmeanR hR
  rw [originalScreening_frame_volume b hR.le] at hmeanR
  rw [integral_congr_ae (ae_originalScreeningFullValue_eq_legalMarkedTilted_frame
    α β _ hq b hR.le kin hhom g τ)] at hmeanR
  exact hmeanR

end OTSelector.Reconstruction
