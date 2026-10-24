import OTSelector.Reconstruction.OriginalStagePhysicalPortProbability
import OTSelector.Reconstruction.OriginalStagePortAtomLaws

/-! The actual axis-aligned canonical port laws are the standard-frame physical port laws. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Literal unchanged axis-aligned reflected port law, on the original root cube. -/
def originalAxisPortProbabilityMeasure {q : ℕ} (R : ℝ) (x : Fin q → ℝ) : Measure (Fin q → ℝ) :=
  (volume.restrict (haarRootCube (Fin q) R)).withDensity
    (fun z ↦ ENNReal.ofReal (originalCubeReflectedKernel (originalEuclideanMollifier q) R z x))

theorem originalStage_standardFrame_cube {q : ℕ} (R : ℝ) :
    originalCenteredPhysicalCubeRegion (EuclideanSpace.basisFun (Fin q) ℝ) (2 * R) =
      haarRootCube (Fin q) R := by
  have hhalf : 2 * R / 2 = R := by ring
  have hneg : -(2 * R) / 2 = -R := by ring
  unfold originalCenteredPhysicalCubeRegion
  change (id '' Icc (fun _ ↦ -(2 * R) / 2) (fun _ ↦ 2 * R / 2)) = _
  simp only [Set.image_id, hhalf, hneg, haarRootCube]

/-- The actual axis-aligned law agrees with the physical law in the canonical standard
orthonormal frame, keeping the same original endpoint and kernel exactly. -/
theorem originalAxisPortProbabilityMeasure_eq_standardFrame {q : ℕ} (R : ℝ) (x : Fin q → ℝ) :
    originalAxisPortProbabilityMeasure R x =
      originalPhysicalPortProbabilityMeasure (EuclideanSpace.basisFun (Fin q) ℝ) R x := by
  rw [originalPhysicalPortProbabilityMeasure, originalStage_standardFrame_cube]
  rfl

theorem originalAxisPortProbabilityMeasure_isProbability {q : ℕ} {R : ℝ} (hR : 1 ≤ R)
    {x : Fin q → ℝ} (hx : x ∈ haarRootCube (Fin q) R) :
    IsProbabilityMeasure (originalAxisPortProbabilityMeasure R x) := by
  rw [originalAxisPortProbabilityMeasure_eq_standardFrame]
  apply originalPhysicalPortProbabilityMeasure_isProbability _ hR
  rwa [originalStage_standardFrame_cube]

/-- The true axis-aligned reflection also has Euclidean deviation at most one. -/
theorem originalAxisPortProbabilityMeasure_ae_euclidean_deviation_le_one {q : ℕ} {R : ℝ}
    {x : Fin q → ℝ} (hx : x ∈ haarRootCube (Fin q) R) :
    ∀ᵐ z ∂originalAxisPortProbabilityMeasure R x,
      ‖(EuclideanSpace.equiv (Fin q) ℝ).symm (z - x)‖ ≤ 1 := by
  rw [originalAxisPortProbabilityMeasure_eq_standardFrame]
  apply originalPhysicalPortProbabilityMeasure_ae_euclidean_deviation_le_one
  rwa [originalStage_standardFrame_cube]

/-- Summing the original indexed axis-aligned port laws in a true class gives exactly the
actual port class density measure used by the original stage arrival/departure law. -/
theorem originalFiniteEndpointAtoms_axisPortClassMeasure {q n : ℕ}
    (points : Fin n → LegalMarkedPhysicalPoint q) (C : Set ℝ) (hC : MeasurableSet C) (R : ℝ) :
    (volume.restrict (haarRootCube (Fin q) R)).withDensity
      (fun z ↦ ENNReal.ofReal (originalStageReflectedClassDensity (originalEuclideanMollifier q) R C
        (∑ i, Measure.dirac (points i)) z)) =
      ∑ i, if (points i).2 ∈ C then originalAxisPortProbabilityMeasure R (points i).1 else 0 := by
  exact originalFiniteEndpointAtoms_classMeasure points C hC
    (originalCubeReflectedKernel (originalEuclideanMollifier q) R)
    (measurable_originalCubeReflectedKernel (contDiff_originalEuclideanMollifier q).continuous.measurable R)
    (originalCubeReflectedKernel_nonneg (originalEuclideanMollifier_nonneg q) R) _

end OTSelector.Reconstruction
