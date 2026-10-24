import OTSelector.Reconstruction.OriginalReserveFullUnitInputReserveCounts
import OTSelector.Probability.PoissonCountLowerTail
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedWindowPorts

/-! Positive actual reserve classes supply natural sample-capacity failure bounds. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- The true theta-volume Poisson mean is positive for every genuinely positive
class in the same physical cube. Dimension zero is included in this volume fact. -/
theorem originalReserveClassCountMean_pos {q : ℕ}
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q)))
    {θ R : ℝ} (hθ : 0 < θ) (hR : 0 < R) (γ : Measure ℝ)
    (C : Set ℝ) (hCmass : 0 < γ.real C) :
    0 < (((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) *
      (γ C).toNNReal : ℝ≥0) : ℝ) := by
  have hV : 0 < volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) := by
    rw [show volume.real (originalCenteredPhysicalCubeRegion b (2 * R)) =
      volume.real (haarRootCube (Fin q) R) from congrArg ENNReal.toReal (volume_originalOrientedTraffic_cube b R),
      volume_real_haarRootCube (Fin q) hR.le, Fintype.card_fin]
    exact pow_pos (by positivity) q
  simp only [NNReal.coe_mul, ENNReal.coe_toNNReal_eq_toReal,
    Real.coe_toNNReal _ hθ.le]
  exact mul_pos (mul_pos hθ hV) hCmass

namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- The actual source class count's deviation event has its quantitative bound
under the same full experiment, with no exceptional-event independence. -/
theorem sourceReserveBlockCount_deviation_probability {C : Set ℝ} (hC : MeasurableSet C)
    {δ : ℝ} (hδ : 0 < δ) :
    let a := (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (α C).toNNReal
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
      {p | δ < |(originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) C : ℝ) - (a : ℝ)|} ≤
      Real.sqrt (a : ℝ) / δ := by
  dsimp only
  exact poissonCount_deviation_probability_of_hasLaw _ _
    (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) hC) _
    (X.hasLaw_sourceReserveBlockCount hC) hδ

/-- Every positive actual source extreme class has its true half-mean sample
capacity event. The mean is exactly theta V times the original class mass. -/
theorem sourceReserveBlockCount_lower_probability (hR : 0 < R)
    {C : Set ℝ} (hC : MeasurableSet C) (hCmass : 0 < α.real C) :
    let a := (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (α C).toNNReal
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
      {p | (originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) C : ℝ) < (a : ℝ) / 2} ≤
      Real.sqrt (a : ℝ) / ((a : ℝ) / 2) := by
  dsimp only
  exact poissonCount_lower_probability_of_hasLaw _ _
    (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) hC) _
    (X.hasLaw_sourceReserveBlockCount hC)
    (originalReserveClassCountMean_pos b hθ hR α C hCmass)

/-- The actual target class count's deviation event has its quantitative bound
under the same full experiment, with no exceptional-event independence. -/
theorem targetReserveBlockCount_deviation_probability {C : Set ℝ} (hC : MeasurableSet C)
    {δ : ℝ} (hδ : 0 < δ) :
    let a := (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (β C).toNNReal
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
      {p | δ < |(originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) C : ℝ) - (a : ℝ)|} ≤
      Real.sqrt (a : ℝ) / δ := by
  dsimp only
  exact poissonCount_deviation_probability_of_hasLaw _ _
    (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) hC) _
    (X.hasLaw_targetReserveBlockCount hC) hδ

/-- Every positive actual target extreme class has its true half-mean sample
capacity event. The mean is exactly theta V times the original class mass. -/
theorem targetReserveBlockCount_lower_probability (hR : 0 < R)
    {C : Set ℝ} (hC : MeasurableSet C) (hCmass : 0 < β.real C) :
    let a := (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (β C).toNNReal
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).real
      {p | (originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) C : ℝ) < (a : ℝ) / 2} ≤
      Real.sqrt (a : ℝ) / ((a : ℝ) / 2) := by
  dsimp only
  exact poissonCount_lower_probability_of_hasLaw _ _
    (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) hC) _
    (X.hasLaw_targetReserveBlockCount hC)
    (originalReserveClassCountMean_pos b hθ hR β C hCmass)

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
