import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalMinimizingSequence

/-! At zero tilt the literal original weighted pressure is nonnegative and
bounded by the true Palm energy of every actual original matching. -/
open Set MeasureTheory Matrix Module Manifold
open scoped ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- One actual original weighted matching supplies both nonemptiness and the
exact zero-tilt Palm comparison. No minimizing-sequence or second-moment input
is needed for this lower-side pressure estimate. -/
theorem originalWeightedStationaryInf_zero_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} (hgap : 0 < gap) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) :
    0 ≤ D.originalWeightedStationaryInf gap g 0 ∧
      D.originalWeightedStationaryInf gap g 0 ≤
        ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law := by
  have hnonneg (R : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g) : 0 ≤ R.value 0 := by
    simp only [LegalWeightedStationaryPoissonMatching.value, zero_mul, add_zero]
    exact integral_nonneg (fun m ↦ D.originalFocalKinetic_nonneg hF hw hgap _ _ _)
  have hbelow : BddBelow (range (fun R : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g ↦ R.value 0)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨R, rfl⟩
    exact hnonneg R
  refine ⟨le_csInf ⟨Q.value 0, Q, rfl⟩ ?_, ?_⟩
  · rintro _ ⟨R, rfl⟩
    exact hnonneg R
  · have hle : D.originalWeightedStationaryInf gap g 0 ≤ Q.value 0 :=
      csInf_le hbelow ⟨Q, rfl⟩
    simpa only [LegalWeightedStationaryPoissonMatching.value, zero_mul, add_zero] using hle

/-- The exact original population normalization preserves the Palm comparison,
including zero density; the weight is the manuscript's `theta^(-2/q)`. -/
theorem original_normalizedWeightedPressure_zero_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap : ℝ} (hgap : 0 < gap) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g) {theta q : ℝ} (htheta : 0 ≤ theta) :
    0 ≤ theta ^ (-2 / q) * D.originalWeightedStationaryInf gap g 0 ∧
      theta ^ (-2 / q) * D.originalWeightedStationaryInf gap g 0 ≤
        theta ^ (-2 / q) * ∫ m, D.originalFocalKinetic gap m.1.1 m.1.2 m.2
          ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law := by
  have hbounds := D.originalWeightedStationaryInf_zero_bounds hF hw hgap Q
  exact ⟨mul_nonneg (Real.rpow_nonneg htheta _) hbounds.1,
    mul_le_mul_of_nonneg_left hbounds.2 (Real.rpow_nonneg htheta _)⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
