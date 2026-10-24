import OTSelector.Reconstruction.OriginalLegalScreeningComparatorActualSignedMaximumData
import OTSelector.Reconstruction.OriginalReserveWorkingOriginalIndices
import OTSelector.Reconstruction.OriginalReserveWorkingFullCounts
import OTSelector.Reconstruction.OriginalReserveWorkingFullClockLabels
import OTSelector.Reconstruction.OriginalReserveWorkingSpatialCarriers

/-! The actual full working experiment produces unchanged original-label screening data. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped BigOperators ENNReal Classical ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- On one event in the actual full working experiment, the complete original
arrays themselves produce the data consumed by signed screening. Both array
functions retain their literal FULL labels, with no fresh enumeration. -/
theorem ae_originalClockBlockFullArrayData
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    {Main Reserve : LegalWeightedStationaryPoissonMatching
      (finrank ℝ S.covector.ker) μ ν kin g}
    {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {ρ R δ diameter : ℝ}
    (hq : 0 < finrank ℝ S.covector.ker) (hR : 0 < R)
    (G : OriginalStageClockGrid)
    (hlo : G.cut 0 = D.lo+(S.level : ℝ)) (hhi : G.cut G.count = D.hi+(S.level : ℝ))
    (hsep : ConditionalClockSupportBounds μ ν δ diameter)
    (hwidth : ∀ k : Fin G.count, G.cut (k+1)-G.cut k < δ) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∀ X : OriginalReserveFullWorkingInputExperiment Main Reserve b ρ R,
    ∀ᵐ p ∂(X.fullLaw : Measure
      (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
      ∃ A : OriginalClockBlockFullArrayData (μ:=μ) (ν:=ν) G b R
        (p.1.1,p.1.2.2) p.2.1.1 p.2.2.1,
      A.source = (originalMappedReserveCloudArrays _
        (originalOrientedRawCubePhysicalMap b R) p.2).1.2 ∧
      A.target = (originalMappedReserveCloudArrays _
        (originalOrientedRawCubePhysicalMap b R) p.2).2.2 := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  intro X
  have hbs := ae_all_iff.mpr (fun block : G.ClockSlabBlock μ ν ↦
    X.ae_fullArray_clockBlock_counts (G.blockCells_measurable block).1)
  have hbt := ae_all_iff.mpr (fun block : G.ClockSlabBlock μ ν ↦
    X.ae_fullArray_clockBlock_counts (G.blockCells_measurable block).2)
  filter_upwards [X.ae_fullArray_injective_and_originalReserve_embeddings hq hR,
    X.ae_full_arrays,D.ae_fullWorkingInput_all_grid_labels X,
    X.ae_fullAndReserveArrays_in_workingCube hR,hbs,hbt]
    with p he hc hl hp hbs hbt
  obtain ⟨hs,ht,es,et,hes,het⟩ := he
  have hd := originalWorkingInput_fullArray_color_decomposition
    (measurableSet_originalOrientedTraffic_cube b R) p.1.1 _ _ hc
  have hl' := hl G hlo hhi
  refine ⟨{
    source := (originalMappedReserveCloudArrays _
      (originalOrientedRawCubePhysicalMap b R) p.2).1.2
    target := (originalMappedReserveCloudArrays _
      (originalOrientedRawCubePhysicalMap b R) p.2).2.2
    source_injective := hs
    target_injective := ht
    sourceEmbedding := es
    targetEmbedding := et
    source_original := hes
    target_original := het
    source_counting := hd.1
    target_counting := hd.2
    source_grid := hl'.1
    target_grid := hl'.2.1
    monochrome := ?_
    source_carrier := hp.1
    target_carrier := hp.2.1
    source_blocks := ?_
    target_blocks := ?_ },rfl,rfl⟩
  · intro k
    rcases hl'.2.2 hsep hwidth k.val k.isLt with h | h
    · exact Or.inl (fun i hi ↦ h i ((G.sourceLabel_eq_iff _ k).mpr hi))
    · exact Or.inr (fun j hj ↦ h j ((G.targetLabel_eq_iff _ k).mpr hj))
  · intro block
    simpa using hbs block 0
  · intro block
    simpa using hbt block 1

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
