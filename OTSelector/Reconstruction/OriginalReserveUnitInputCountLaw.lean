import OTSelector.Reconstruction.OriginalReserveUnitInputFullCounts

/-! The actual global count in the full joined experiment has the literal two-color Poisson count law. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- Both complete original cube counts have their independent original Poisson laws. -/
theorem map_originalCubeReserve_countPair (q : ℕ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (rate : ℝ≥0) :
    (twoMarkedCloudLaw q ℝ ℝ α β rate).map (fun cloud ↦ (cloud.1.1, cloud.2.1)) =
      (poissonMeasure rate).prod (poissonMeasure rate) := by
  change ((markedPoissonLaw q ℝ α rate).prod (markedPoissonLaw q ℝ β rate)).map
    (Prod.map Prod.fst Prod.fst) = _
  rw [← Measure.map_prod_map _ _ measurable_fst measurable_fst]
  simp only [markedPoissonLaw, Measure.map_fst_prod, measure_univ, one_smul]

/-- The same literal total count is the sum of the two original Poisson counts. -/
theorem map_originalCubeReserve_totalCount (q : ℕ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] (rate : ℝ≥0) :
    (twoMarkedCloudLaw q ℝ ℝ α β rate).map
      (fun cloud ↦ (cloud.1.1 : ℝ) + (cloud.2.1 : ℝ)) =
      ((poissonMeasure rate).prod (poissonMeasure rate)).map
        (fun counts ↦ (counts.1 : ℝ) + (counts.2 : ℝ)) := by
  change (twoMarkedCloudLaw q ℝ ℝ α β rate).map
    ((fun counts : ℕ × ℕ ↦ (counts.1 : ℝ) + (counts.2 : ℝ)) ∘
      (fun cloud ↦ (cloud.1.1, cloud.2.1))) = _
  rw [← Measure.map_map (by fun_prop) (by fun_prop), map_originalCubeReserve_countPair]

/-- In the actual full-array lift the global total count has this exact law.
The lift preserves all prior bad-cut events and correlations; the count is not
assumed independent of the selected exceptional event. -/
theorem hasLaw_originalReserveUnitInput_globalCount_of_fullArrays
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (J : ProbabilityMeasure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
    (hright : (J : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      Prod.snd = twoMarkedCloudLaw q ℝ ℝ α β
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)
    (hfull : ∀ᵐ p ∂(J : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      ((originalReserveUnitInputReadout q θ hθ hθ1 p.1).2 :
        Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.2)) :
    HasLaw (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
        (originalReserveUnitInputReadout q θ hθ hθ1 p.1))
      (((poissonMeasure (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal).prod
        (poissonMeasure (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal)).map
          (fun counts ↦ (counts.1 : ℝ) + (counts.2 : ℝ)))
      (J : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) := by
  have hcount : ∀ᵐ p ∂(J : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
        (originalReserveUnitInputReadout q θ hθ hθ1 p.1) = (p.2.1.1 : ℝ) + (p.2.2.1 : ℝ) := by
    filter_upwards [hfull] with p hp
    exact (originalInputWindow_counts_eq_fullArrays _ _ _ hp).2
  refine ⟨((measurable_originalScreeningActualCount
    (measurableSet_originalOrientedTraffic_cube b R)).comp
      ((measurable_originalReserveUnitInputReadout q θ hθ hθ1).comp measurable_fst)).aemeasurable, ?_⟩
  calc
    _ = (J : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
        (fun p ↦ (p.2.1.1 : ℝ) + (p.2.2.1 : ℝ)) := Measure.map_congr hcount
    _ = (twoMarkedCloudLaw q ℝ ℝ α β
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal).map
        (fun cloud ↦ (cloud.1.1 : ℝ) + (cloud.2.1 : ℝ)) := by
      rw [show (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
        (p.2.1.1 : ℝ) + (p.2.2.1 : ℝ)) =
        (fun cloud : TwoMarkedCloudSpace q ℝ ℝ ↦ (cloud.1.1 : ℝ) + (cloud.2.1 : ℝ)) ∘ Prod.snd from rfl,
        ← Measure.map_map (by fun_prop) measurable_snd, hright]
    _ = _ := map_originalCubeReserve_totalCount q α β _

end OTSelector.Reconstruction
