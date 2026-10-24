import OTSelector.Reconstruction.OriginalReserveUnitInputCounts

/-! Full unit arrays, reserve arrays and actual global counts stay in one established experiment. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The actual full and reserve arrays identify both literal total counts in
the same unit scene and retained main. No independence from the bad event is used. -/
theorem originalReserveUnitInput_fullArray_counts {q : ℕ}
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (p : OriginalReserveUnitExperimentSpace q) (full : TwoMarkedCloudSpace q ℝ ℝ)
    (hfull : ((originalReserveUnitInputReadout q θ hθ hθ1 p).2 :
        Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) full))
    (hdecomp : ((originalReserveUnitInputReadout q θ hθ hθ1 p).2 :
        Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      (((originalReserveMainSamplerReadout q θ hθ1 p).1).2 :
        Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) +
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.2.2)) :
    originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
      (originalReserveUnitInputReadout q θ hθ hθ1 p) = (full.1.1 : ℝ) + (full.2.1 : ℝ) ∧
    originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
      (originalReserveUnitInputReadout q θ hθ hθ1 p) =
        originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
          (originalReserveMainSamplerReadout q θ hθ1 p).1 +
            ((p.2.2.1.1 : ℝ) + (p.2.2.2.1 : ℝ)) := by
  constructor
  · exact (originalInputWindow_counts_eq_fullArrays _ _ _ hfull).2
  · exact (originalUnitInput_counts_eq_main_add_reserve _ _ _ _ _ hfull hdecomp).2

/-- Lifting to full arrays preserves the actual total-count identities together
with every established main/reserve marginal and their bad-cut correlations. -/
theorem ae_originalReserveUnitInput_lifted_fullCounts {q : ℕ}
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) (R : ℝ)
    (L : ProbabilityMeasure (OriginalReserveUnitExperimentSpace q))
    (J : ProbabilityMeasure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ))
    (hleft : (J : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      Prod.fst = (L : Measure (OriginalReserveUnitExperimentSpace q)))
    (hdecomp : ∀ᵐ p ∂(L : Measure (OriginalReserveUnitExperimentSpace q)),
      ((originalReserveUnitInputReadout q θ hθ hθ1 p).2 :
        Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      (((originalReserveMainSamplerReadout q θ hθ1 p).1).2 :
        Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) +
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.2.2))
    (hfull : ∀ᵐ p ∂(J : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      ((originalReserveUnitInputReadout q θ hθ hθ1 p.1).2 :
        Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.2)) :
    ∀ᵐ p ∂(J : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
        (originalReserveUnitInputReadout q θ hθ hθ1 p.1) = (p.2.1.1 : ℝ) + (p.2.2.1 : ℝ) ∧
      originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
        (originalReserveUnitInputReadout q θ hθ hθ1 p.1) =
          originalScreeningActualCount (originalCenteredPhysicalCubeRegion b (2 * R))
            (originalReserveMainSamplerReadout q θ hθ1 p.1).1 +
              ((p.1.2.2.1.1 : ℝ) + (p.1.2.2.2.1 : ℝ)) := by
  have hbase : ∀ᵐ p ∂(J : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)),
      ((originalReserveUnitInputReadout q θ hθ hθ1 p.1).2 :
        Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
      (((originalReserveMainSamplerReadout q θ hθ1 p.1).1).2 :
        Measure (LegalColoredInputPoint q)).restrict
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) +
      legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
        (originalOrientedRawCubePhysicalMap b R) p.1.2.2) := by
    have h : ∀ᵐ p ∂(J : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
        Prod.fst,
        ((originalReserveUnitInputReadout q θ hθ hθ1 p).2 :
          Measure (LegalColoredInputPoint q)).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
        (((originalReserveMainSamplerReadout q θ hθ1 p).1).2 :
          Measure (LegalColoredInputPoint q)).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) +
        legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q
          (originalOrientedRawCubePhysicalMap b R) p.2.2) := by
      rw [hleft]
      exact hdecomp
    exact ae_of_ae_map measurable_fst.aemeasurable h
  filter_upwards [hfull, hbase] with p hf hb
  exact originalReserveUnitInput_fullArray_counts θ hθ hθ1 b R p.1 p.2 hf hb

end OTSelector.Reconstruction
