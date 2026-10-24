import OTSelector.Reconstruction.OriginalReserveFullUnitInputExperiment
import OTSelector.Probability.PoissonCountDeviationTransfer
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockExcessBudget

/-! Actual theta-reserve class counts and fluctuations on the same full unit-input joining. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace OriginalReserveFullUnitInputExperiment
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
  {Main Reserve : LegalWeightedStationaryPoissonMatching q α β kin g}
  {b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))}
  {θ R : ℝ} {hθ : 0 < θ} {hθ1 : θ < 1}
  (X : OriginalReserveFullUnitInputExperiment Main Reserve b θ hθ hθ1 R)

/-- The same full joining retains the entire literal original theta-reserve sampler. -/
theorem fullLaw_reserve_sampler :
    (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
      (fun p ↦ p.1.2.2) = twoMarkedCloudLaw q ℝ ℝ α β
        (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) := by
  have hm : Measurable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveMainSamplerReadout q θ hθ1 p.1) :=
    (measurable_originalReserveMainSamplerReadout q θ hθ1).comp measurable_fst
  change (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)).map
    (Prod.snd ∘ (fun p ↦ originalReserveMainSamplerReadout q θ hθ1 p.1)) = _
  rw [← Measure.map_map measurable_snd hm, X.fullLaw_main_sampler,
    Measure.map_snd_prod, measure_univ, one_smul]

/-- The unchanged two original reserve class counts have true independent
Poisson(theta V alpha(S), theta V beta(T)) laws on this full experiment. -/
theorem hasLaw_reserveBlockCount_pair {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    let rate := Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal
    HasLaw (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) S,
        originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) T))
      ((poissonMeasure (rate * (α S).toNNReal)).prod (poissonMeasure (rate * (β T).toNNReal)))
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) := by
  dsimp only
  have hraw : HasLaw
      (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦ p.1.2.2)
      (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal θ *
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal))
      (X.fullLaw : Measure (OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ)) :=
    ⟨(by fun_prop), X.fullLaw_reserve_sampler⟩
  have h := (hasLaw_originalReserveObservedBlockCount_pair (q := q) α β _ hS hT).fun_comp hraw
  change HasLaw (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
    (originalReserveObservedBlockCount S p.1.2.2.1, originalReserveObservedBlockCount T p.1.2.2.2)) _ _ at h
  simpa only [originalReserveObservedBlockCount_eq_natCount] using h

/-- Exact actual source reserve count law, before deletion or own-position conditioning. -/
theorem hasLaw_sourceReserveBlockCount {C : Set ℝ} (hC : MeasurableSet C) :
    let a := (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (α C).toNNReal
    HasLaw (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) C)
      (poissonMeasure a) (X.fullLaw : Measure _) := by
  dsimp only
  have h := X.hasLaw_reserveBlockCount_pair hC hC
  have hf : HasLaw (Prod.fst : ℕ × ℕ → ℕ)
      (poissonMeasure ((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (α C).toNNReal))
      ((poissonMeasure ((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (α C).toNNReal)).prod
        (poissonMeasure ((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (β C).toNNReal))) :=
    ⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩
  exact hf.fun_comp h

/-- Exact actual target reserve count law in the same joined experiment. -/
theorem hasLaw_targetReserveBlockCount {C : Set ℝ} (hC : MeasurableSet C) :
    let a := (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (β C).toNNReal
    HasLaw (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) C)
      (poissonMeasure a) (X.fullLaw : Measure _) := by
  dsimp only
  have h := X.hasLaw_reserveBlockCount_pair hC hC
  have hf : HasLaw (Prod.snd : ℕ × ℕ → ℕ)
      (poissonMeasure ((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (β C).toNNReal))
      ((poissonMeasure ((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (α C).toNNReal)).prod
        (poissonMeasure ((Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (β C).toNNReal))) :=
    ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩
  exact hf.fun_comp h

/-- The actual source class count has the sharp mean absolute Poisson deviation. -/
theorem sourceReserveBlockCount_deviation {C : Set ℝ} (hC : MeasurableSet C) :
    let a := (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (α C).toNNReal
    Integrable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      |(originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) C : ℝ) - (a : ℝ)|)
      (X.fullLaw : Measure _) ∧
    (∫ p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ,
      |(originalReserveBlockCount p.1.2.2.1.1 (fun i ↦ (p.1.2.2.1.2 i).2) C : ℝ) - (a : ℝ)|
      ∂(X.fullLaw : Measure _)) ≤ Real.sqrt (a : ℝ) := by
  dsimp only
  exact poissonCount_deviation_of_hasLaw _ _
    (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) hC) _
    (X.hasLaw_sourceReserveBlockCount hC)

/-- The actual target class count has the sharp mean absolute Poisson deviation. -/
theorem targetReserveBlockCount_deviation {C : Set ℝ} (hC : MeasurableSet C) :
    let a := (Real.toNNReal θ * (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal) * (β C).toNNReal
    Integrable (fun p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ ↦
      |(originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) C : ℝ) - (a : ℝ)|)
      (X.fullLaw : Measure _) ∧
    (∫ p : OriginalReserveUnitExperimentSpace q × TwoMarkedCloudSpace q ℝ ℝ,
      |(originalReserveBlockCount p.1.2.2.2.1 (fun i ↦ (p.1.2.2.2.2 i).2) C : ℝ) - (a : ℝ)|
      ∂(X.fullLaw : Measure _)) ≤ Real.sqrt (a : ℝ) := by
  dsimp only
  exact poissonCount_deviation_of_hasLaw _ _
    (measurable_originalReserveBlockCount (by fun_prop) (by fun_prop) hC) _
    (X.hasLaw_targetReserveBlockCount hC)

end OriginalReserveFullUnitInputExperiment
end OTSelector.Reconstruction
