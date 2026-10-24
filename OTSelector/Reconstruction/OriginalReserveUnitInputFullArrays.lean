import OTSelector.Reconstruction.OriginalReserveUnitInputWindowLaw
import OTSelector.Reconstruction.OriginalReserveUnitInputExperiment

/-! Add literal full unit-input arrays while preserving the entire established original experiment. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology Module Manifold
open scoped ENNReal NNReal BigOperators Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance originalReserveUnitFullArraysInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance originalReserveUnitFullArraysPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

omit [BorelSpace E] in
/-- Lift an actual unit-input experiment to literal full original arrays on
this same physical cube. Its entire prior marginal is preserved, so all existing
marks-only reserve laws and main correlations survive unchanged. The new full
array is an identity witness, never an iid-conditioning auxiliary coordinate. -/
theorem exists_originalReserve_unitInput_fullArrays_lift
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M₀ N : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hq : 0 < finrank ℝ S.covector.ker) {θ R : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hR : 0 < R)
    (L : ProbabilityMeasure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker)))
    (hunitlaw : (L : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker))).map
      (originalReserveUnitInputReadout (finrank ℝ S.covector.ker) θ hθ hθ1) =
      (legalOriginalIntensityReserveLaw M₀ N θ hθ hθ1 :
        Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∃ J : ProbabilityMeasure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ),
      (J : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)).map Prod.fst =
        (L : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker))) ∧
      (J : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)).map Prod.snd =
        twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν
          (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal ∧
      ∀ᵐ p ∂(J : Measure (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) ×
        TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ)),
        ((originalReserveUnitInputReadout (finrank ℝ S.covector.ker) θ hθ hθ1 p.1).2 :
          Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker))).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) =
          legalInputTwoBlockMeasure _ (originalMappedReserveCloudArrays _
            (originalOrientedRawCubePhysicalMap b R) p.2) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let : StandardBorelSpace (MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ) := by infer_instance
  let : Nonempty (OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker)) :=
    nonempty_of_isProbabilityMeasure (L : Measure (OriginalReserveUnitExperimentSpace _))
  let K := originalCenteredPhysicalCubeRegion b (2 * R)
  let U : Set (LegalColoredInputPoint (finrank ℝ S.covector.ker)) := (Prod.fst ∘ Prod.fst) ⁻¹' K
  have hU : MeasurableSet U :=
    (measurableSet_originalOrientedTraffic_cube b R).preimage (measurable_fst.comp measurable_fst)
  let f : OriginalReserveUnitExperimentSpace (finrank ℝ S.covector.ker) →
      LocalFiniteMeasure (LegalColoredInputPoint (finrank ℝ S.covector.ker)) :=
    fun p ↦ legalInputRestrictionLocal U
      (originalReserveUnitInputReadout _ θ hθ hθ1 p).2
  let a : TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ →
      LocalFiniteMeasure (LegalColoredInputPoint (finrank ℝ S.covector.ker)) :=
    fun cloud ↦ legalInputTwoBlockLocal _ (originalMappedReserveCloudArrays _
      (originalOrientedRawCubePhysicalMap b R) cloud)
  have hf : Measurable f := (measurable_legalInputRestrictionLocal hU).comp
    (measurable_snd.comp (measurable_originalReserveUnitInputReadout _ θ hθ hθ1))
  have ha : Measurable a := (measurable_legalInputTwoBlockLocal _).comp
    (measurable_originalMappedReserveCloudArrays _ (measurable_originalOrientedRawCubePhysicalMap b R))
  have hwindow : Measurable (fun scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ↦
      legalInputRestrictionLocal U scene.2) :=
    (measurable_legalInputRestrictionLocal hU).comp measurable_snd
  have hlaw : (L : Measure (OriginalReserveUnitExperimentSpace _)).map f =
      (twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν (volume K).toNNReal).map a := by
    change (L : Measure (OriginalReserveUnitExperimentSpace _)).map
      ((fun scene ↦ legalInputRestrictionLocal U scene.2) ∘
        originalReserveUnitInputReadout _ θ hθ hθ1) = _
    rw [← Measure.map_map hwindow (measurable_originalReserveUnitInputReadout _ θ hθ hθ1), hunitlaw]
    exact D.originalReserve_unitInput_orientedWindow_readoutLaw M₀ N b hq hθ hθ1 hR
  obtain ⟨J, hleft, hright, heq⟩ := exists_joint_original_input_readout
    (L : Measure (OriginalReserveUnitExperimentSpace _))
    (twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν (volume K).toNNReal) f a hf ha hlaw
  refine ⟨J, hleft, hright, ?_⟩
  filter_upwards [heq] with p hp
  exact congrArg (fun μ : LocalFiniteMeasure (LegalColoredInputPoint (finrank ℝ S.covector.ker)) ↦
    (μ : Measure (LegalColoredInputPoint (finrank ℝ S.covector.ker)))) hp

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
