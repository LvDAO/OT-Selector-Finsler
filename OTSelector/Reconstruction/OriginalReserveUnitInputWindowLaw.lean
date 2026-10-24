import OTSelector.Reconstruction.OriginalReserveUnitInputLaw
import OTSelector.Reconstruction.OriginalReserveOrientedWindowJoining

/-! The actual unit input and literal same-frame unit-volume arrays have exactly the same whole-window readout law. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology Module Manifold
open scoped ENNReal NNReal BigOperators Classical ContDiff
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

omit [BorelSpace E] in
/-- The true unit-intensity whole-input law, not a selected-port law, supplies
the literal unit-volume Poisson array readout on this same chosen physical cube. -/
theorem originalReserve_unitInput_orientedWindow_readoutLaw
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M₀ N : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hq : 0 < finrank ℝ S.covector.ker) {θ R : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hR : 0 < R) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    (legalOriginalIntensityReserveLaw M₀ N θ hθ hθ1 :
      Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).map
      (fun scene ↦ legalInputRestrictionLocal
        ((Prod.fst ∘ Prod.fst) ⁻¹' originalCenteredPhysicalCubeRegion b (2 * R)) scene.2) =
      (twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν
        (volume (originalCenteredPhysicalCubeRegion b (2 * R))).toNNReal).map
        (fun cloud ↦ legalInputTwoBlockLocal _ (originalMappedReserveCloudArrays _
          (originalOrientedRawCubePhysicalMap b R) cloud)) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  let K := originalCenteredPhysicalCubeRegion b (2 * R)
  let U : Set (LegalColoredInputPoint (finrank ℝ S.covector.ker)) := (Prod.fst ∘ Prod.fst) ⁻¹' K
  have hU : MeasurableSet U :=
    (measurableSet_originalOrientedTraffic_cube b R).preimage (measurable_fst.comp measurable_fst)
  let f : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) →
      LocalFiniteMeasure (LegalColoredInputPoint (finrank ℝ S.covector.ker)) :=
    fun scene ↦ legalInputRestrictionLocal U scene.2
  let g : TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ →
      LocalFiniteMeasure (LegalColoredInputPoint (finrank ℝ S.covector.ker)) :=
    fun cloud ↦ legalInputTwoBlockLocal _ (originalMappedReserveCloudArrays _
      (originalOrientedRawCubePhysicalMap b R) cloud)
  have hf : Measurable f := (measurable_legalInputRestrictionLocal hU).comp measurable_snd
  have hg : Measurable g := (measurable_legalInputTwoBlockLocal _).comp
    (measurable_originalMappedReserveCloudArrays _ (measurable_originalOrientedRawCubePhysicalMap b R))
  obtain ⟨J, hleft, hright, heq⟩ := D.exists_originalReserve_orientedWindow_joining M₀ b hR
  have hM : (M₀.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))).map f =
      (twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν (volume K).toNNReal).map g := by
    rw [← hleft, ← hright, Measure.map_map hf measurable_fst, Measure.map_map hg measurable_snd]
    apply Measure.map_congr
    filter_upwards [heq] with p hp
    exact Subtype.ext hp
  have hwhole := originalReserveUnitInputLaw_map_input_eq_original hq M₀ N hθ hθ1
  have hcut := congrArg (fun P : Measure (LocalFiniteMeasure
      (LegalColoredInputPoint (finrank ℝ S.covector.ker))) ↦
        P.map (legalInputRestrictionLocal U)) hwhole
  rw [Measure.map_map (measurable_legalInputRestrictionLocal hU) measurable_snd,
    Measure.map_map (measurable_legalInputRestrictionLocal hU) measurable_snd] at hcut
  exact hcut.trans hM

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
