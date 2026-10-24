import OTSelector.Reconstruction.MarkedStationaryValuePhysicalPairAnchorReadout
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryEdgeReadoutSecondMoment
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalPalmTightness

/-!
# The extracted original Palm is the true Palm of the same scene limit

One actual nonzero compact source test transfers compact mark tests to compact
edge tests through the full edge-anchor homeomorphism. Original Poisson input
second moments make their expectations converge. Campbell factorization and
uniqueness of the two actual limits identify the extracted probability Palm
with the original weak scene's own true Palm, without assuming fullness.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
local instance markedStationaryValueLegalTruePalmIdentificationInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalTruePalmIdentificationPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Every actual weak scene limit of genuine unit-intensity original laws
has at most unit true Palm mass. The source-window density bound is produced
from each original full probability Palm; no input or moment oracle is given. -/
theorem legalMarkedJointPalm_univ_le_one_of_genuineStationary_tendsto
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hweak : Tendsto (fun n ↦ (M n).law) atTop (𝓝 Q)) :
    legalMarkedJointPalm q Q univ ≤ 1 := by
  have hpair := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n ↦ (M n).law) Q hweak continuous_fst
  have hbound : ∀ (U : Set (Fin q → ℝ)), IsOpen U → ∀ n,
      (∫⁻ scene, ∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ U},
        ENNReal.ofReal ((1 : ℝ)) ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q))
        ∂(legalMarkedInputPairLaw q (M n).law :
          Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))) ≤
        volume U * 1 := by
    intro U hU n
    have hB : MeasurableSet (U ×ˢ (univ : Set (PhysicalPairPalmMark (Fin q)))) :=
      hU.measurableSet.prod MeasurableSet.univ
    have heq : (physicalScenePairCampbell (legalMarkedInputPairLaw q (M n).law :
        Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))))
        (U ×ˢ univ) =
      ∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
        {e | e.1.1 ∈ U} ∂(legalMarkedInputPairLaw q (M n).law :
          Measure (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) := by
      rw [physicalScenePairCampbell, Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
      apply lintegral_congr
      intro scene
      rw [physicalScenePairKernel_apply, Measure.map_apply measurable_physicalPairAnchor hB]
      congr 1
      ext e
      simp only [mem_preimage, mem_prod, mem_univ, and_true, mem_ofPred_eq, physicalPairAnchor]
    have : IsProbabilityMeasure (legalMarkedJointPalm q (M n).law) := (M n).palm_probability
    simp only [ENNReal.ofReal_one, lintegral_one, Measure.restrict_apply_univ]
    rw [← heq, (M n).campbell_eq_volume_prod_palm, Measure.prod_prod, measure_univ]
  have h := lintegral_cubePalm_le_of_weak_energy_density_bound
    (fun n ↦ legalMarkedInputPairLaw q (M n).law) hpair
    (fun _ ↦ (1 : ℝ)) continuous_const (fun _ ↦ zero_le_one) 1 hbound
  simpa only [ENNReal.ofReal_one, lintegral_one, legalMarkedJointPalm,
    legalMarkedInputPairLaw] using h

/-- The actual same-sequence scene and full-displacement Palm limits are
compatible. The only source moment is the limiting scene's own finite unit
mass; no equality between an independently selected Palm and that scene is
assumed, and no second displacement moment is needed. -/
theorem legalMarkedJointPalm_eq_of_genuineStationary_weak_of_truePalm_weak
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : ℕ → LegalWeightedStationaryPoissonMatching q α β kin g)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hweak : Tendsto (fun n ↦ (M n).law) atTop (𝓝 Q))
    (hstat : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q))
      (Q : Measure (LegalMarkedOptimalInputScene q)))
    (η : ProbabilityMeasure (PhysicalPairPalmMark (Fin q)))
    (hPalm : Tendsto (fun n ↦ (M n).truePalmProbability) atTop (𝓝 η)) :
    legalMarkedJointPalm q Q = (η : Measure (PhysicalPairPalmMark (Fin q))) := by
  have hpalm : legalMarkedJointPalm q Q univ < ∞ :=
    (legalMarkedJointPalm_univ_le_one_of_genuineStationary_tendsto M Q hweak).trans_lt ENNReal.one_lt_top
  have hunit : (∫⁻ s, (s.1.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)}
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) < ∞ := by
    rw [← legalMarkedJointPalm_univ_eq_expected_sourceUnitMass]
    exact hpalm
  have : IsFiniteMeasure (legalMarkedJointPalm q Q) := ⟨hpalm⟩
  obtain ⟨h, hh0, hh⟩ := LocalFiniteMeasure.exists_compact_cutoff
    (isCompact_singleton (x := (0 : Fin q → ℝ)))
  have hhzero : h (0 : Fin q → ℝ) = 1 := hh0 (mem_singleton _)
  have hpositive : 0 < ∫ x, h x ∂(volume : Measure (Fin q → ℝ)) :=
    h.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : Fin q → ℝ))
      h.hasCompactSupport (fun x ↦ (hh x).1)
      (by rw [hhzero]; exact one_ne_zero)
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let H := physicalAnchoredProductTest q h f
  have hedge := (integrable_and_tendsto_original_stationary_edgeTest_integral M hweak H).2.2.2
  have hmark := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hPalm)
    f.toBoundedContinuousFunction
  have hscaled := hmark.const_mul (∫ x, h x ∂(volume : Measure (Fin q → ℝ)))
  change Tendsto (fun n ↦ (∫ x, h x ∂(volume : Measure (Fin q → ℝ))) *
    ∫ m, f m ∂((M n).truePalmProbability : Measure (PhysicalPairPalmMark (Fin q)))) atTop
      (𝓝 ((∫ x, h x ∂(volume : Measure (Fin q → ℝ))) *
        ∫ m, f m ∂(η : Measure (PhysicalPairPalmMark (Fin q))))) at hscaled
  have hfinite (n : ℕ) :
      (∫ s, LocalFiniteMeasure.testIntegral s.1.1 H
        ∂((M n).law : Measure (LegalMarkedOptimalInputScene q))) =
        (∫ x, h x ∂(volume : Measure (Fin q → ℝ))) *
          ∫ m, f m ∂((M n).truePalmProbability : Measure (PhysicalPairPalmMark (Fin q))) :=
    (M n).integral_physicalAnchoredProductTest h f
  have hscaled' : Tendsto
      (fun n ↦ ∫ s, LocalFiniteMeasure.testIntegral s.1.1 H
        ∂((M n).law : Measure (LegalMarkedOptimalInputScene q))) atTop
      (𝓝 ((∫ x, h x ∂(volume : Measure (Fin q → ℝ))) *
        ∫ m, f m ∂(η : Measure (PhysicalPairPalmMark (Fin q))))) := by
    simpa only [hfinite] using hscaled
  have heq := tendsto_nhds_unique hedge hscaled'
  rw [integral_physicalAnchoredProductTest_of_stationary Q hstat hunit h f] at heq
  exact mul_left_cancel₀ hpositive.ne' heq

end OTSelector.Reconstruction
