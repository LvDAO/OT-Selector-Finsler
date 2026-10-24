import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalMeanMarginalFullness
import OTSelector.Probability.InvariantFactorConditioning

/-!
# Conditioning a genuine original stationary matching on an invariant event

Original full matching and forward support survive absolutely continuous
conditioning. The same whole original input law fixes actual Palm clocks and
normalization. A literal measure domination preserves finite original energy.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
local instance markedStationaryValueLegalConditionedMatchingInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalConditionedMatchingPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Literal domination of the original scene law dominates its own actual
unnormalized probability Palm. The comparison is linear in the scene law. -/
theorem legalMarkedJointPalm_le_smul_of_law_le
    {q : ℕ} (Q P : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) {c : ℝ≥0∞}
    (hQP : (Q : Measure (LegalMarkedOptimalInputScene q)) ≤ c • (P : Measure _)) :
    legalMarkedJointPalm q Q ≤ c • legalMarkedJointPalm q P := by
  have hpair := Measure.map_mono hQP measurable_fst
  rw [Measure.map_smul] at hpair
  have hcamp : physicalScenePairCampbell (legalMarkedInputPairLaw q Q : Measure
      (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) ≤
      c • physicalScenePairCampbell (legalMarkedInputPairLaw q P : Measure
        (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q))) := by
    rw [physicalScenePairCampbell, physicalScenePairCampbell, ← Measure.bind_smul]
    apply Measure.le_iff.mpr
    intro B hB
    rw [Measure.bind_apply hB (Kernel.measurable _).aemeasurable,
      Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
    exact lintegral_mono' hpair (fun _ ↦ le_rfl)
  have h := Measure.map_mono (Measure.restrict_mono (subset_refl (palmUnitCube (Fin q) ×ˢ (univ : Set (PhysicalPairPalmMark (Fin q))))) hcamp) measurable_snd
  simpa only [legalMarkedJointPalm, cubePalm, Measure.restrict_smul, Measure.map_smul] using h

/-- The actual original scene law conditioned on a positive original event. -/
def LegalWeightedStationaryPoissonMatching.conditionedLaw
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (A : Set (LegalMarkedOptimalInputScene q))
    (hpos : (M.law : Measure (LegalMarkedOptimalInputScene q)) A ≠ 0) :
    ProbabilityMeasure (LegalMarkedOptimalInputScene q) :=
  ⟨(M.law : Measure (LegalMarkedOptimalInputScene q))[|A], cond_isProbabilityMeasure hpos⟩

/-- The same actual full-displacement Palm has finite original energy after
conditioning on any positive original event, without an unweighted moment. -/
theorem LegalWeightedStationaryPoissonMatching.conditionedPalm_le
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (A : Set (LegalMarkedOptimalInputScene q))
    (hpos : (M.law : Measure (LegalMarkedOptimalInputScene q)) A ≠ 0) :
    legalMarkedJointPalm q (M.conditionedLaw A hpos) ≤
      ((M.law : Measure (LegalMarkedOptimalInputScene q)) A)⁻¹ • legalMarkedJointPalm q M.law := by
  apply legalMarkedJointPalm_le_smul_of_law_le
  change ((M.law : Measure (LegalMarkedOptimalInputScene q)) A)⁻¹ •
    (M.law : Measure (LegalMarkedOptimalInputScene q)).restrict A ≤ _
  gcongr
  exact Measure.restrict_le_self

/-- Whole original input-law equality transfers each actual compact input
Laplace readout, independently of any already established matching class. -/
theorem integral_legalMarkedInputSceneLaplace_eq_of_inputLaw_eq
    {q : ℕ} (Q P : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hinput : (Q : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (P : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd)
    (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x) :
    (∫ s, legalMarkedInputSceneLaplace q F hF s
      ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
      ∫ s, legalMarkedInputSceneLaplace q F hF s
        ∂(P : Measure (LegalMarkedOptimalInputScene q)) := by
  have h := congrArg (fun R : Measure (LocalFiniteMeasure (LegalColoredInputPoint q)) ↦
    ∫ μ, legalInputMeasureLaplace ⟨F, hF⟩ μ ∂R) hinput
  rw [integral_map measurable_snd.aemeasurable (legalInputMeasureLaplace ⟨F, hF⟩).continuous.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable (legalInputMeasureLaplace ⟨F, hF⟩).continuous.aestronglyMeasurable] at h
  exact h

/-- A shift-invariant event with its unchanged whole original input law
produces a genuine matching in the very same weighted class. The input-law
identity is later generated by the ergodic original input factor. -/
def LegalWeightedStationaryPoissonMatching.conditionedMatching
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (A : Set (LegalMarkedOptimalInputScene q)) (hA : MeasurableSet A)
    (hpos : (M.law : Measure (LegalMarkedOptimalInputScene q)) A ≠ 0)
    (hinv : ∀ v : Fin q → ℝ, legalMarkedInputSceneReroot q v ⁻¹' A =ᵐ[(M.law : Measure _)] A)
    (hinput : (M.conditionedLaw A hpos : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) :
    LegalWeightedStationaryPoissonMatching q α β kin g := by
  let Q := M.conditionedLaw A hpos
  have habs : (Q : Measure (LegalMarkedOptimalInputScene q)) ≪
      (M.law : Measure (LegalMarkedOptimalInputScene q)) := cond_absolutelyContinuous
  have hfull : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      IsFullOriginalInputMatching q s := habs.ae_le M.full_matching
  have hstat (v : Fin q → ℝ) : MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q)) := by
    have hres : MeasurePreserving (legalMarkedInputSceneReroot q v)
        ((M.law : Measure (LegalMarkedOptimalInputScene q)).restrict A)
        ((M.law : Measure (LegalMarkedOptimalInputScene q)).restrict A) := by
      simpa only [Measure.restrict_congr_set (hinv v)] using (M.stationary v).restrict_preimage hA
    exact hres.smul_measure ((M.law : Measure (LegalMarkedOptimalInputScene q)) A)⁻¹
  have hmeans := physicalScene_intensities_eq_inputColors q Q
    (hfull.mono (fun _ hs ↦ ⟨hs.source_marginal, hs.target_marginal⟩))
  have hi0 := (legalMarkedInputColorIntensity_eq_of_inputLaw_eq Q M.law hinput 0).trans
    M.inputColorIntensities_eq_volume_prod.1
  have hi1 := (legalMarkedInputColorIntensity_eq_of_inputLaw_eq Q M.law hinput 1).trans
    M.inputColorIntensities_eq_volume_prod.2
  have hnorm := probability_cubePalm_physicalScenePairCampbell_clock_marginals _
    (measurePreserving_legalMarkedInputPairLaw q Q hstat) α β
    (hmeans.1.trans hi0) (hmeans.2.trans hi1)
  have hc : ((M.law : Measure (LegalMarkedOptimalInputScene q)) A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hpos
  exact {
    law := Q
    stationary := hstat
    full_matching := hfull
    forward := habs.ae_le M.forward
    input_laplace := by
      intro S hS F hF hzero
      rw [integral_legalMarkedInputSceneLaplace_eq_of_inputLaw_eq Q M.law hinput F hF]
      exact M.input_laplace S hS F hF hzero
    palm_probability := hnorm.1
    source_clock := hnorm.2.1
    target_clock := hnorm.2.2
    kinetic_integrable := (M.kinetic_integrable.smul_measure hc).mono_measure (M.conditionedPalm_le A hpos)
    probe_integrable := (M.probe_integrable.smul_measure hc).mono_measure (M.conditionedPalm_le A hpos) }

end OTSelector.Reconstruction
