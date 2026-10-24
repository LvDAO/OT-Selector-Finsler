import OTSelector.Reconstruction.OriginalIIDWholeCoreSceneKernel
import OTSelector.Reconstruction.OriginalIIDMaskedMacroStationarity

/-!
# Literal pair-plan Palm readout of one fixed original scene candidate

The full-scene and pair-plan joints are projections of the same prescribed Q.
Their own conditional laws commute with the pair-plan readout. The original
frame-owner translation then identifies the whole-core candidate's literal
pair law and its unnormalized cube Palm measure, without any energy or clock
assumption and without choosing a new weak law or sample subsequence.
-/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 20000

variable {q : ℕ}
local instance iidFixedCandidatePalmPointStandardBorel :
    StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidFixedCandidatePalmPlanPolish : PolishSpace
    (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidFixedCandidatePalmInputPolish : PolishSpace
    (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidFixedCandidatePalmPlanNonempty : Nonempty
    (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  ⟨⟨0, inferInstance⟩⟩
local instance iidFixedCandidatePalmInputNonempty : Nonempty
    (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := ⟨⟨0, inferInstance⟩⟩
local instance iidFixedCandidatePalmConfigurationTopology :
    TopologicalSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) :=
  LocalConfiguration.vagueTopology _
local instance iidFixedCandidatePalmConfigurationBorel :
    BorelSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) :=
  LocalConfiguration.vagueBorelSpace
local instance iidFixedCandidatePalmConfigurationPolish :
    PolishSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) :=
  LocalConfiguration.vaguePolishSpace

set_option quotPrecheck false
local notation "V" => (Fin q → ℝ)
local notation "X" => V × ℝ
local notation "PairScene" => CavityLocalScene X X
local notation "Scene" => OriginalIIDMaskedMacroInputScene (Fin q)
local notation "Macro" => OriginalIIDMaskedMacroCarrier (0 : X)

/-- The original macro tag and full scene are read from the prescribed law. -/
def originalIIDFixedCandidateFullSceneJoint
    (Q : ProbabilityMeasure (Macro × Macro)) : Measure (V × Scene) :=
  (Q.map (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable.aemeasurable :
    Measure (V × Scene))

/-- The original macro tag and pair plan are read from the very same law. -/
def originalIIDFixedCandidatePairPlanJoint
    (Q : ProbabilityMeasure (Macro × Macro)) : Measure (V × PairScene) :=
  (Q.map (continuous_originalIIDMaskedMacroPlanProjection (0 : X)).measurable.aemeasurable :
    Measure (V × PairScene))

instance originalIIDFixedCandidateFullSceneJoint_probability
    (Q : ProbabilityMeasure (Macro × Macro)) :
    IsProbabilityMeasure (originalIIDFixedCandidateFullSceneJoint Q) := by
  unfold originalIIDFixedCandidateFullSceneJoint
  infer_instance

instance originalIIDFixedCandidatePairPlanJoint_probability
    (Q : ProbabilityMeasure (Macro × Macro)) :
    IsProbabilityMeasure (originalIIDFixedCandidatePairPlanJoint Q) := by
  unfold originalIIDFixedCandidatePairPlanJoint
  infer_instance

/-- The pair-plan joint is literally the first scene-coordinate projection
of the original full-scene joint, with its original tag unchanged. -/
theorem originalIIDFixedCandidatePairPlanJoint_eq_fullScene_projection
    (Q : ProbabilityMeasure (Macro × Macro)) :
    originalIIDFixedCandidatePairPlanJoint Q =
      (originalIIDFixedCandidateFullSceneJoint Q).map
        (Prod.map id (Prod.fst : Scene → PairScene)) := by
  unfold originalIIDFixedCandidatePairPlanJoint originalIIDFixedCandidateFullSceneJoint
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (measurable_id.prodMap measurable_fst)
    (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable]
  congr 1

/-- The own full-scene conditional law projects to the own pair-plan
conditional law on one common original root set. -/
theorem ae_originalIIDFixedCandidate_condKernel_pair_readout
    (Q : ProbabilityMeasure (Macro × Macro)) :
    (originalIIDFixedCandidatePairPlanJoint Q).fst =
      (originalIIDFixedCandidateFullSceneJoint Q).fst ∧
    ∀ᵐ c ∂(originalIIDFixedCandidateFullSceneJoint Q).fst,
      ((originalIIDFixedCandidateFullSceneJoint Q).condKernel c).map
        (Prod.fst : Scene → PairScene) =
          (originalIIDFixedCandidatePairPlanJoint Q).condKernel c := by
  have hproj := ae_condKernel_map_readout_eq_of_joint_projection
    (originalIIDFixedCandidateFullSceneJoint Q) (Prod.fst : Scene → PairScene) measurable_fst
  dsimp only at hproj
  simpa only [← originalIIDFixedCandidatePairPlanJoint_eq_fullScene_projection Q] using hproj

/-- The fixed whole-core candidate's pair marginal equals the original frame
joint's own conditional pair law at the translated original center. -/
theorem ae_owner_originalIIDFixedCandidate_pair_readout
    (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) (j : ℕ)
    (hroot : (originalIIDFixedCandidateFullSceneJoint (Q j)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
        (physicalScene_centered_unitCube_mass (Fin q)) : Measure V)) :
    ∀ᵐ c ∂(volume : Measure V).restrict (originalMacroFrameOwner q K j),
      (originalIIDWholeCoreSceneKernel K hK Q c).map (Prod.fst : Scene → PairScene) =
        (originalIIDFixedCandidatePairPlanJoint (Q j)).condKernel
          (c - originalMacroFrameCenter q j) := by
  let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
    (physicalScene_centered_unitCube_mass (Fin q))
  let B := (fun y : V => originalMacroFrameCenter q j + y) ⁻¹'
    originalMacroFrameOwner q K j
  have hB : MeasurableSet B :=
    (measurableSet_originalMacroFrameOwner q hK j).preimage
      (measurable_const.add measurable_id)
  have hproj := (ae_originalIIDFixedCandidate_condKernel_pair_readout (Q j)).2
  rw [hroot] at hproj
  have hprojB : ∀ᵐ y ∂(η : Measure V).restrict B,
      ((originalIIDFixedCandidateFullSceneJoint (Q j)).condKernel y).map
        (Prod.fst : Scene → PairScene) =
          (originalIIDFixedCandidatePairPlanJoint (Q j)).condKernel y :=
    ae_restrict_of_ae hproj
  apply (ae_originalMacroFrameOwner_iff q hK j _).mpr
  filter_upwards [hprojB, ae_restrict_mem hB] with y hy howner
  have howner' : originalMacroFrameCenter q j + y ∈ originalMacroFrameOwner q K j := howner
  rw [originalIIDWholeCoreSceneKernel_eq_on_owner K hK Q j howner']
  simp only [originalIIDFrameSceneKernel, Kernel.comap_apply,
    add_sub_cancel_left]
  exact hy

/-- The literal raw cube Palm measures of the same candidate pair readout
and original conditional pair law are equal on every original owner. -/
theorem ae_owner_originalIIDFixedCandidate_cubePalm_eq
    (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) (j : ℕ)
    (hroot : (originalIIDFixedCandidateFullSceneJoint (Q j)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
        (physicalScene_centered_unitCube_mass (Fin q)) : Measure V)) :
    ∀ᵐ c ∂(volume : Measure V).restrict (originalMacroFrameOwner q K j),
      cubePalm (Fin q) (physicalScenePairCampbell
        ((originalIIDWholeCoreSceneKernel K hK Q c).map (Prod.fst : Scene → PairScene))) =
      cubePalm (Fin q) (physicalScenePairCampbell
        ((originalIIDFixedCandidatePairPlanJoint (Q j)).condKernel
          (c - originalMacroFrameCenter q j))) := by
  filter_upwards [ae_owner_originalIIDFixedCandidate_pair_readout K hK Q j hroot] with c hc
  rw [hc]

/-- Any literal nonnegative Palm readout transfers to a measured or arbitrary
subset of one original owner, with the same unnormalized root restriction. -/
theorem lintegral_originalIIDFixedCandidate_cubePalm_eq_on_owner_subset
    (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) (j : ℕ)
    (hroot : (originalIIDFixedCandidateFullSceneJoint (Q j)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
        (physicalScene_centered_unitCube_mass (Fin q)) : Measure V))
    {A : Set V} (hA : A ⊆ originalMacroFrameOwner q K j)
    (F : V → PhysicalPairPalmMark (Fin q) → ℝ≥0∞) :
    (∫⁻ c in A, ∫⁻ mark, F c mark ∂cubePalm (Fin q) (physicalScenePairCampbell
      ((originalIIDWholeCoreSceneKernel K hK Q c).map (Prod.fst : Scene → PairScene))) ∂volume) =
    ∫⁻ c in A, ∫⁻ mark, F c mark ∂cubePalm (Fin q) (physicalScenePairCampbell
      ((originalIIDFixedCandidatePairPlanJoint (Q j)).condKernel
        (c - originalMacroFrameCenter q j))) ∂volume := by
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hA
    (ae_owner_originalIIDFixedCandidate_cubePalm_eq K hK Q j hroot)] with c hc
  rw [hc]

end OTSelector.Reconstruction
