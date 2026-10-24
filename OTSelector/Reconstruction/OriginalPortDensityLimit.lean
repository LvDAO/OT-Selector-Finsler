import OTSelector.Reconstruction.OriginalTargetPortCountExpectation
import OTSelector.Reconstruction.OriginalPathLengthTail
import OTSelector.Reconstruction.NormalizedHaarCubeCount

/-! # The actual original source and target ports have vanishing volume density -/
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option linter.unusedSectionVars false

/-- A literal collar-and-tail upper bound suffices for vanishing normalized
expected count; no count-law property of the selected cloud is used. -/
theorem tendsto_normalized_haarCube_count_of_collar_tail
    (ι : Type*) [Fintype ι] {ell : ℝ → ℝ} {k : ℝ} (hk : 0 ≤ k)
    (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0))
    {z tail : ℝ → ℝ≥0∞} (htailfin : ∀ R, tail R ≠ (⊤ : ℝ≥0∞))
    (htail : Tendsto (fun R ↦ (tail R).toReal) atTop (𝓝 0))
    (hz : ∀ᶠ R in atTop, z R ≤
      volume (haarRootCube ι R \ haarRootCube ι (R - k * ell R)) +
        volume (haarRootCube ι R) * tail R) :
    Tendsto (fun R ↦ (z R).toReal / volume.real (haarRootCube ι R)) atTop (𝓝 0) := by
  have hmodel : Tendsto (fun R ↦
      1 - (1 - k * (ell R / R)) ^ Fintype.card ι + (tail R).toReal) atTop (𝓝 0) := by
    have hksmall : Tendsto (fun R ↦ k * (ell R / R)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hsmall
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub
      (((tendsto_const_nhds (x := (1 : ℝ))).sub hksmall).pow (Fintype.card ι))).add htail
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ div_nonneg ENNReal.toReal_nonneg measureReal_nonneg) _ hmodel
  filter_upwards [hell, hz, eventually_gt_atTop (0 : ℝ),
    eventually_collar_mul_le_radius (k := k) hsmall] with R hellR hzR hR hke
  exact (finite_and_normalized_count_le_haarCube_collar_tail ι hR hellR hk hke (htailfin R) hzR).2

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Both colors of the same unchanged matching have vanishing expected port
count per physical Haar volume for every diverging sublinear collar. -/
theorem tendsto_original_sourcePorts_density_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦
      (∫⁻ scene, physicalScenePairKernel scene.1 (originalPathSourcePorts S w R (ell R))
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))).toReal /
          volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)) atTop (𝓝 0) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    Q.palm_probability
  apply tendsto_normalized_haarCube_count_of_collar_tail
    (Fin (finrank ℝ S.covector.ker)) (k := 2)
    (tail := fun R ↦ (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
      {m | ell R < originalSeedPairPathLength S w m}) (by norm_num) hell hsmall
    (fun _ ↦ measure_ne_top _ _) _
    (Eventually.of_forall fun R ↦ lintegral_original_sourcePorts_le_boundary_and_pathTail hF hw Q R (ell R))
  exact (tendsto_original_truePalm_pathLength_tail_real hF hw Q).comp hlarge

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- The target count uses its own original marginal and the same retained edges,
not a distribution imposed on the adaptive port population. -/
theorem tendsto_original_targetPorts_density_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦
      (∫⁻ scene, physicalScenePairKernel scene.1 (originalPathTargetPorts S w R (ell R))
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))).toReal /
          volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)) atTop (𝓝 0) := by
  have : IsProbabilityMeasure (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law) :=
    Q.palm_probability
  apply tendsto_normalized_haarCube_count_of_collar_tail
    (Fin (finrank ℝ S.covector.ker)) (k := 3)
    (tail := fun R ↦ (legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)
      {m | ell R < originalSeedPairPathLength S w m}) (by norm_num) hell hsmall
    (fun _ ↦ measure_ne_top _ _)
    ((tendsto_original_truePalm_pathLength_tail_real hF hw Q).comp hlarge)
  filter_upwards [hell, eventually_collar_mul_le_radius (k := (3 : ℝ)) hsmall] with R hellR hR
  exact D.lintegral_original_targetPorts_le_boundary_and_pathTail hF hw Q hellR hR

/-- A single concrete deterministic square-root collar works for both actual
colors of every original genuine weighted matching. -/
theorem tendsto_original_bothPorts_sqrt_density_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g) :
    Tendsto (fun R : ℝ ↦
      (∫⁻ scene, physicalScenePairKernel scene.1 (originalPathSourcePorts S w R (Real.sqrt R))
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))).toReal /
          volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)) atTop (𝓝 0) ∧
    Tendsto (fun R : ℝ ↦
      (∫⁻ scene, physicalScenePairKernel scene.1 (originalPathTargetPorts S w R (Real.sqrt R))
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))).toReal /
          volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)) atTop (𝓝 0) :=
  ⟨tendsto_original_sourcePorts_density_zero hF hw Q
      (Eventually.of_forall Real.sqrt_nonneg) sqrt_collar_limits.1 sqrt_collar_limits.2,
    D.tendsto_original_targetPorts_density_zero hF hw Q
      (Eventually.of_forall Real.sqrt_nonneg) sqrt_collar_limits.1 sqrt_collar_limits.2⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
