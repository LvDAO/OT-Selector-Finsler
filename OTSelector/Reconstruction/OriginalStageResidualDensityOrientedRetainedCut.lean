import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedEqualMass

/-! The genuine same-frame retained cut is finite, deep, and preserves its raw smoothed mass. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- The anchor measure of every actual path restriction is exactly the pushforward of the
same unchanged original edge restriction. -/
theorem originalStageRestrictedPathPlan_anchorKernel_eq {q : ℕ}
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A)
    (scene : LegalMarkedOptimalInputScene q) :
    (physicalScenePairKernel scene.1).restrict A =
      (originalStageRestrictedPathPlan A scene : Measure (LegalMarkedPhysicalEdge q)).map physicalPairAnchor := by
  rw [physicalScenePairKernel_apply, Measure.restrict_map measurable_physicalPairAnchor hA]
  rfl

/-- Every finite cut supported one unit inside the actual oriented cube preserves its
original mass under the same physical raw mollifier. Reflection and its genuine unit mass
supply this fact internally. -/
theorem originalOrientedStageRawSmoothing_integrable_mass_of_deep {q : ℕ}
    (ρ : Measure (Fin q → ℝ)) [IsFiniteMeasure ρ]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 1 ≤ R)
    (hρ : ∀ᵐ x ∂ρ, x ∈ originalCenteredPhysicalCubeRegion b (2 * (R - 1))) :
    Integrable (fun z ↦ ∫ x, originalEuclideanMollifier q (x - z) ∂ρ)
      (volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))) ∧
    (∫ z in originalCenteredPhysicalCubeRegion b (2 * R),
      ∫ x, originalEuclideanMollifier q (x - z) ∂ρ) = ρ.real univ := by
  let toMarked : (Fin q → ℝ) → LegalMarkedPhysicalPoint q := fun x ↦ (x, 0)
  have hm : Measurable toMarked := measurable_id.prodMk measurable_const
  let π := ρ.map toMarked
  have hπ : ∀ᵐ p ∂π, p.1 ∈ originalCenteredPhysicalCubeRegion b (2 * R) := by
    apply (ae_map_iff hm.aemeasurable
      ((isCompact_originalStagePhysicalCube b (2 * R)).measurableSet.preimage measurable_fst)).mpr
    filter_upwards [hρ] with x hx
    exact originalCenteredPhysicalCubeRegion_mono b (by linarith : 2 * (R - 1) ≤ 2 * R) hx
  obtain ⟨hint, hmass⟩ := originalOrientedStageReflectedClassDensity_integrable_mass b hR π hπ univ
  have hsame : originalOrientedStageReflectedClassDensity b R univ π =ᵐ[
      volume.restrict (originalCenteredPhysicalCubeRegion b (2 * R))]
      fun z ↦ ∫ x, originalEuclideanMollifier q (x - z) ∂ρ := by
    filter_upwards [ae_restrict_mem (isCompact_originalStagePhysicalCube b (2 * R)).measurableSet] with z hz
    have hmap : Measurable (fun p : LegalMarkedPhysicalPoint q ↦ (z, p.1)) :=
      measurable_const.prodMk measurable_fst
    have hφ : Measurable (fun p : LegalMarkedPhysicalPoint q ↦
        originalCanonicalOrientedReflectedKernel b R z p.1) := by
      simpa only [Function.comp_def] using (measurable_originalCanonicalOrientedReflectedKernel b R).comp hmap
    unfold originalOrientedStageReflectedClassDensity
    simp only [mem_univ, ofPred_true, Measure.restrict_univ]
    rw [show π = ρ.map toMarked from rfl, integral_map hm.aemeasurable hφ.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hρ] with x hx
    rw [originalCanonicalOrientedReflectedKernel_eq_raw_of_inner b hz hx]
    exact coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial q) _ _
      (fun i ↦ abs_sub_comm (z i) (x i))
  refine ⟨hint.congr hsame, ?_⟩
  rw [← integral_congr_ae hsame, hmass]
  simp [π, measureReal_def, Measure.map_apply hm MeasurableSet.univ]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Actual original same-frame retained cut occupation is finite and is supported in the
same actual inner cube. Both facts come from the true retained restriction and path geometry. -/
theorem ae_originalOrientedRetainedCut_finite_inner
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * (originalStageFrameCollarFactor b * ell) ≤ R) (c : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsFiniteMeasure (originalRestrictedSceneActiveCutMeasure S w
        (originalOrientedPathLengthRetained S w b R ell) c scene) ∧
      ∀ᵐ x ∂originalRestrictedSceneActiveCutMeasure S w (originalOrientedPathLengthRetained S w b R ell) c scene,
        x ∈ originalCenteredPhysicalCubeRegion b (2 * (R - originalStageFrameCollarFactor b * ell)) := by
  filter_upwards [D.ae_originalOrientedStagePlans_finite hF hw Q b hell hR,
    D.ae_ae_original_pairKernel_interior_forward Q] with scene hfinite hlegal
  let A := originalOrientedPathLengthRetained S w b R ell
  let B : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :=
    {a | a.2.1.1 < c ∧ c < a.2.1.2}
  have hA := measurableSet_originalOrientedPathLengthRetained S hF hw b R ell
  have hB : MeasurableSet B := (measurableSet_lt measurable_snd.fst.fst measurable_const).inter
    (measurableSet_lt measurable_const measurable_snd.fst.snd)
  let σ := (physicalScenePairKernel scene.1).restrict A
  let : IsFiniteMeasure (originalStageRestrictedPathPlan A scene :
    Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) := hfinite.1
  have hanchor : σ = (originalStageRestrictedPathPlan A scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))).map physicalPairAnchor :=
    originalStageRestrictedPathPlan_anchorKernel_eq hA scene
  let : IsFiniteMeasure σ := by rw [hanchor]; infer_instance
  have hpos : Measurable (fun a : (Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      a.1 + originalSeedPathOffset S w c a.2) :=
    measurable_fst.add ((measurable_originalSeedPathOffset S hF hw c).comp measurable_snd)
  constructor
  · change IsFiniteMeasure ((σ.restrict B).map (fun a ↦ a.1 + originalSeedPathOffset S w c a.2))
    infer_instance
  · change ∀ᵐ x ∂(σ.restrict B).map (fun a ↦ a.1 + originalSeedPathOffset S w c a.2), _
    apply (ae_map_iff hpos.aemeasurable (isCompact_originalStagePhysicalCube b _).measurableSet).mpr
    filter_upwards [ae_restrict_of_ae (ae_restrict_of_ae hlegal),
      ae_restrict_of_ae (ae_restrict_mem hA), ae_restrict_mem hB] with a ha hret hactive
    change a.1 + originalSeedPathOffset S w c a.2 ∈ originalCenteredPhysicalCubeRegion b
      (2 * (R - originalStageFrameCollarFactor b * ell))
    simpa only [originalSeedCompletePath_eq_anchor_add_offset] using
      D.originalOrientedPathLengthRetained_path_mem_innerCube hF hw b hell hR hret ha.1 ha.2.1
        ⟨hactive.1.le, hactive.2.le⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
