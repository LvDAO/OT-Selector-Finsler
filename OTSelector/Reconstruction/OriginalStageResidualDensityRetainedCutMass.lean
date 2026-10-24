import OTSelector.Reconstruction.OriginalStageResidualDensityEqualMass

/-! Actual retained cut occupation is finite, interior, and preserves its literal smoothed mass. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- A finite positive measure supported at least one unit inside the actual cube has
raw compact-kernel smoothing of exactly its own original mass. -/
theorem originalStageRawSmoothing_integrable_mass_of_deep {q : ℕ}
    (ρ : Measure (Fin q → ℝ)) [IsFiniteMeasure ρ]
    {η : (Fin q → ℝ) → ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (hηone : ∫ x, η x = 1) (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w : Fin q → ℝ, (∀ i, |v i| = |w i|) → η v = η w)
    {M R : ℝ} (hηM : ∀ x, |η x| ≤ M) (hR : 1 ≤ R)
    (hρ : ∀ᵐ x ∂ρ, x ∈ haarRootCube (Fin q) (R - 1)) :
    Integrable (fun z ↦ ∫ x, η (x - z) ∂ρ) (volume.restrict (haarRootCube (Fin q) R)) ∧
      (∫ z in haarRootCube (Fin q) R, ∫ x, η (x - z) ∂ρ) = ρ.real univ := by
  let toMarked : (Fin q → ℝ) → LegalMarkedPhysicalPoint q := fun x ↦ (x, 0)
  have hm : Measurable toMarked := measurable_id.prodMk measurable_const
  let π := ρ.map toMarked
  have hπ : ∀ᵐ p ∂π, p.1 ∈ haarRootCube (Fin q) R := by
    apply (ae_map_iff hm.aemeasurable (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [hρ] with x hx
    constructor <;> intro i
    · have hi := hx.1 i
      dsimp at hi ⊢
      linarith
    · have hi := hx.2 i
      dsimp at hi ⊢
      linarith
  obtain ⟨hint, hmass⟩ := originalStageReflectedClassDensity_integrable_mass hη hηI hηone
    hηsupport hηeven hηM hR π hπ univ
  have hsame : originalStageReflectedClassDensity η R univ π =ᵐ[
      volume.restrict (haarRootCube (Fin q) R)] fun z ↦ ∫ x, η (x - z) ∂ρ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    have hφ : Measurable (fun p : LegalMarkedPhysicalPoint q ↦
        originalCubeReflectedKernel η R z p.1) :=
      (measurable_originalCubeReflectedKernel hη R).comp (measurable_const.prodMk measurable_fst)
    unfold originalStageReflectedClassDensity
    simp only [mem_univ, ofPred_true, Measure.restrict_univ]
    rw [show π = ρ.map toMarked from rfl, integral_map hm.aemeasurable hφ.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [hρ] with x hx
    rw [originalCubeReflectedKernel_eq_kernel_of_inner hηsupport hz hx]
    exact hηeven _ _ (fun i ↦ abs_sub_comm (z i) (x i))
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

/-- The same original length-retained active cut is genuinely finite and stays inside the
actual path-retention inner cube. No retained-cut count or geometry callback is assumed. -/
theorem ae_originalRetainedCut_finite_inner
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 0 ≤ ell) (hR : 2 * ell ≤ R) (c : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      IsFiniteMeasure (originalRestrictedSceneActiveCutMeasure S w
        (originalPathLengthRetained S w R ell) c scene) ∧
      ∀ᵐ x ∂originalRestrictedSceneActiveCutMeasure S w
        (originalPathLengthRetained S w R ell) c scene,
        x ∈ haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - ell) := by
  filter_upwards [ae_originalPathRetainedPlan_finite hF hw Q R ell,
    D.ae_ae_original_pairKernel_interior_forward Q] with scene hfinite hlegal
  let A := originalPathLengthRetained S w R ell
  let B : Set ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) :=
    {a | a.2.1.1 < c ∧ c < a.2.1.2}
  have hA := measurableSet_originalPathLengthRetained S hF hw R ell
  have hB : MeasurableSet B :=
    (measurableSet_lt measurable_snd.fst.fst measurable_const).inter
      (measurableSet_lt measurable_const measurable_snd.fst.snd)
  have hpos : Measurable (fun a : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      a.1 + originalSeedPathOffset S w c a.2) :=
    measurable_fst.add ((measurable_originalSeedPathOffset S hF hw c).comp measurable_snd)
  have hmass : physicalScenePairKernel scene.1 A < (∞ : ℝ≥0∞) := by
    rw [← originalPathRetainedPlan_mass_eq_pairKernel hF hw R ell scene]
    exact hfinite
  constructor
  · constructor
    change (((physicalScenePairKernel scene.1).restrict A).restrict B).map
      (fun a ↦ a.1 + originalSeedPathOffset S w c a.2) univ < (∞ : ℝ≥0∞)
    rw [Measure.map_apply hpos MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ, Measure.restrict_apply hB]
    exact (measure_mono inter_subset_right).trans_lt hmass
  · change ∀ᵐ x ∂(((physicalScenePairKernel scene.1).restrict A).restrict B).map
      (fun a ↦ a.1 + originalSeedPathOffset S w c a.2), _
    apply (ae_map_iff hpos.aemeasurable measurableSet_Icc).mpr
    filter_upwards [ae_restrict_of_ae (ae_restrict_of_ae hlegal),
      ae_restrict_of_ae (ae_restrict_mem hA), ae_restrict_mem hB] with a ha hret hactive
    change a.1 + originalSeedPathOffset S w c a.2 ∈
      haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - ell)
    simpa only [originalSeedCompletePath_eq_anchor_add_offset] using
      D.originalPathLengthRetained_path_mem_innerCube hF hw hell hR hret ha.1 ha.2.1
        ⟨hactive.1.le, hactive.2.le⟩

/-- Every actual retained cut has exactly its original mass after raw smoothing on the
same physical cube. Interior retention and kernel mass preservation are proved internally. -/
theorem ae_originalRetainedCut_rawSmoothing_mass
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) (c : ℝ)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hη : Measurable η) (hηI : Integrable η volume) (hηone : ∫ x, η x = 1)
    (hηsupport : ∀ x, 1 ≤ ‖x‖ → η x = 0)
    (hηeven : ∀ v w, (∀ i, |v i| = |w i|) → η v = η w)
    {M : ℝ} (hηM : ∀ x, |η x| ≤ M) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      (∫ z in haarRootCube _ R, ∫ x, η (x - z)
        ∂originalRestrictedSceneActiveCutMeasure S w (originalPathLengthRetained S w R ell) c scene) =
        (originalRestrictedSceneActiveCutMeasure S w
          (originalPathLengthRetained S w R ell) c scene).real univ := by
  filter_upwards [D.ae_originalRetainedCut_finite_inner hF hw Q (by linarith) hR c]
    with scene hscene
  have := hscene.1
  apply (originalStageRawSmoothing_integrable_mass_of_deep _ hη hηI hηone hηsupport hηeven
    hηM (by linarith) ?_).2
  filter_upwards [hscene.2] with x hx
  constructor <;> intro i
  · have hi := hx.1 i
    dsimp at hi ⊢
    linarith
  · have hi := hx.2 i
    dsimp at hi ⊢
    linarith

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
