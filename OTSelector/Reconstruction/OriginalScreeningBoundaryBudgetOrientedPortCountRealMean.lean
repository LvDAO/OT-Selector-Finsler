import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetOrientedPortCountLimit

/-! Real measurable port-count costs for the same actual oriented original plans. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Any unused part of an actual marked window has an integrable real count. Its real
expectation equals its genuine Campbell count; finiteness follows from the full window. -/
theorem LegalWeightedStationaryPoissonMatching.original_unused_markedWindow_count_real_mean
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    (d : PhysicalPairPalmMark (Fin q) → Fin q → ℝ) (hd : Measurable d)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (hKfinite : volume K ≠ (⊤ : ℝ≥0∞))
    {A : Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))} (hA : MeasurableSet A) :
    let X := fun scene : LegalMarkedOptimalInputScene q ↦
      physicalScenePairKernel scene.1 ({a | a.1+d a.2 ∈ K} \ A)
    Measurable (fun scene ↦ (X scene).toReal) ∧
      Integrable (fun scene ↦ (X scene).toReal) (Q.law : Measure _) ∧
      (∫ scene, (X scene).toReal ∂(Q.law : Measure _)) =
        (∫⁻ scene, X scene ∂(Q.law : Measure _)).toReal := by
  let : IsProbabilityMeasure (legalMarkedJointPalm q Q.law) := Q.palm_probability
  let X := fun scene : LegalMarkedOptimalInputScene q ↦
    physicalScenePairKernel scene.1 ({a | a.1+d a.2 ∈ K} \ A)
  have hwindow : MeasurableSet {a : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) |
      a.1+d a.2 ∈ K} := hK.preimage (measurable_fst.add (hd.comp measurable_snd))
  have hm : Measurable X := (Kernel.measurable_coe physicalScenePairKernel (hwindow.diff hA)).comp measurable_fst
  have hmean : (∫⁻ scene, X scene ∂(Q.law : Measure _)) ≠ (⊤ : ℝ≥0∞) := by
    apply ne_top_of_le_ne_top hKfinite
    calc
      _ ≤ ∫⁻ scene, physicalScenePairKernel scene.1 {a | a.1+d a.2 ∈ K}
          ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)) :=
        lintegral_mono (fun _ ↦ measure_mono sdiff_subset)
      _ = volume K := by
        simpa only [mem_univ, and_true, measure_univ, mul_one] using
          Q.lintegral_original_markedWindow_count d hd hK MeasurableSet.univ
  exact ⟨hm.ennreal_toReal, integrable_toReal_of_lintegral_ne_top hm.aemeasurable hmean,
    integral_toReal hm.aemeasurable (ae_lt_top hm hmean)⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Both actual oriented port plans have measurable integrable real masses, and these
real expectations equal the original nonnegative expected counts. -/
theorem originalOrientedStagePortCounts_real_means
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ) :
    let A := originalOrientedPathLengthRetained S w b R ell
    let K := originalCenteredPhysicalCubeRegion b (2*R)
    let X := fun scene ↦ (originalStageWindowSourcePortPlan A K scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ
    let Y := fun scene ↦ (originalStageWindowTargetPortPlan A K scene :
      Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ
    (Measurable (fun scene ↦ (X scene).toReal) ∧ Integrable (fun scene ↦ (X scene).toReal) (Q.law : Measure _) ∧
      (∫ scene, (X scene).toReal ∂(Q.law : Measure _)) = (∫⁻ scene, X scene ∂(Q.law : Measure _)).toReal) ∧
    (Measurable (fun scene ↦ (Y scene).toReal) ∧ Integrable (fun scene ↦ (Y scene).toReal) (Q.law : Measure _) ∧
      (∫ scene, (Y scene).toReal ∂(Q.law : Measure _)) = (∫⁻ scene, Y scene ∂(Q.law : Measure _)).toReal) := by
  dsimp only
  have hK := measurableSet_originalOrientedTraffic_cube b R
  have hA := measurableSet_originalOrientedPathLengthRetained S hF hw b R ell
  simp_rw [originalStageWindowSourcePortPlan_mass_eq_pairKernel hA hK,
    originalStageWindowTargetPortPlan_mass_eq_pairKernel hA hK]
  have hfinite : volume (originalCenteredPhysicalCubeRegion b (2*R)) ≠ (⊤ : ℝ≥0∞) := by
    rw [volume_originalOrientedTraffic_cube]
    exact isCompact_Icc.measure_ne_top
  constructor
  · simpa only [add_zero] using (Q.original_unused_markedWindow_count_real_mean
      (fun _ ↦ 0) measurable_const hK hfinite hA)
  · exact Q.original_unused_markedWindow_count_real_mean Prod.snd measurable_snd hK hfinite hA

/-- The sum of the actual source and target port masses is a measurable integrable
random budget whose expectation is o(the same physical cube volume), for paying bounded
endpoint smoothing costs without a path-length moment or iid port law. -/
theorem OriginalSeedConditionalMoments.originalOrientedStagePortCount_mean_density_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop) (hsmall : Tendsto (fun R ↦ ell R/R) atTop (𝓝 0)) :
    let X := fun R scene ↦ (originalStageWindowSourcePortPlan
      (originalOrientedPathLengthRetained S w b R (ell R))
      (originalCenteredPhysicalCubeRegion b (2*R)) scene :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ
    let Y := fun R scene ↦ (originalStageWindowTargetPortPlan
      (originalOrientedPathLengthRetained S w b R (ell R))
      (originalCenteredPhysicalCubeRegion b (2*R)) scene :
        Measure (LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker))) univ
    (∀ R, Measurable (fun scene ↦ (X R scene).toReal+(Y R scene).toReal) ∧
      Integrable (fun scene ↦ (X R scene).toReal+(Y R scene).toReal) (Q.law : Measure _)) ∧
    Tendsto (fun R : ℝ ↦
      (∫ scene, (X R scene).toReal+(Y R scene).toReal ∂(Q.law : Measure _)) /
        volume.real (originalCenteredPhysicalCubeRegion b (2*R))) atTop (𝓝 0) := by
  dsimp only
  have hmeans (R : ℝ) := originalOrientedStagePortCounts_real_means hF hw Q b R (ell R)
  refine ⟨fun R ↦ ⟨(hmeans R).1.1.add (hmeans R).2.1,
    (hmeans R).1.2.1.add (hmeans R).2.2.1⟩, ?_⟩
  have hS := tendsto_originalOrientedStage_sourcePort_count_density_zero hF hw Q b hell hlarge hsmall
  have hT := D.tendsto_originalOrientedStage_targetPort_count_density_zero hF hw Q b hell hlarge hsmall
  have hl := hS.add hT
  simp only [add_zero] at hl
  apply hl.congr'
  apply Eventually.of_forall
  intro R
  dsimp only
  rw [integral_add (hmeans R).1.2.1 (hmeans R).2.2.1,
    (hmeans R).1.2.2, (hmeans R).2.2.2, add_div]

end OTSelector.Reconstruction
