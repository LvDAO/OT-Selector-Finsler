import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCutCost

/-! All finitely many actual cut bad events jointly pay the same actual input-count cost. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

private theorem tendsto_quadratic_finite_union_probability_zero
    {Ω I : Type*} [MeasurableSpace Ω] [Fintype I] (P : Measure Ω)
    (B : I → ℝ → Set Ω)
    (hB : ∀ i, Tendsto (fun R : ℝ ↦ R^2*P.real (B i R)) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦ R^2*P.real (⋃ i, B i R)) atTop (𝓝 0) := by
  have hl : Tendsto (fun R : ℝ ↦ ∑ i, R^2*P.real (B i R)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ ↦ hB i)
  apply squeeze_zero' (Eventually.of_forall (fun R ↦ mul_nonneg (sq_nonneg R) measureReal_nonneg)) ?_ hl
  apply Eventually.of_forall
  intro R
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (measureReal_iUnion_fintype_le (μ := P) (fun i ↦ B i R)) (sq_nonneg R)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The union of every actual finite-grid full-main cut bad event has a genuine measurable
envelope and negligible actual two-input-count weighted quadratic cost, on this same frame.
The actual cut probabilities and original count laws are produced internally. -/
theorem OriginalSeedConditionalMoments.tendsto_all_originalScreening_cutBadEnvelope_count_cost_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {I : Type*} [Fintype I] (cuts ε : I → ℝ)
    (hcuts : ∀ a, D.lo + (S.level : ℝ) ≤ cuts a) (hε : ∀ a, 0 < ε a)
    (hj : ∀ a k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (D.lo + (S.level : ℝ)) (cuts a)) scene k) 2 (Q.law : Measure _))
    (hproj : ∀ a i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _)
          (Ioc (D.lo + (S.level : ℝ)) (cuts a))) (hj a) (originalEuclideanNormalReadout (b i))) = 0) :
    let bad := fun R ↦ ⋃ a, originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts a) (ε a)
    (∀ R, MeasurableSet (bad R)) ∧
    (∀ R, (⋃ a, {scene | ε a*volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤
      |originalOrientedStageFullCutError S w b R (cuts a) scene|}) ⊆ bad R) ∧
    Tendsto (fun R : ℝ ↦ R^2 *
      ((∫ scene, (bad R).indicator (originalScreeningPhysicalCubeActualCount b R) scene
        ∂(Q.law : Measure _)) / volume.real (originalCenteredPhysicalCubeRegion b (2*R))))
      atTop (𝓝 0) := by
  let bad := fun R ↦ ⋃ a, originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts a) (ε a)
  have hm (R : ℝ) : MeasurableSet (bad R) := MeasurableSet.iUnion (fun a ↦
    (originalScreeningActualCutBadEnvelope_spec S w (Q.law : Measure _) b R (cuts a) (ε a)).1)
  refine ⟨hm, ?_, ?_⟩
  · intro R
    exact iUnion_mono (fun a ↦
      (originalScreeningActualCutBadEnvelope_spec S w (Q.law : Measure _) b R (cuts a) (ε a)).2.1)
  · apply Q.tendsto_originalScreeningPhysicalCubeActualCount_bad_cost_zero hq b bad hm
    apply tendsto_quadratic_finite_union_probability_zero
    intro a
    have h := D.tendsto_originalOrientedStageFullCutError_quadratic_bad_probability_zero
      hF hw (by omega) hbounds Q b (hcuts a) (hj a) (hproj a) (hε a)
    apply h.congr'
    apply Eventually.of_forall
    intro R
    dsimp only
    rw [(originalScreeningActualCutBadEnvelope_spec S w (Q.law : Measure _) b R (cuts a) (ε a)).2.2]

end OTSelector.Reconstruction
