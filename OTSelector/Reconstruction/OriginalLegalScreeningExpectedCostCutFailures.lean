import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostCapacity
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetAllCutsBadCost
import OTSelector.Reconstruction.OriginalReserveRawClockGridPrefixDeviation

/-! The same frame pays actual full-main cut, raw reserve, block and deletion-capacity exceptions jointly. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {α β : Measure ℝ}

/-- The actual simultaneous bad observation retains the original main cut
envelopes and every genuine raw-prefix/block/deletion-capacity failure. -/
def originalScreeningAllFailure {I : Type*} [Fintype I]
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) (α β : Measure ℝ)
    (P : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (rho R : ℝ) (G : OriginalStageClockGrid) (r : ℝ) (cuts ε : I → ℝ) :
    Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
      TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ) :=
  {p | p.1 ∈ ⋃ i, originalScreeningActualCutBadEnvelope S w P b R (cuts i) (ε i)} ∪
    originalScreeningCapacityReserveFailure α β b rho R G r

/-- All rates here are produced from the true original cut currents, raw laws,
full block counts and capacities. The same whole-observation event has negligible
quadratic probability and negligible actual full-input-count weighted quadratic cost. -/
theorem OriginalSeedConditionalMoments.original_screening_allFailure_count_cost
    (D : OriginalSeedConditionalMoments S w α β)
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 4 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds α β gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β (D.originalFocalKinetic gap) g)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {rho r : ℝ} (hrho : 0 < rho) (G : OriginalStageClockGrid) (hr : 0 < r)
    (hmono : ∀ i, α (G.sourceCell i) = 0 ∨ β (G.targetCell i) = 0)
    (hH : ∀ k ≤ G.count, 0 ≤ G.clockSlabSurplus α β k)
    {I : Type*} [Fintype I] (cuts ε : I → ℝ)
    (hcuts : ∀ i, D.lo+(S.level : ℝ) ≤ cuts i) (hε : ∀ i, 0 < ε i)
    (hj : ∀ i k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (D.lo+(S.level : ℝ)) (cuts i)) scene k) 2
      (Q.law : Measure _))
    (hproj : ∀ a i, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
      (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
        (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _)
          (Ioc (D.lo+(S.level : ℝ)) (cuts a))) (hj a) (originalEuclideanNormalReadout (b i))) = 0) :
    let K := fun R ↦ originalCenteredPhysicalCubeRegion b (2*R)
    let L := fun R ↦ originalMainReserveExperimentLaw Q (Real.toNNReal rho * (volume (K R)).toNNReal)
    let bad := fun R ↦ originalScreeningAllFailure S w α β (Q.law : Measure _) b rho R G r cuts ε
    (∀ R, MeasurableSet (bad R)) ∧
      Tendsto (fun R : ℝ ↦ R^2*(L R).real (bad R)) atTop (𝓝 0) ∧
      Tendsto (fun R : ℝ ↦ R^2*((∫ p, (bad R).indicator
        (originalScreeningFullExperimentCount (K R)) p ∂L R)/volume.real (K R))) atTop (𝓝 0) := by
  let q := finrank ℝ S.covector.ker
  let L := fun R ↦ originalMainReserveExperimentLaw Q (Real.toNNReal rho *
    (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
  let cutbad := fun i R ↦ originalScreeningActualCutBadEnvelope S w (Q.law : Measure _) b R (cuts i) (ε i)
  let lifted := fun i R ↦ {p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ | p.1 ∈ cutbad i R}
  have hcm (i) (R) : MeasurableSet (cutbad i R) :=
    (originalScreeningActualCutBadEnvelope_spec S w (Q.law : Measure _) b R (cuts i) (ε i)).1
  have hm (R) : MeasurableSet
      (originalScreeningAllFailure S w α β (Q.law : Measure _) b rho R G r cuts ε) :=
    ((MeasurableSet.iUnion (fun i ↦ hcm i R)).preimage measurable_fst).union
      (measurableSet_originalScreeningCapacityReserveFailure b rho R G r)
  have hi (i) : Tendsto (fun R : ℝ ↦ R^2*(L R).real (lifted i R)) atTop (𝓝 0) := by
    have hc := D.tendsto_originalOrientedStageFullCutError_quadratic_bad_probability_zero
      hF hw (by omega) hbounds Q b (hcuts i) (hj i) (hproj i) (hε i)
    apply hc.congr'
    exact Eventually.of_forall fun R ↦ by
      have hset : lifted i R = cutbad i R ×ˢ (univ : Set (TwoMarkedCloudSpace q ℝ ℝ)) := by ext p; simp [lifted]
      change R^2*(Q.law : Measure _).real {scene | ε i *
          volume.real (originalCenteredPhysicalCubeRegion b (2*R)) ≤
            |originalOrientedStageFullCutError S w b R (cuts i) scene|} =
        R^2*(L R).real (lifted i R)
      apply congrArg (fun x : ℝ ↦ R^2*x)
      calc
        _ = (Q.law : Measure _).real (cutbad i R) :=
          (originalScreeningActualCutBadEnvelope_spec S w (Q.law : Measure _) b R (cuts i) (ε i)).2.2.symm
        _ = _ := by
          rw [hset]
          simp only [L,originalMainReserveExperimentLaw,measureReal_def,Measure.prod_prod,measure_univ,mul_one]
  have hcu := tendsto_quadratic_finite_union_measureReal_zero L lifted hi
  have hca := Q.tendsto_original_screening_capacityReserveFailure_probability hq b hrho G hr hmono hH
  have hsum := hcu.add hca
  simp only [add_zero] at hsum
  have hprob : Tendsto (fun R : ℝ ↦ R^2*(L R).real
      (originalScreeningAllFailure S w α β (Q.law : Measure _) b rho R G r cuts ε)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun R ↦ mul_nonneg (sq_nonneg R) measureReal_nonneg)) ?_ hsum
    exact Eventually.of_forall fun R ↦ by
      rw [← mul_add]
      have hset : {p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ |
          p.1 ∈ ⋃ i, cutbad i R} = ⋃ i, lifted i R := by ext p; simp [lifted]
      change R^2*(L R).real ({p | p.1 ∈ ⋃ i, cutbad i R} ∪ _) ≤ _
      rw [hset]
      simpa only [Set.ofPred_exists,Set.ofPred_mem_eq] using
        mul_le_mul_of_nonneg_left (measureReal_union_le (μ := L R) (⋃ i, lifted i R)
          (originalScreeningCapacityReserveFailure α β b rho R G r)) (sq_nonneg R)
  exact ⟨hm,hprob,Q.tendsto_original_screening_fullExperimentCount_bad_cost_zero hq b hrho.le _ hm hprob⟩

end OTSelector.Reconstruction
