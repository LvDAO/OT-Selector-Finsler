import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostCompleteBudget
import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualStageFrame
import OTSelector.Reconstruction.OriginalLegalScreeningExpectedCostFiniteValue

/-! The actual model chooses one frame and a reserve-independent complete expected-cost coefficient. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold TopologicalSpace
open scoped ENNReal NNReal Topology ContDiff BigOperators InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {α β : Measure ℝ}

/-- The original focal model chooses C before every tilt, matching, reserve
intensity and physical frame. Each true minimizer then supplies one common frame
for all stages and cuts, independent of reserve intensity and path cutoff.
The literal complete budget satisfies its actual expectation bound on every
original unit-main/raw-reserve experiment, with no frame, L2 or rate oracle. -/
theorem OriginalSeedConditionalMoments.exists_original_screening_completeCostBudget_frame
    (D : OriginalSeedConditionalMoments S w α β)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 4 < finrank ℝ S.covector.ker)
    {densityα densityβ : M → ℝ} {v : M → E → ℝ} (cα cβ : ℝ≥0∞)
    (hρα : Continuous densityα) (hρα0 : ∀ x, 0 ≤ densityα x)
    (hρβ : Continuous densityβ) (hρβ0 : ∀ x, 0 ≤ densityβ x)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ,E) old).target, 0 ≤ v old y)
    (hdensityα : PopulationSeedClockDensity S w (α.map (fun x : ℝ ↦ x-S.level)) densityα v cα.toReal)
    (hdensityβ : PopulationSeedClockDensity S w (β.map (fun x : ℝ ↦ x-S.level)) densityβ v cβ.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds α β gap diameter) (hgap : 0 < gap)
    {g : ℝ → ℝ → ℝ} {G : ℝ} (hg : Measurable (Function.uncurry g)) (hgb : ∀ x y, |g x y| ≤ G)
    {I J H : Type*} [Fintype I] [Fintype J] [Fintype H]
    (s t : I → ℝ)
    (cuts : J → ℝ) (hcuts : ∀ i, D.lo+(S.level : ℝ) ≤ cuts i) :
    let : IsProbabilityMeasure α := D.support.source.probability
    let : IsProbabilityMeasure β := D.support.target.probability
    ∃ C ≥ 0, (∀ a b v, |D.originalFocalKinetic gap a b v| ≤ C*∑ i, v i^2) ∧
    ∀ (τ : ℝ)
      (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β
        (D.originalFocalKinetic gap) g),
      (∀ Q' : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) α β
        (D.originalFocalKinetic gap) g, Q.value τ ≤ Q'.value τ) →
      let clocks : I ⊕ J → Set ℝ := Sum.elim (fun i ↦ Ioc (s i) (t i))
        (fun i ↦ Ioc (D.lo+(S.level : ℝ)) (cuts i))
      ∃ hL2 : ∀ a k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
          (originalEuclideanMollifier _) (clocks a) scene k) 2 (Q.law : Measure _),
      ∃ b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
        (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
      (∀ i a C, (translationFixedSubspace Q.sceneEuclideanKoopman (ℝ ∙ b i)ᗮ).starProjection
        (originalLinearCurrentReadoutLtwo (Q.law : Measure _)
          (originalSeedPathClockSetCurrent S w (originalEuclideanMollifier _) (clocks a))
          (hL2 a) C) = 0) ∧
      ∀ (rho r : ℝ), 0 < rho → ∀ (grid : OriginalStageClockGrid), 0 < r →
        (∀ i, α (grid.sourceCell i) = 0 ∨ β (grid.targetCell i) = 0) →
        (∀ k ≤ grid.count, 0 ≤ grid.clockSlabSurplus α β k) →
      ∀ (ε : J → ℝ), (∀ i, 0 < ε i) →
      ∀ (weight : I → ℝ) (K : I → ℝ → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ))
        (RS RT RCs RCt RDs RDt : H → Set ℝ),
        (∀ i, MeasurableSet (RS i)) → (∀ i, MeasurableSet (RT i)) →
        (∀ i, MeasurableSet (RCs i)) → (∀ i, MeasurableSet (RCt i)) →
        (∀ i, MeasurableSet (RDs i)) → (∀ i, MeasurableSet (RDt i)) →
      ∀ (ell : ℝ → ℝ), (∀ᶠ R in atTop, 0 ≤ ell R) → Tendsto ell atTop atTop →
        Tendsto (fun R ↦ ell R/R) atTop (𝓝 0) →
      let V := fun R ↦ volume.real (originalCenteredPhysicalCubeRegion b (2*R))
      let Law := fun R ↦ originalMainReserveExperimentLaw Q (Real.toNNReal rho *
        (volume (originalCenteredPhysicalCubeRegion b (2*R))).toNNReal)
      let B := fun R ↦ originalScreeningCompleteCostBudget S w Q b (fun i ↦ K i R)
        R (ell R) s t weight (fun i ↦ hL2 (Sum.inl i)) rho grid r cuts ε C (|τ| * G)
        RS RT RCs RCt RDs RDt τ
      (∀ R, 1 ≤ R → Integrable (B R) (Law R)) ∧
        ∀ δ > 0, ∀ᶠ R : ℝ in atTop, (∫ p, B R p ∂Law R)/V R ≤
          Q.value τ + (6*C*(Fintype.card H : ℝ)*(finrank ℝ S.covector.ker : ℝ)*
            dyadicMatchingConstant (finrank ℝ S.covector.ker))*rho^(1-2/(finrank ℝ S.covector.ker : ℝ)) +
            2*|τ| * G*rho+δ := by
  let : IsProbabilityMeasure α := D.support.source.probability
  let : IsProbabilityMeasure β := D.support.target.probability
  obtain ⟨C,hC,hkb⟩ := D.exists_originalFocalKinetic_quadratic_bound hF hw hgap hbounds
  refine ⟨C,hC,hkb,fun τ Q hmin ↦ ?_⟩
  obtain ⟨hL2,b,hproj,_hface,_hcut⟩ := D.exists_actualCanonical_screening_frame_cut_costs
    hF hw hq cα cβ hρα hρα0 hρβ hρβ0 hv hv0 hdensityα hdensityβ hbounds hgap
    hg hgb τ Q hmin (fun i ↦ Ioc (s i) (t i)) cuts hcuts
  refine ⟨hL2,b,hproj,?_⟩
  intro rho r hrho grid hr hmono hH ε hε weight K RS RT RCs RCt RDs RDt
    hRS hRT hRCs hRCt hRDs hRDt ell hell hlarge hsmall
  have hh := D.original_screening_completeCostBudget_expected_bound hF hw hq cα cβ
    hρα hρα0 hρβ hρβ0 hv hv0 hdensityα hdensityβ hbounds hgap hg hgb τ Q hmin
    b s t weight K (fun i ↦ hL2 (Sum.inl i))
    (fun a i ↦ hproj i (Sum.inl a) (originalEuclideanNormalReadout (b i)))
    hrho grid hr hmono hH cuts ε hcuts hε (fun i ↦ hL2 (Sum.inr i))
    (fun a i ↦ hproj i (Sum.inr a) (originalEuclideanNormalReadout (b i)))
    RS RT RCs RCt RDs RDt hRS hRT hRCs hRCt hRDs hRDt C (|τ| * G) hC hell hlarge hsmall
  simpa only [mul_assoc] using hh

end OTSelector.Reconstruction
