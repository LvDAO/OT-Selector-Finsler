import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsGamma
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsLaws

/-! Actual same-frame background endpoint laws vanish at genuine balanced-block boundaries. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal BigOperators ContDiff Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Genuine law-tight cuts and actual blockwise original main-plus-surviving-reserve
count balance make the actual same-frame background law zero. In particular both ends
of every true constructed block vanish, without endpoint-background hypotheses. -/
theorem OriginalSeedConditionalMoments.ae_all_originalOrientedClockBlockEndpointBackground_zero
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    (G : OriginalStageClockGrid) {δ diameter : ℝ} (hδ : 0 < δ)
    (hsep : ConditionalClockSupportBounds μ ν δ diameter)
    (hs : ∀ᵐ x ∂μ, x ∈ ⋃ i, G.sourceCell i)
    (ht : ∀ᵐ y ∂ν, y ∈ ⋃ j, G.targetCell j)
    (hmono : ∀ i, μ (G.sourceCell i) = 0 ∨ ν (G.targetCell i) = 0)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalOrientedStageResidualDensityData S w b R ell, A.scene = scene →
      (∀ i ∈ A.sourceKept, (A.sourceReserve.2 i).2 ∈ ⋃ j, G.sourceCell j) →
      (∀ i ∈ A.targetKept, (A.targetReserve.2 i).2 ∈ ⋃ j, G.targetCell j) →
      (∀ block : G.ClockSlabBlock μ ν,
        originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2*R))
            (G.sourceBlockCell μ ν block) 0 A.scene +
          originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (G.sourceBlockCell μ ν block) =
        originalMainPhysicalBlockCount (originalCenteredPhysicalCubeRegion b (2*R))
            (G.targetBlockCell μ ν block) 1 A.scene +
          originalStageRemainingReserveClassCount A.targetReserve A.targetKept (G.targetBlockCell μ ν block)) →
      (∀ k : Fin (G.count+1), G.clockSlabSurplus μ ν k.val = 0 →
        A.orientedBackgroundLaw (G.cut k.val) = 0) ∧
      ∀ block : G.ClockSlabBlock μ ν,
        A.orientedBackgroundLaw (G.cut block.lower.val) = 0 ∧
        A.orientedBackgroundLaw (G.cut block.upper.val) = 0 := by
  filter_upwards [D.ae_all_originalOrientedClockBlockEndpointGamma_zero hF hw Q G hδ hsep hs ht hmono b hell hR,
    Q.ae_all_originalActiveCuts_zero_at_tight_clockSlabCuts (S := S) (w := w) G hδ hsep hs ht hmono]
    with scene hgamma hcuts
  intro A hA hkeptS hkeptT hcounts
  have hz (k : Fin (G.count+1)) (hk : G.clockSlabSurplus μ ν k.val = 0) :
      A.orientedBackgroundLaw (G.cut k.val) = 0 := by
    have hγ := (hgamma A hA hkeptS hkeptT hcounts k hk).2
    have hν : ∀ z, originalOrientedOmittedCutDensity S w b R ell (G.cut k.val) A.scene z = 0 := by
      intro z
      rw [hA]
      exact ((hcuts k hk).2.2 b R ell).2 z
    simp only [OriginalOrientedStageResidualDensityData.orientedBackgroundLaw,hν,hγ,add_zero,ENNReal.ofReal_zero]
    change (A.cubeMeasure.withDensity (0 : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ≥0∞)).map
      (EuclideanSpace.equiv _ ℝ).symm = 0
    rw [withDensity_zero,Measure.map_zero]
  exact ⟨hz,fun block ↦ ⟨hz block.lower block.consecutive.2.1,hz block.upper block.consecutive.2.2.1⟩⟩

end OTSelector.Reconstruction
