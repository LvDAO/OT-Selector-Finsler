import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsBackground
import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockKeptBalance

/-! Actual global original reserve deletions produce zero same-frame block backgrounds. -/
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

/-- The actual scene and original reserve arrays with the genuine blockwise kept union. -/
def originalOrientedClockBlockKeptData
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (G : OriginalStageClockGrid) (μ ν : Measure ℝ)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))) (R ell : ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))
    (source target : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
    (Cs Ct : G.ClockSlabBlock μ ν → Set ℝ) :
    OriginalOrientedStageResidualDensityData S w b R ell where
  scene := scene
  sourceReserve := source
  targetReserve := target
  sourceKept := originalReserveBlocksKeptFin (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
    (G.sourceBlockCell μ ν) (G.targetBlockCell μ ν) Cs
    ((scene,target),source.1,fun i ↦ (source.2 i).2)
  targetKept := originalReserveBlocksKeptFin (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
    (G.targetBlockCell μ ν) (G.sourceBlockCell μ ν) Ct
    ((scene,source),target.1,fun i ↦ (target.2 i).2)

/-- Actual block deletion capacities on the unchanged original reserve arrays internally
produce kept support, literal main-plus-reserve balance and zero endpoint backgrounds.
No endpoint gamma, background measure or desired balanced-count premise is required. -/
theorem OriginalSeedConditionalMoments.ae_all_originalOrientedClockBlockKeptEndpoints_zero
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
      ∀ (source target : MarkedCloudSpace (finrank ℝ S.covector.ker) ℝ)
        (Cs Ct : G.ClockSlabBlock μ ν → Set ℝ),
      (∀ block, Cs block ⊆ G.sourceBlockCell μ ν block) →
      (∀ block, Ct block ⊆ G.targetBlockCell μ ν block) →
      (∀ block, originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
        (G.sourceBlockCell μ ν block) (G.targetBlockCell μ ν block)
        ((scene,target),source.1,fun i ↦ (source.2 i).2) ≤
          originalReserveBlockCount source.1 (fun i ↦ (source.2 i).2) (Cs block)) →
      (∀ block, originalReserveBlockExcess (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
        (G.targetBlockCell μ ν block) (G.sourceBlockCell μ ν block)
        ((scene,source),target.1,fun i ↦ (target.2 i).2) ≤
          originalReserveBlockCount target.1 (fun i ↦ (target.2 i).2) (Ct block)) →
      let A := originalOrientedClockBlockKeptData S w G μ ν b R ell scene source target Cs Ct
      (∀ k : Fin (G.count+1), G.clockSlabSurplus μ ν k.val = 0 →
        A.gamma (G.cut k.val) = 0 ∧ A.orientedBackgroundLaw (G.cut k.val) = 0) ∧
      ∀ block : G.ClockSlabBlock μ ν,
        A.orientedBackgroundLaw (G.cut block.lower.val) = 0 ∧
        A.orientedBackgroundLaw (G.cut block.upper.val) = 0 := by
  have : IsProbabilityMeasure μ := D.support.source.probability
  have : IsProbabilityMeasure ν := D.support.target.probability
  let η := legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law
  let π := η.map Prod.fst
  have : IsProbabilityMeasure η := Q.palm_probability
  have : IsProbabilityMeasure π := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hπ : Vlasov.IsCoupling π μ ν := by
    constructor
    · simpa only [π,η,Measure.map_map measurable_fst measurable_fst,Function.comp_def] using Q.source_clock
    · simpa only [π,η,Measure.map_map measurable_snd measurable_fst,Function.comp_def] using Q.target_clock
  have hweak : ∀ᵐ p ∂π, p.1 ≤ p.2 :=
    (ae_map_iff measurable_fst.aemeasurable (measurableSet_le measurable_fst measurable_snd)).mpr
      (Q.ae_palm_forward.mono fun _ hp ↦ hp.le)
  obtain ⟨h₀,hN,_⟩ := G.clockSlabSurplus_facts hδ hsep π hπ hs ht hmono hweak
  obtain ⟨hSdis,hTdis⟩ := G.blockCells_disjoint h₀ hN
  filter_upwards [D.ae_all_originalOrientedClockBlockEndpointGamma_zero hF hw Q G hδ hsep hs ht hmono b hell hR,
    D.ae_all_originalOrientedClockBlockEndpointBackground_zero hF hw Q G hδ hsep hs ht hmono b hell hR]
    with scene hgamma hbackground
  intro source target Cs Ct hCs hCt hsCap htCap
  let A := originalOrientedClockBlockKeptData S w G μ ν b R ell scene source target Cs Ct
  have hkeepS : ∀ i ∈ A.sourceKept, (A.sourceReserve.2 i).2 ∈ ⋃ j, G.sourceCell j := by
    intro i hi
    have hu := originalReserveBlocksKeptFin_mark_mem_union
      (originalCenteredPhysicalCubeRegion b (2*R)) 0 1
      (G.sourceBlockCell μ ν) (G.targetBlockCell μ ν) Cs
      ((scene,target),source.1,fun i ↦ (source.2 i).2) i hi
    simp only [OriginalStageClockGrid.sourceBlockCell,mem_iUnion] at hu
    obtain ⟨block,j,_,hj⟩ := hu
    exact mem_iUnion.mpr ⟨j,hj⟩
  have hkeepT : ∀ i ∈ A.targetKept, (A.targetReserve.2 i).2 ∈ ⋃ j, G.targetCell j := by
    intro i hi
    have hu := originalReserveBlocksKeptFin_mark_mem_union
      (originalCenteredPhysicalCubeRegion b (2*R)) 1 0
      (G.targetBlockCell μ ν) (G.sourceBlockCell μ ν) Ct
      ((scene,source),target.1,fun i ↦ (target.2 i).2) i hi
    simp only [OriginalStageClockGrid.targetBlockCell,mem_iUnion] at hu
    obtain ⟨block,j,_,hj⟩ := hu
    exact mem_iUnion.mpr ⟨j,hj⟩
  have hbal := originalReserveBlocksKeptFin_actual_balance
    (originalCenteredPhysicalCubeRegion b (2*R)) scene source target
    (G.sourceBlockCell μ ν) (G.targetBlockCell μ ν) Cs Ct hSdis hTdis hCs hCt hsCap htCap
  have hg := hgamma A rfl hkeepS hkeepT hbal
  have hb := hbackground A rfl hkeepS hkeepT hbal
  exact ⟨fun k hk ↦ ⟨(hg k hk).2,hb.1 k hk⟩,hb.2⟩

end OTSelector.Reconstruction
