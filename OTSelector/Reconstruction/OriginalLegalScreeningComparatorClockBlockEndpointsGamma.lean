import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsCounts
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsScene
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedGoodCut

/-! True blockwise original count balance produces zero actual background gamma at tight cuts. -/
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

/-- Actual original main counts plus actual surviving reserve counts balance in every
true law-balanced block. On a single original-scene event this forces the literal port
plus reserve prefix, and hence the literal same-frame gamma, to vanish at every tight
block boundary. Zero gamma or zero active cut is never an input. -/
theorem OriginalSeedConditionalMoments.ae_all_originalOrientedClockBlockEndpointGamma_zero
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
      ∀ k : Fin (G.count+1), G.clockSlabSurplus μ ν k.val = 0 →
        A.portPrefix (G.cut k.val) + A.reservePrefix (G.cut k.val) = 0 ∧ A.gamma (G.cut k.val) = 0 := by
  have : IsProbabilityMeasure μ := D.support.source.probability
  have : IsProbabilityMeasure ν := D.support.target.probability
  let K := originalCenteredPhysicalCubeRegion b (2*R)
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
  have hRone : 1 ≤ R := by nlinarith [one_le_originalStageFrameCollarFactor b]
  have hgammas := ae_all_iff.mpr (fun k : Fin (G.count+1) ↦
    D.ae_all_originalOrientedStageGamma_eq_reservePrefix_add_fullCutError hF hw Q b hell hR hRone (G.cut k.val))
  filter_upwards [Q.ae_all_originalActiveCuts_zero_at_tight_clockSlabCuts (S := S) (w := w)
      G hδ hsep hs ht hmono,Q.ae_originalInputs_clockSlab_cover G hs ht,
    Q.ae_exists_originalStageMainPhysicalWindowArrays K (isCompact_originalStagePhysicalCube b (2*R)),
    hgammas] with scene hcuts hcover harrays hgamma
  obtain ⟨sourceMain,targetMain,harrays⟩ := harrays
  have hsArray : (legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ K} =
      ∑ i : Fin sourceMain.1, Measure.dirac (sourceMain.2 i) := by
    simpa only [originalStageRemainingReserveMeasure] using harrays.1
  have htArray : (legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ K} =
      ∑ i : Fin targetMain.1, Measure.dirac (targetMain.2 i) := by
    simpa only [originalStageRemainingReserveMeasure] using harrays.2
  have : IsFiniteMeasure ((legalInputColorMeasure _ scene.2 0).restrict {p | p.1 ∈ K}) := by
    rw [hsArray]
    infer_instance
  have : IsFiniteMeasure ((legalInputColorMeasure _ scene.2 1).restrict {p | p.1 ∈ K}) := by
    rw [htArray]
    infer_instance
  intro A hA hkeptS hkeptT hcounts k hk
  rw [hA] at hcounts
  let ρs := originalWindowReserveClockLaw K 0 scene A.sourceReserve A.sourceKept
  let ρt := originalWindowReserveClockLaw K 1 scene A.targetReserve A.targetKept
  have : IsFiniteMeasure ρs := by unfold ρs originalWindowReserveClockLaw; infer_instance
  have : IsFiniteMeasure ρt := by unfold ρt originalWindowReserveClockLaw; infer_instance
  have hρs := ae_originalWindowReserveClockLaw_mem K 0 scene A.sourceReserve A.sourceKept
    (MeasurableSet.iUnion fun _ ↦ measurableSet_Ico) hcover.1 hkeptS
  have hρt := ae_originalWindowReserveClockLaw_mem K 1 scene A.targetReserve A.targetKept
    (MeasurableSet.iUnion fun _ ↦ measurableSet_Ioc) hcover.2 hkeptT
  have hbal (block : G.ClockSlabBlock μ ν) :
      ρs.real (G.sourceBlockCell μ ν block) = ρt.real (G.targetBlockCell μ ν block) := by
    rw [originalWindowReserveClockLaw_real K 0 scene A.sourceReserve A.sourceKept (G.blockCells_measurable block).1,
      originalWindowReserveClockLaw_real K 1 scene A.targetReserve A.targetKept (G.blockCells_measurable block).2,
      originalMainPhysicalBlockCount_mass_of_original_array (isCompact_originalStagePhysicalCube b (2*R)).measurableSet
        (G.blockCells_measurable block).1 0 scene _ hsArray,
      originalMainPhysicalBlockCount_mass_of_original_array (isCompact_originalStagePhysicalCube b (2*R)).measurableSet
        (G.blockCells_measurable block).2 1 scene _ htArray]
    exact_mod_cast hcounts block
  have hpref := G.tight_prefix_masses_eq_of_block_balance h₀ hN ρs ρt hρs hρt hbal hk
  rw [originalWindowReserveClockLaw_real K 0 scene A.sourceReserve A.sourceKept measurableSet_Iio,
    originalWindowReserveClockLaw_real K 1 scene A.targetReserve A.targetKept measurableSet_Iic] at hpref
  simp only [Set.mem_Iio,Set.mem_Iic] at hpref
  have hprefix : originalStageMainInputWindowPrefix K (G.cut k.val) scene + A.reservePrefix (G.cut k.val) = 0 := by
    dsimp only [originalStageMainInputWindowPrefix,OriginalOrientedStageResidualDensityData.reservePrefix,
      originalStageRemainingReservePrefix]
    linarith only [hpref]
  have hAe : (⟨scene,A.sourceReserve,A.targetReserve,A.sourceKept,A.targetKept⟩ :
      OriginalOrientedStageResidualDensityData S w b R ell) = A := by
    cases A
    cases hA
    rfl
  have hγ := hgamma k A.sourceReserve A.targetReserve A.sourceKept A.targetKept
  dsimp only at hγ
  rw [hAe] at hγ
  have hδeq : originalOrientedStageFullCutError S w b R (G.cut k.val) scene =
      originalStageMainInputWindowPrefix K (G.cut k.val) scene := by
    simp only [K,originalOrientedStageFullCutError,(hcuts k hk).1,integral_zero_measure,integral_zero,sub_zero]
  have hγzero : A.gamma (G.cut k.val) = 0 := by
    rw [hγ,hδeq]
    have hnum : A.reservePrefix (G.cut k.val) + originalStageMainInputWindowPrefix K (G.cut k.val) scene = 0 := by
      linarith only [hprefix]
    rw [hnum,zero_div]
  refine ⟨?_,hγzero⟩
  have hν : ∀ z, originalOrientedOmittedCutDensity S w b R ell (G.cut k.val) A.scene z = 0 := by
    intro z
    rw [hA]
    exact ((hcuts k hk).2.2 b R ell).2 z
  have hInt : (∫ z, originalOrientedOmittedCutDensity S w b R ell (G.cut k.val) A.scene z ∂A.cubeMeasure) = 0 := by
    simp only [hν,integral_zero]
  have hdef : (A.portPrefix (G.cut k.val)+A.reservePrefix (G.cut k.val))/A.cubeVolume = 0 := by
    simpa only [OriginalOrientedStageResidualDensityData.gamma,hInt,sub_zero] using hγzero
  simpa only [zero_mul] using (div_eq_iff (A.cubeVolume_pos (by linarith : 0 < R)).ne').mp hdef

end OTSelector.Reconstruction
