import OTSelector.Reconstruction.FinslerOriginalMicrocellCoverExpectation
import OTSelector.Reconstruction.FinslerOriginalFixedClassifierGridPressure
import OTSelector.Reconstruction.FinslerOriginalPressureVolumeUpper
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalMacroGridScale

/-! An actual original measurable cell produces its own deterministic fitting
microboxes and the legal macro-to-micro expectation bound on those boxes. -/
open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}


/-- The original finite-cloud cell model has its actual full-cell pressure
upper bound after the sample limit at each fixed microscopic side. One original
classifier, population experiment and parent grid are retained throughout.
Both the signed missing-volume error and legal parent repair remain explicit. -/
theorem PopulationLocalPressureCore.exists_original_cell_mean_pressure_upper
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count)
    [(κ (D.haar.continuous.coefficient i).seedIndex).IsAddHaarMeasure]
    {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (classify : ℝ → Fin Q.count) (hm : Measurable classify)
    (hclass : ∀ j x, x ∈ Q.cell j → classify x = j)
    (fallbackS fallbackT : Fin Q.count → ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ) (hP₀ : ∀ j k, 0 ≤ P₀ j k)
    (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (Pf residual : (ℚ → M) → Fin Q.count → Fin Q.count → ℝ)
    (hmPf : ∀ j k, Measurable (fun z ↦ Pf z j k))
    (hPf : ∀ z ∈ L, ∀ j k, Pf z j k = P₀ j k / D.rootIntensity i z)
    (hresidual : ∀ᵐ z ∂lambda.restrict L, ∀ j k, 0 ≤ residual z j k)
    (hrow : ∀ᵐ z ∂lambda.restrict L, ∀ j, ∑ k, (Pf z j k + residual z j k) =
      (condDistrib u a η₀ z).real (Q.cell j))
    (hcol : ∀ᵐ z ∂lambda.restrict L, ∀ k, ∑ j, (Pf z j k + residual z j k) =
      (condDistrib u a η₁ z).real (Q.cell k))
    {Cells : Type*} [Fintype Cells]
    (cell : Cells → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (K : Cells → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (K c)]
    (c : Cells) (hc : L ⊆ cell c)
    (hKc : K c = finiteClassPopulationKernel Pf
      (fun j ↦ normalizedActualBinKernel (condDistrib u a η₀) (Q.cell j) (Q.measurable_cell j) (fallbackS j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a η₁) (Q.cell k) (Q.measurable_cell k) (fallbackT k)))
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell K z + Qglobal z) (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    (hb : Measurable b)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x, u x) = x) (hη₁inv : ∀ᵐ y ∂η₁, b (a y, u y) = y)
    (hlabel0 : η₀.map a = lambda) (hlabel1 : η₁.map a = lambda)
    (πWhole ξ : Measure (M × M)) [IsFiniteMeasure πWhole]
    (hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
    (hsplit : πWhole = (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b)) + ξ)
    {T : Type*} [Fintype T] {qAtlas : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData πWhole η₀ η₁ T qAtlas cost)
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    (ref : (D.haar.continuous.coefficient i).roots) (f : M × M →ᵇ ℝ)
    (hzero : ∀ j k, ¬(D.haar.continuous.coefficient i).clockClassAllowed Q j k → P₀ j k = 0)
    (hq : 4 < Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let root := populationSeedRootLabelValue Seed a
    let basis := Module.finBasis ℝ Seed.covector.ker
    let coord := atlasSeedCoord Seed basis.equivFunL a
    let q := Module.finrank ℝ Seed.covector.ker
    let _instClass := normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
    let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
    let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
    let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
    ∃ (R : ℕ) (B : ℝ) (cHaar : ℝ≥0), 0 < R ∧ 0 ≤ B ∧ 0 < cHaar ∧
      (κ C.seedIndex).map basis.equivFunL =
        (cHaar : ℝ≥0∞) • (volume : Measure (Fin q → ℝ)) ∧
    ∀ (scale : ℝ) (hscale : 0 < scale) (ε : ℝ), 0 < ε →
    ∃ indices : ℕ → Finset (Fin q → ℤ),
      (∀ N, lambda (L \ coord ⁻¹' (⋃ ν ∈ indices N,
        (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set (Fin q → ℝ)))) <
          ENNReal.ofReal ε) ∧
      (∀ N, volume ((coord '' L) \ (⋃ ν ∈ indices N,
        (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set (Fin q → ℝ)))) <
          ENNReal.ofReal ε) ∧
      Tendsto (fun N ↦ volume ((⋃ ν ∈ indices N,
        (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set (Fin q → ℝ))) \ (coord '' L)))
        atTop (𝓝 0) ∧
    ∀ (G : ℕ → Set (ℚ → M)) (hG : ∀ N, MeasurableSet (G N)),
      (∀ N, L ∩ G N = L ∩ coord ⁻¹' (⋃ ν ∈ indices N,
        (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set (Fin q → ℝ)))) →
    ∀ tilt : ℝ,
      let density := cHaar * (clockClassPairMeasure P₀ univ).toNNReal
      let pressure := finiteClassLegalPressure q (C.clockClassAllowed Q) α β
        (density * ⟨scale ^ q, pow_nonneg hscale.le q⟩)
        (C.densityClockClassKinetic Q ref.val density) (C.clockClassProbe Q ref.val ref.property f) tilt / scale ^ q
      let ξG := fun N ↦ restrictOriginalRetainedResidual χ ξ a (G N)
      let hξG : ∀ N, ξG N ≤ πWhole := fun N ↦ by
        rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha (hG N)
      let Refined := fun N ↦ Cst.refineSubplan (ξG N) (hξG N)
      let original := fun (N : ℕ) ↦ originalRetainedSeedClassCost (T := T) (N := N) a L (fun x ↦ root (a x)) basis.equivFunL.toLinearMap
        (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
        ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic Q ref.val)
        (C.clockClassProbe Q ref.val ref.property f) tilt
      (∀ᶠ N in atTop, Integrable (original N) ((Refined N).markedLaw N)) ∧
      ∀ ζ : ℝ, 0 < ζ → ∀ᶠ N in atTop,
        (∫ sample, original N sample ∂(Refined N).markedLaw N) / N ≤
          volume.real (coord '' L) * pressure + ε * |pressure| +
          activeGridRepairError q (legalGridRepairConstant q (Q.count + 1) (Q.count * Q.count))
            B ‖f‖ tilt 1 ((scale / (2 * (R : ℝ))) ^ q) + ζ := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let root := populationSeedRootLabelValue Seed a
  let basis := Module.finBasis ℝ Seed.covector.ker
  let coord := atlasSeedCoord Seed basis.equivFunL a
  let q := Module.finrank ℝ Seed.covector.ker
  letI := normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
  let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
  let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
  letI : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  letI : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
    sameLabelPopulationPair).map (Prod.map b b))
  obtain ⟨R,B,hR,hB,hcover⟩ := D.exists_original_microcell_cover_expectation_bound
    hF hcomplete hu ha hinj i hL hsub Q classify hm hclass fallbackS fallbackT P₀ hP₀ hmass
    Pf residual hmPf hPf hresidual hrow hcol cell hcell hdisj K c hc hKc Qglobal hwhole
    hb hη₀inv hη₁inv hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst ref f hzero hq
  obtain ⟨cHaar,hcHaar,hmap,hpressure⟩ := D.exists_actual_original_fixed_classifier_grid_pressure_error
    hF hcomplete hu ha hinj i hL hsub Q classify hm hclass fallbackS fallbackT P₀ hP₀ hmass
    Pf residual hmPf hPf hresidual hrow hcol cell hcell hdisj K c hc hKc Qglobal hwhole
    hb hη₀inv hη₁inv hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst ref.val ref.property f (by omega)
  have hq0 : 0 < q := by dsimp only [q,Seed,C]; omega
  refine ⟨R,B,cHaar,hR,hB,hcHaar,hmap,?_⟩
  intro scale hscale ε hε
  obtain ⟨indices,hdisjoint,hloss,hmissing,hadded,hbound⟩ :=
    hcover (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) (positiveMicroscopicGridOrder q scale)
      (tendsto_positiveMicroscopicGridOrder hq0 hscale)
  refine ⟨indices,hloss,hmissing,hadded,?_⟩
  intro G hG htrace tilt
  let density := cHaar * (clockClassPairMeasure P₀ univ).toNNReal
  let pressure := finiteClassLegalPressure q (C.clockClassAllowed Q) α β
    (density * ⟨scale ^ q, pow_nonneg hscale.le q⟩)
    (C.densityClockClassKinetic Q ref.val density) (C.clockClassProbe Q ref.val ref.property f) tilt / scale ^ q
  let ξG := fun N ↦ restrictOriginalRetainedResidual χ ξ a (G N)
  have hξG : ∀ N, ξG N ≤ πWhole := fun N ↦ by
    rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha (hG N)
  let Refined := fun N ↦ Cst.refineSubplan (ξG N) (hξG N)
  let original := fun (N : ℕ) ↦ originalRetainedSeedClassCost (T := T) (N := N) a L (fun x ↦ root (a x)) basis.equivFunL.toLinearMap
    (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
    ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic Q ref.val)
    (C.clockClassProbe Q ref.val ref.property f) tilt
  let micro := fun (N : ℕ) (ν : Fin q → ℤ) ↦ originalRetainedSeedClassCost (T := T) (N := N) a
    (L ∩ coord ⁻¹' (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set _))
    (fun x ↦ root (a x)) basis.equivFunL.toLinearMap
    (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
    ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic Q ref.val)
    (C.clockClassProbe Q ref.val ref.property f) tilt
  let microValue := fun N sample ↦ ∑ ν : {ν // ν ∈ indices N}, micro N ν.val sample
  let U := fun N ↦ ⋃ ν ∈ indices N,
    (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set (Fin q → ℝ))
  have hlocal : ∀ N, 0 < N → Integrable (original N) ((Refined N).markedLaw N) ∧
      (∀ ν ∈ indices N, Integrable (micro N ν) ((Refined N).markedLaw N)) ∧
      (∫ sample, original N sample ∂(Refined N).markedLaw N) / N ≤
        (∑ ν ∈ indices N, ∫ sample, micro N ν sample ∂(Refined N).markedLaw N) / N +
        activeGridRepairError q (legalGridRepairConstant q (Q.count + 1) (Q.count * Q.count))
          B ‖f‖ tilt 1 ((N : ℝ) / ((2 * R * positiveMicroscopicGridOrder q scale N : ℕ) : ℝ) ^ q) := by
    intro N hN
    exact hbound N hN (G N) (hG N) tilt (htrace N)
  have hcoverG : ∀ N, ∀ ν ∈ indices N, ∀ z ∈ L,
      coord z ∈ (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder q scale N) ν : Set _) → z ∈ G N := by
    intro N ν hν z hz hzbox
    have hm : z ∈ L ∩ G N := by
      rw [htrace N]
      exact ⟨hz, mem_iUnion.mpr ⟨ν, mem_iUnion.mpr ⟨hν,hzbox⟩⟩⟩
    exact hm.2
  have hpress := hpressure scale hscale indices G hG hcoverG hadded
  have herror : Tendsto (fun N ↦
      (∫ sample, microValue N sample ∂(Refined N).markedLaw N) / N - volume.real (U N) * pressure)
      atTop (𝓝 0) := by
    exact (hpress.2 |tilt| (abs_nonneg _)).tendsto_at ⟨neg_abs_le tilt,le_abs_self tilt⟩
  have hpos : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_gt_atTop 0
  refine ⟨hpos.mono (fun N hN ↦ (hlocal N hN).1),?_⟩
  refine eventually_mean_le_original_volume_pressure volume
    (s := coord '' L) ?_ ?_ U ?_ ?_
    (mean := fun N ↦ (∫ sample, original N sample ∂(Refined N).markedLaw N) / N)
    (micro := fun N ↦ (∫ sample, microValue N sample ∂(Refined N).markedLaw N) / N)
    (repair := fun N ↦ activeGridRepairError q
      (legalGridRepairConstant q (Q.count + 1) (Q.count * Q.count)) B ‖f‖ tilt 1
      ((N : ℝ) / ((2 * R * positiveMicroscopicGridOrder q scale N : ℕ) : ℝ) ^ q))
    (pressure := pressure) (missing := ε)
    (repairLimit := activeGridRepairError q
      (legalGridRepairConstant q (Q.count + 1) (Q.count * Q.count)) B ‖f‖ tilt 1
      ((scale / (2 * (R : ℝ))) ^ q)) ?_ herror ?_ hadded ?_
  · have hR := D.haar.measurable_cell_label_image hcomplete i hL hsub
    have h := basis.equivFunL.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hR
    change MeasurableSet (basis.equivFunL '' (root '' L)) at h
    change MeasurableSet ((fun z ↦ basis.equivFunL (root z)) '' L)
    simpa only [image_image] using h
  · have hsubI : L ⊆ (D.haar.intensity i).roots := by rwa [D.haar.intensity_roots]
    have hcompact : IsCompact (basis.equivFunL '' (root '' (D.haar.intensity i).roots)) :=
      (D.haar.intensity i).compact_labels.image basis.equivFunL.continuous
    apply (hcompact.isBounded.subset ?_).measure_lt_top.ne
    rintro _ ⟨z,hz,rfl⟩
    exact mem_image_of_mem basis.equivFunL (mem_image_of_mem root (hsubI hz))
  · intro N
    exact MeasurableSet.biUnion (indices N).countable_toSet (fun ν _ ↦
      (BoxIntegral.unitPartition.box (positiveMicroscopicGridOrder q scale N) ν).measurableSet_coe)
  · intro N
    apply ne_top_of_le_ne_top _ (measure_biUnion_finset_le _ _)
    apply ENNReal.sum_ne_top.mpr
    intro ν _
    rw [BoxIntegral.unitPartition.volume_box]
    exact ENNReal.div_ne_top ENNReal.one_ne_top (pow_ne_zero _ (by
      exact_mod_cast (NeZero.ne (positiveMicroscopicGridOrder q scale N))))
  · filter_upwards [hpos] with N hN
    have hh := (hlocal N hN).2.2
    have hsum : (∑ ν ∈ indices N, ∫ sample, micro N ν sample ∂(Refined N).markedLaw N) =
        ∫ sample, microValue N sample ∂(Refined N).markedLaw N := by
      rw [← Finset.sum_coe_sort]
      exact (integral_finsetSum Finset.univ (fun ν _ ↦ (hlocal N hN).2.1 ν.val ν.property)).symm
    rwa [hsum] at hh
  · intro N
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmissing N).le
    simpa only [measureReal_def, ENNReal.toReal_ofReal hε.le] using hreal
  · exact tendsto_original_macro_grid_repair_fixed_side hq0 hR
      (legalGridRepairConstant q (Q.count + 1) (Q.count * Q.count)) B ‖f‖ tilt hscale

end OTSelector.Reconstruction
