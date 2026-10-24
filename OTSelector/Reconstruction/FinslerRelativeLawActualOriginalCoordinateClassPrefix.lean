import OTSelector.Reconstruction.FinslerRelativeLawActualOriginalClassPrefix

/-! Exact finite class/Haar prefix laws on the actual original marked sample.
The physical inverse, original weighted clock-bin split, class normalization,
and binomial count mass are all discharged from the original population data. -/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

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


/-- Every finite binomial count law gives a sigma-finite finite-cloud law. -/
theorem sfinite_original_binomial_blockDataLaw
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (N : ℕ) (p : ℝ≥0) :
    SFinite (OTSelector.Probability.blockDataLaw ν (OTSelector.Probability.binomWeight N p)) := by
  unfold OTSelector.Probability.blockDataLaw
  have hfinite (m : ℕ) : IsFiniteMeasure
      (OTSelector.Probability.binomWeight N p m •
        (Measure.pi (fun _ : Fin m ↦ ν)).map
          (fun y ↦ (⟨m, y⟩ : OTSelector.Probability.BlockData X))) := by
    apply Measure.smul_finite
    unfold OTSelector.Probability.binomWeight
    finiteness
  exact MeasureTheory.sfinite_sum_of_countable _

/-- Changing the original seed coordinate applies the same measurable map to
every retained observation. The actual original Haar/class binomial law, count
and enumeration are preserved, including affine pressure coordinates. -/
theorem PopulationLocalPressureCore.exists_actual_original_retained_coordinate_class_prefix_law
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {W : Type*} [MeasurableSpace W]
    (J : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker → W)
    (hJ : Measurable J)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
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
    (c : Cells) (hc : cell c = L)
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
    {T : Type*} [Fintype T] {q : ℕ} {cost : M → M → ℝ}
    (Cst : PopulationTypedCostData πWhole η₀ η₁ T q cost)
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    (hHaar : 0 < ((κ (D.haar.continuous.coefficient i).seedIndex).restrict
      (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a '' L)).real univ) :
    let C := D.haar.continuous.coefficient i
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let m := (κ C.seedIndex).restrict (R '' L)
    let _instFinite : IsFiniteMeasure m := D.isFiniteMeasure_original_haar_cell hF hcomplete hu ha hinj i hL hsub
    let _instHaar : IsProbabilityMeasure (normalizedFiniteLaw m) := normalizedFiniteLaw_probability m hHaar
    let _instClass : IsProbabilityMeasure (normalizedClockClassPairMeasure P₀) :=
      normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
    let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
    let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
    let _instα : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instβ : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    let _instSpatial : IsProbabilityMeasure ((normalizedFiniteLaw m).map J) :=
      Measure.isProbabilityMeasure_map hJ.aemeasurable
    let p : ℝ≥0 := (m univ * ENNReal.ofReal (∑ j, ∑ k, P₀ j k)).toNNReal
    let hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
    let Refined := Cst.refineSubplan ξ hξ
    p ≤ 1 ∧ ∃ classify : ℝ → Fin Q.count, Measurable classify ∧
      (∀ j x, x ∈ Q.cell j → classify x = j) ∧ ∀ N : ℕ,
      (Refined.markedLaw N).map (Prod.map
        (fun x ↦ OTSelector.Probability.mapBlockData
          (fun z ↦ (J (R (a z.1)), classify (u z.1)))
          (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) x))
        (fun y ↦ OTSelector.Probability.mapBlockData
          (fun z ↦ (J (R (a z.1)), classify (u z.1)))
          (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) y))) =
        (OTSelector.Probability.blockDataLaw (((normalizedFiniteLaw m).map J).prod α)
          (OTSelector.Probability.binomWeight N p)).prod
        (OTSelector.Probability.blockDataLaw (((normalizedFiniteLaw m).map J).prod β)
          (OTSelector.Probability.binomWeight N p)) := by
  classical
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  let m := (κ C.seedIndex).restrict (R '' L)
  let _instCellFinite : IsFiniteMeasure m := D.isFiniteMeasure_original_haar_cell hF hcomplete hu ha hinj i hL hsub
  let _instHaar : IsProbabilityMeasure (normalizedFiniteLaw m) := normalizedFiniteLaw_probability m hHaar
  let _instClass : IsProbabilityMeasure (normalizedClockClassPairMeasure P₀) :=
    normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
  let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
  let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
  let _instα : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  let _instβ : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  let _instSpatial : IsProbabilityMeasure ((normalizedFiniteLaw m).map J) :=
    Measure.isProbabilityMeasure_map hJ.aemeasurable
  obtain ⟨hp, classify, hm, hclass, hprefix⟩ :=
    D.exists_actual_original_retained_class_prefix_law hF hcomplete hu ha hinj i hL hsub Q
      fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf hPf hresidual hrow hcol
      cell hcell hdisj K c hc hKc Qglobal hwhole hb hη₀inv hη₁inv hlabel0 hlabel1
      πWhole ξ hπWhole hsplit Cst hHaar
  refine ⟨hp, classify, hm, hclass, ?_⟩
  intro N
  let pointMap := Prod.map J (id : Fin Q.count → Fin Q.count)
  have hpointMap : Measurable pointMap := hJ.prodMap measurable_id
  let dataMap := OTSelector.Probability.mapBlockData pointMap
  have hdataMap : Measurable dataMap := OTSelector.Probability.measurable_mapBlockData hpointMap
  have hR : Measurable R := measurable_populationSeedRootLabelValue (P C.seedIndex).seed
    hF hcomplete hu ha hinj
  have hread : Measurable (fun z : M × Option (Bool × T) ↦ (R (a z.1), classify (u z.1))) :=
    ((hR.comp ha).comp measurable_fst).prodMk ((hm.comp hu.continuous.measurable).comp measurable_fst)
  let obs := fun x : Fin N → M × Option (Bool × T) ↦ OTSelector.Probability.mapBlockData
    (fun z ↦ (R (a z.1), classify (u z.1)))
    (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) x)
  have hobs : Measurable obs :=
    (OTSelector.Probability.measurable_mapBlockData hread).comp
      (measurable_finiteOriginalRestrictedData (measurableSet_retainedMarkedCellEvent (ha hL)))
  have hs : ((normalizedFiniteLaw m).prod α).map pointMap = ((normalizedFiniteLaw m).map J).prod α := by
    rw [← Measure.map_prod_map _ _ hJ measurable_id, Measure.map_id]
  have ht : ((normalizedFiniteLaw m).prod β).map pointMap = ((normalizedFiniteLaw m).map J).prod β := by
    rw [← Measure.map_prod_map _ _ hJ measurable_id, Measure.map_id]
  let _instBlockS : SFinite (OTSelector.Probability.blockDataLaw ((normalizedFiniteLaw m).prod α)
      (OTSelector.Probability.binomWeight N (m univ * ENNReal.ofReal (∑ j, ∑ k, P₀ j k)).toNNReal)) :=
    sfinite_original_binomial_blockDataLaw _ _ _
  let _instBlockT : SFinite (OTSelector.Probability.blockDataLaw ((normalizedFiniteLaw m).prod β)
      (OTSelector.Probability.binomWeight N (m univ * ENNReal.ofReal (∑ j, ∑ k, P₀ j k)).toNNReal)) :=
    sfinite_original_binomial_blockDataLaw _ _ _
  have h := congrArg (fun ρ ↦ ρ.map (Prod.map dataMap dataMap)) (hprefix N)
  rw [Measure.map_map (hdataMap.prodMap hdataMap) (hobs.prodMap hobs),
    ← Measure.map_prod_map _ _ hdataMap hdataMap,
    OTSelector.Probability.blockDataLaw_mapPoints _ _ hpointMap hs,
    OTSelector.Probability.blockDataLaw_mapPoints _ _ hpointMap ht] at h
  change ((Cst.refineSubplan ξ _).markedLaw N).map
    (Prod.map (dataMap ∘ obs) (dataMap ∘ obs)) = _ at h
  simpa only [Function.comp_def, obs, dataMap, pointMap,
    OTSelector.Probability.mapBlockData, Prod.map_apply, id_eq] using h

end OTSelector.Reconstruction
