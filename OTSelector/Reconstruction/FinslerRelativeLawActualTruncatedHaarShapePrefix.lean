import OTSelector.Reconstruction.FinslerRelativeLawActualTruncatedClassObservation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalMarkedHaarShapePrefix
import OTSelector.Reconstruction.FinslerRelativeLawDeterministicLabelRestriction
import OTSelector.Reconstruction.FinslerConcreteUpperActualClassObservation

/-! Exact finite class/Haar prefix laws on the actual original marked sample.
The physical inverse, original weighted clock-bin split, class normalization,
and binomial count mass are all discharged from the original population data. -/

open Set Function MeasureTheory ProbabilityTheory BoxIntegral Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
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


/-- The actual original physical Haar/class marginal laws produce exact paired
binomial shape prefixes on the same deterministic residual experiment. Null
subcells are included, without a normalized-Haar positivity premise. -/
theorem PopulationLocalPressureCore.exists_actual_original_truncated_haar_shape_prefix_law
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {G : Set (ℚ → M)} (hG : MeasurableSet G) (hLG : L ⊆ G)
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
    [(κ (D.haar.continuous.coefficient i).seedIndex).IsAddHaarMeasure]
    (e : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker ≃L[ℝ]
      (Fin (Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ))
    (n : ℕ) [NeZero n]
    (index : Fin (Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℤ)
    (hcellbox : ∀ z ∈ L, e (populationSeedRootLabelValue
      (P (D.haar.continuous.coefficient i).seedIndex).seed a z) ∈ (unitPartition.box n index : Set _))
    (hboxProbability : ((κ (D.haar.continuous.coefficient i).seedIndex)
      (e ⁻¹' (unitPartition.box n index : Set _)) * (clockClassPairMeasure P₀) univ).toNNReal ≤ 1) :
    let C := D.haar.continuous.coefficient i
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let normalize := affineHaarCubeCoord e (fun l ↦ (index l : ℝ) / n) (n : ℝ≥0)⁻¹
    let _instClass := normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
    let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
    let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
    let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    let p : unitInterval := ⟨((κ C.seedIndex) (e ⁻¹' (unitPartition.box n index : Set _)) *
      (clockClassPairMeasure P₀) univ).toNNReal, NNReal.coe_nonneg _, (by exact_mod_cast hboxProbability)⟩
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    ∃ classify : ℝ → Fin Q.count, Measurable classify ∧
      (∀ j x, x ∈ Q.cell j → classify x = j) ∧ ∀ N : ℕ,
      (Refined.markedLaw N).map (Prod.map
        (fun x ↦ mapBlockData (fun z ↦ (normalize (R (a z.1)), classify (u z.1)))
          (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) x))
        (fun y ↦ mapBlockData (fun z ↦ (normalize (R (a z.1)), classify (u z.1)))
          (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) y))) =
        (binomialShapeBlockLaw q α N p (originalMicrocellShape e n index (R '' L))).prod
          (binomialShapeBlockLaw q β N p (originalMicrocellShape e n index (R '' L))) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  let μ := κ C.seedIndex
  let atomic := clockClassPairMeasure P₀
  let τS := atomic.map Prod.fst
  let τT := atomic.map Prod.snd
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
    sameLabelPopulationPair).map (Prod.map b b))
  let ξG := restrictOriginalRetainedResidual χ ξ a G
  let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
  obtain ⟨classify, hm, hclass, hsource, htarget⟩ :=
    D.exists_actual_original_truncated_subcell_class_observation_laws hF hcomplete hu ha hinj i hL hsub
      hG hLG Q fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf hPf hresidual hrow hcol
      cell hcell hdisj K c hc hKc Qglobal hwhole hb hη₀inv hη₁inv hlabel0 hlabel1
      πWhole ξ hπWhole hsplit
  have hτS : 0 < τS.real univ := by
    have heq : τS.real univ = atomic.real univ := by
      simp only [τS, measureReal_def, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
    rw [heq, show atomic.real univ = ∑ j, ∑ k, P₀ j k from clockClassPairMeasure_real_univ P₀ hP₀]
    exact hmass
  have hτT : 0 < τT.real univ := by
    have heq : τT.real univ = atomic.real univ := by
      simp only [τT, measureReal_def, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ]
    rw [heq, show atomic.real univ = ∑ j, ∑ k, P₀ j k from clockClassPairMeasure_real_univ P₀ hP₀]
    exact hmass
  have htotal : τT univ = τS univ := by
    simp only [τT, τS, Measure.map_apply measurable_snd MeasurableSet.univ,
      Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
  have hs : MeasurableSet (R '' L) := D.haar.measurable_cell_label_image hcomplete i hL hsub
  have hsubbox : R '' L ⊆ e ⁻¹' (unitPartition.box n index : Set (Fin q → ℝ)) := by
    rintro _ ⟨z, hz, rfl⟩
    exact hcellbox z hz
  have hset : (R '' L) ∩ e ⁻¹' (unitPartition.box n index : Set (Fin q → ℝ)) = R '' L :=
    inter_eq_left.mpr hsubbox
  have hR : Measurable R := measurable_populationSeedRootLabelValue (P C.seedIndex).seed hF hcomplete hu ha hinj
  let read := fun x ↦ (R (a x), classify (u x))
  have hread : Measurable read := (hR.comp ha).prodMk (hm.comp hu.continuous.measurable)
  have hnormS : normalizedFiniteLaw τS = (normalizedClockClassPairMeasure P₀).map Prod.fst := by
    have hm0 : τS.real univ = atomic.real univ := by
      simp only [τS, measureReal_def, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
    simp only [normalizedClockClassPairMeasure, normalizedFiniteLaw, hm0, τS, Measure.map_smul, atomic]
  have hnormT : normalizedFiniteLaw τT = (normalizedClockClassPairMeasure P₀).map Prod.snd := by
    have hm0 : τT.real univ = atomic.real univ := by
      simp only [τT, measureReal_def, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ]
    simp only [normalizedClockClassPairMeasure, normalizedFiniteLaw, hm0, τT, Measure.map_smul, atomic]
  refine ⟨classify, hm, hclass, ?_⟩
  intro N
  have h := Cst.original_retained_haar_shape_prefix_law hπWhole ξG hξG N (ha hL) (ha hL)
    read read hread hread μ e n index (R '' L) hs τS τT hτS hτT htotal
    (by rw [hset]; exact hsource) (by rw [hset]; exact htarget)
    (by simpa only [τS, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] using hboxProbability)
  dsimp only at h ⊢
  simpa only [hnormS, hnormT, read, Function.comp_def, Prod.map_apply, id_eq,
    τS, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] using h

end OTSelector.Reconstruction
