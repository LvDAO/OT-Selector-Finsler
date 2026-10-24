import OTSelector.Reconstruction.FinslerRelativeLawOriginalPhysicalSubcellObservation
import OTSelector.Reconstruction.FinslerRelativeLawDeterministicLabelRestriction
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPrefixModelLaw
import OTSelector.Reconstruction.FinslerConcreteUpperActualClassObservation

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


/-- On every positive measurable subcell of an original retained Haar cell, the unchanged original
marked experiment produces the literal normalized Haar × fixed-class finite
prefix laws at their original binomial counts. The prescribed discarded label mass joins the global residual
on the same whole original coupling; no conditional-iid or retained-point-law oracle remains. -/
theorem PopulationLocalPressureCore.exists_actual_original_truncated_subcell_class_prefix_law
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
    let p : ℝ≥0 := (m univ * ENNReal.ofReal (∑ j, ∑ k, P₀ j k)).toNNReal
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    p ≤ 1 ∧ ∃ classify : ℝ → Fin Q.count, Measurable classify ∧
      (∀ j x, x ∈ Q.cell j → classify x = j) ∧ ∀ N : ℕ,
      (Refined.markedLaw N).map (Prod.map
        (fun x ↦ OTSelector.Probability.mapBlockData
          (fun z ↦ (R (a z.1), classify (u z.1)))
          (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) x))
        (fun y ↦ OTSelector.Probability.mapBlockData
          (fun z ↦ (R (a z.1), classify (u z.1)))
          (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) y))) =
        (OTSelector.Probability.blockDataLaw ((normalizedFiniteLaw m).prod α)
          (OTSelector.Probability.binomWeight N p)).prod
        (OTSelector.Probability.blockDataLaw ((normalizedFiniteLaw m).prod β)
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
  let atomic := clockClassPairMeasure P₀
  let τS := m.prod (atomic.map Prod.fst)
  let τT := m.prod (atomic.map Prod.snd)
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
    sameLabelPopulationPair).map (Prod.map b b))
  let hξ : ξ ≤ πWhole := by rw [hsplit]; exact Measure.le_add_left le_rfl
  let _instResidualFinite : IsFiniteMeasure ξ := isFiniteMeasure_of_le πWhole hξ
  let _instRetainedFinite : IsFiniteMeasure χ := isFiniteMeasure_of_le πWhole (by
    rw [hsplit]
    exact Measure.le_add_right le_rfl)
  let ξG := restrictOriginalRetainedResidual χ ξ a G
  let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
  have hcancel : πWhole - ξG = χ.restrict {p | a p.1 ∈ G} := by
    rw [hsplit]
    exact original_retained_label_restriction_complement χ ξ a ha hG
  have hχlabel := original_global_retained_shared_labels η₀ η₁ lambda a u ha hu.continuous.measurable
    b hb hη₀inv hη₁inv hlabel0 hlabel1 cell hcell K Qglobal hwhole
  obtain ⟨classify, hm, hclass, _, _, hrawS, hrawT⟩ :=
    D.exists_actual_retained_haar_class_observation hF hcomplete hu ha hinj i hL hsub Q
      fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf hPf hresidual hrow hcol
  have hR : Measurable R := measurable_populationSeedRootLabelValue (P C.seedIndex).seed
    hF hcomplete hu ha hinj
  let read := fun x ↦ (R (a x), classify (u x))
  have hread : Measurable read := (hR.comp ha).prodMk (hm.comp hu.continuous.measurable)
  have hs := original_global_retained_subcell_observation η₀ η₁ lambda a u ha hu.continuous.measurable
    b hb hη₀inv hη₁inv hlabel0 hlabel1 cell hcell hdisj K Qglobal hwhole R hR classify hm c hL hc false
  have ht := original_global_retained_subcell_observation η₀ η₁ lambda a u ha hu.continuous.measurable
    b hb hη₀inv hη₁inv hlabel0 hlabel1 cell hcell hdisj K Qglobal hwhole R hR classify hm c hL hc true
  rw [hKc] at hs ht
  have hsource : (((πWhole - ξG).map Prod.fst).restrict (a ⁻¹' L)).map read = τS := by
    rw [hcancel, original_retained_label_restriction_source χ a ha hG hLG]
    exact hs.trans hrawS
  have htarget : (((πWhole - ξG).map Prod.snd).restrict (a ⁻¹' L)).map read = τT := by
    rw [hcancel, original_retained_label_restriction_target χ a ha hχlabel hG hLG]
    exact ht.trans hrawT
  have hMassS : τS.real univ = m.real univ * (∑ j, ∑ k, P₀ j k) := by
    simp only [τS, measureReal_def, ← univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul,
      Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
    rw [univ_prod_univ]
    exact congrArg (fun z : ℝ ↦ m.real univ * z) (clockClassPairMeasure_real_univ P₀ hP₀)
  have hMassT : τT.real univ = m.real univ * (∑ j, ∑ k, P₀ j k) := by
    simp only [τT, measureReal_def, ← univ_prod_univ, Measure.prod_prod, ENNReal.toReal_mul,
      Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ]
    rw [univ_prod_univ]
    exact congrArg (fun z : ℝ ↦ m.real univ * z) (clockClassPairMeasure_real_univ P₀ hP₀)
  have hτS : 0 < τS.real univ := hMassS.symm ▸ mul_pos hHaar hmass
  have hτT : 0 < τT.real univ := hMassT.symm ▸ mul_pos hHaar hmass
  have hAtomic : atomic univ = ENNReal.ofReal (∑ j, ∑ k, P₀ j k) :=
    finiteClassPopulationCoupling_mass P₀ _ _ hP₀
  have hCountS : τS univ = m univ * ENNReal.ofReal (∑ j, ∑ k, P₀ j k) := by
    rw [show τS = m.prod (atomic.map Prod.fst) from rfl, ← univ_prod_univ, Measure.prod_prod,
      Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ, hAtomic]
  have hCountT : τT univ = m univ * ENNReal.ofReal (∑ j, ∑ k, P₀ j k) := by
    rw [show τT = m.prod (atomic.map Prod.snd) from rfl, ← univ_prod_univ, Measure.prod_prod,
      Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ, hAtomic]
  have hRetainedMass : ((πWhole - ξG).map Prod.fst) (a ⁻¹' L) = τS univ := by
    have h := congrArg (fun ρ ↦ ρ univ) hsource
    simpa only [Measure.map_apply hread MeasurableSet.univ, preimage_univ,
      Measure.restrict_apply_univ] using h
  have hdom : (πWhole - ξG).map Prod.fst ≤ η₀ :=
    (Measure.map_mono Measure.sub_le measurable_fst).trans_eq hπWhole.1
  have hcountLe : τS univ ≤ 1 := by
    rw [← hRetainedMass]
    exact (hdom (a ⁻¹' L)).trans prob_le_one
  have hpLe : (m univ * ENNReal.ofReal (∑ j, ∑ k, P₀ j k)).toNNReal ≤ 1 := by
    have h := ENNReal.toNNReal_mono ENNReal.one_ne_top hcountLe
    simpa only [hCountS, ENNReal.toNNReal_one] using h
  have hnormS : normalizedFiniteLaw (atomic.map Prod.fst) =
      (normalizedClockClassPairMeasure P₀).map Prod.fst := by
    have hm0 : (atomic.map Prod.fst).real univ = atomic.real univ := by
      simp only [measureReal_def, Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ]
    simp only [normalizedClockClassPairMeasure, normalizedFiniteLaw, hm0, Measure.map_smul, atomic]
  have hnormT : normalizedFiniteLaw (atomic.map Prod.snd) =
      (normalizedClockClassPairMeasure P₀).map Prod.snd := by
    have hm0 : (atomic.map Prod.snd).real univ = atomic.real univ := by
      simp only [measureReal_def, Measure.map_apply measurable_snd MeasurableSet.univ, preimage_univ]
    simp only [normalizedClockClassPairMeasure, normalizedFiniteLaw, hm0, Measure.map_smul, atomic]
  have hpointS : normalizedFiniteLaw τS = (normalizedFiniteLaw m).prod
      ((normalizedClockClassPairMeasure P₀).map Prod.fst) :=
    (normalizedFiniteLaw_prod_eq m (atomic.map Prod.fst)).trans (congrArg ((normalizedFiniteLaw m).prod) hnormS)
  have hpointT : normalizedFiniteLaw τT = (normalizedFiniteLaw m).prod
      ((normalizedClockClassPairMeasure P₀).map Prod.snd) :=
    (normalizedFiniteLaw_prod_eq m (atomic.map Prod.snd)).trans (congrArg ((normalizedFiniteLaw m).prod) hnormT)
  dsimp only
  refine ⟨hpLe, classify, hm, hclass, ?_⟩
  intro N
  have h := Cst.original_retained_prefix_normalized_model_law hπWhole ξG hξG N
    (ha hL) (ha hL) read read hread hread τS τT hτS hτT hsource htarget
  dsimp only at h
  simpa only [read, hpointS, hpointT, hCountS, hCountT] using h

end OTSelector.Reconstruction
