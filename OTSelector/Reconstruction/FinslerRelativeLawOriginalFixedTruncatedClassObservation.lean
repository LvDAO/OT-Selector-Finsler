import OTSelector.Reconstruction.FinslerRelativeLawOriginalFixedClassObservation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPhysicalSubcellObservation
import OTSelector.Reconstruction.FinslerRelativeLawDeterministicLabelRestriction
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
set_option linter.unusedSectionVars false

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


/-- The same actual original retained experiment has its literal unnormalized
Haar/class marginal laws on every measurable subcell, including null cells.
The deterministic discarded labels join the same global residual. -/
theorem PopulationLocalPressureCore.actual_original_truncated_class_laws_of_classifier
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
    (classify : ℝ → Fin Q.count) (hm : Measurable classify)
    (hclass : ∀ j x, x ∈ Q.cell j → classify x = j)
    (fallbackS fallbackT : Fin Q.count → ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ) (hP₀ : ∀ j k, 0 ≤ P₀ j k)
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
    (_hπWhole : Vlasov.IsCoupling πWhole η₀ η₁)
    (hsplit : πWhole = (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b)) + ξ) :
    let C := D.haar.continuous.coefficient i
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let m := (κ C.seedIndex).restrict (R '' L)
    let atomic := clockClassPairMeasure P₀
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    ((((πWhole - ξG).map Prod.fst).restrict (a ⁻¹' L)).map
        (fun x ↦ (R (a x), classify (u x))) = m.prod (atomic.map Prod.fst)) ∧
      ((((πWhole - ξG).map Prod.snd).restrict (a ⁻¹' L)).map
        (fun x ↦ (R (a x), classify (u x))) = m.prod (atomic.map Prod.snd)) := by
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
  obtain ⟨_, _, hrawS, hrawT⟩ :=
    D.actual_retained_haar_class_observation_of_classifier hF hcomplete hu ha hinj i hL hsub Q
      classify hm hclass fallbackS fallbackT P₀ hP₀ Pf residual hmPf hPf hresidual hrow hcol
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
  exact ⟨hsource, htarget⟩

end OTSelector.Reconstruction
