import OTSelector.Probability.SubcouplingTypedIID
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFixedTruncatedClassObservation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedActiveLaw

/-! The same original full retained cloud is an observed iid latent paired-class experiment. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
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


/-- The actual original clock split and fixed classifier give the exact
whole-cloud latent product observation law. Its activity rate is derived from
the original retained event and is at most one, including null cells. -/
theorem PopulationLocalPressureCore.actual_original_paired_active_observation_of_classifier
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
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))] :
    let C := D.haar.continuous.coefficient i
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let m := (κ C.seedIndex).restrict (R '' L)
    let atomic := clockClassPairMeasure P₀
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    let read := fun p : M × Option (Bool × T) ↦
      if p ∈ retainedMarkedCellEvent (a ⁻¹' L) then some (R (a p.1),classify (u p.1)) else none
    let spatial := originalRetainedSpatialLaw m (atomic univ)
    let common := spatial.prod (clockClassJointProbability P₀ hP₀ hmass : Measure (Fin Q.count × Fin Q.count))
    m univ * atomic univ ≤ 1 ∧ IsProbabilityMeasure spatial ∧
      (Refined.types.sourceMarkedLaw η₀).map read = common.map pairedActiveSourceRead ∧
      (Refined.types.targetMarkedLaw η₁).map read = common.map pairedActiveTargetRead ∧
      ∀ N : ℕ,
        (Refined.markedLaw N).map
          (Prod.map (fun xs ↦ fun j ↦ read (xs j)) (fun ys ↦ fun k ↦ read (ys k))) =
        ((Measure.pi (fun _ : Fin N ↦ common)).prod (Measure.pi (fun _ : Fin N ↦ common))).map
          (Prod.map (fun xs ↦ fun j ↦ pairedActiveSourceRead (xs j))
            (fun ys ↦ fun k ↦ pairedActiveTargetRead (ys k))) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  let m := (κ C.seedIndex).restrict (R '' L)
  letI : IsFiniteMeasure m := D.isFiniteMeasure_original_haar_cell hF hcomplete hu ha hinj i hL hsub
  let atomic := clockClassPairMeasure P₀
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
  let ξG := restrictOriginalRetainedResidual χ ξ a G
  let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
  let Refined := Cst.refineSubplan ξG hξG
  let E := retainedMarkedCellEvent (T := T) (a ⁻¹' L)
  have hE : MeasurableSet E := measurableSet_retainedMarkedCellEvent (ha hL)
  let physicalRead := fun x ↦ (R (a x),classify (u x))
  have hR : Measurable R := measurable_populationSeedRootLabelValue _ hF hcomplete hu ha hinj
  have hr : Measurable physicalRead := (hR.comp ha).prodMk (hm.comp hu.continuous.measurable)
  have hphysical := Cst.refineSubplan_retained_cell_observation_laws ξG hξG
    (ha hL) (ha hL) physicalRead physicalRead hr hr
  have hclasses := D.actual_original_truncated_class_laws_of_classifier hF hcomplete hu ha hinj
    i hL hsub hG hLG Q classify hm hclass fallbackS fallbackT P₀ hP₀ Pf residual hmPf
    hPf hresidual hrow hcol cell hcell hdisj K c hc hKc Qglobal hwhole hb hη₀inv hη₁inv
    hlabel0 hlabel1 πWhole ξ hπWhole hsplit
  have hread : Measurable (fun p : M × Option (Bool × T) ↦ physicalRead p.1) := hr.comp measurable_fst
  have hs : ((Refined.types.sourceMarkedLaw η₀).restrict E).map
      (fun p ↦ physicalRead p.1) = m.prod (atomic.map Prod.fst) := hphysical.1.trans hclasses.1
  have ht : ((Refined.types.targetMarkedLaw η₁).restrict E).map
      (fun p ↦ physicalRead p.1) = m.prod (atomic.map Prod.snd) := hphysical.2.trans hclasses.2
  have hprob := Refined.types.marked_probabilities hπWhole
  letI : IsProbabilityMeasure (Refined.types.sourceMarkedLaw η₀) := hprob.1
  letI : IsProbabilityMeasure (Refined.types.targetMarkedLaw η₁) := hprob.2.1
  have hmassS : (Refined.types.sourceMarkedLaw η₀) E = m univ * atomic univ := by
    have h := congrArg (fun ρ ↦ ρ univ) hs
    rw [Measure.map_apply hread MeasurableSet.univ,
      preimage_univ,Measure.restrict_apply_univ] at h
    exact h.trans (by
      rw [← univ_prod_univ,Measure.prod_prod,Measure.map_apply measurable_fst MeasurableSet.univ,preimage_univ])
  have hmassT : (Refined.types.targetMarkedLaw η₁) E = m univ * atomic univ := by
    have h := congrArg (fun ρ ↦ ρ univ) ht
    rw [Measure.map_apply hread MeasurableSet.univ,
      preimage_univ,Measure.restrict_apply_univ] at h
    exact h.trans (by
      rw [← univ_prod_univ,Measure.prod_prod,Measure.map_apply measurable_snd MeasurableSet.univ,preimage_univ])
  have hp : m univ * atomic univ ≤ 1 := hmassS ▸
    (prob_le_one (μ := Refined.types.sourceMarkedLaw η₀) (s := E))
  let read := fun p : M × Option (Bool × T) ↦ if p ∈ E then some (physicalRead p.1) else none
  have hreadGate : Measurable read :=
    (MeasureTheory.Option.measurable_some.comp hread).ite hE measurable_const
  let spatial := originalRetainedSpatialLaw m (atomic univ)
  let common := spatial.prod (clockClassJointProbability P₀ hP₀ hmass : Measure (Fin Q.count × Fin Q.count))
  have hsp : IsProbabilityMeasure spatial := originalRetainedSpatialLaw_probability m (atomic univ) hp
  letI : IsProbabilityMeasure spatial := hsp
  have hsMap : (Refined.types.sourceMarkedLaw η₀).map read = common.map pairedActiveSourceRead := by
    change (Refined.types.sourceMarkedLaw η₀).map
      (fun p ↦ if p ∈ E then some (physicalRead p.1) else none) = _
    rw [map_gated_original_observation _ hE (fun p ↦ physicalRead p.1) hread,hmassS,hs]
    exact (originalRetainedSpatialLaw_clockClass_source_map m P₀ hP₀ hmass).symm
  have htMap : (Refined.types.targetMarkedLaw η₁).map read = common.map pairedActiveTargetRead := by
    change (Refined.types.targetMarkedLaw η₁).map
      (fun p ↦ if p ∈ E then some (physicalRead p.1) else none) = _
    rw [map_gated_original_observation _ hE (fun p ↦ physicalRead p.1) hread,hmassT,ht]
    exact (originalRetainedSpatialLaw_clockClass_target_map m P₀ hP₀ hmass).symm
  refine ⟨hp,hsp,hsMap,htMap,?_⟩
  intro N
  have hobs : Measurable (fun xs : Fin N → M × Option (Bool × T) ↦ fun j ↦ read (xs j)) :=
    measurable_pi_lambda _ (fun j ↦ hreadGate.comp (measurable_pi_apply j))
  have hlatentS : Measurable (fun xs : Fin N → Option (P C.seedIndex).seed.covector.ker ×
      (Fin Q.count × Fin Q.count) ↦ fun j ↦ pairedActiveSourceRead (xs j)) :=
    measurable_pi_lambda _ (fun j ↦ measurable_pairedActiveSourceRead.comp (measurable_pi_apply j))
  have hlatentT : Measurable (fun xs : Fin N → Option (P C.seedIndex).seed.covector.ker ×
      (Fin Q.count × Fin Q.count) ↦ fun j ↦ pairedActiveTargetRead (xs j)) :=
    measurable_pi_lambda _ (fun j ↦ measurable_pairedActiveTargetRead.comp (measurable_pi_apply j))
  calc
    _ = (Measure.pi (fun _ : Fin N ↦ (Refined.types.sourceMarkedLaw η₀).map read)).prod
        (Measure.pi (fun _ : Fin N ↦ (Refined.types.targetMarkedLaw η₁).map read)) := by
      rw [show Refined.markedLaw N = (Measure.pi (fun _ : Fin N ↦ Refined.types.sourceMarkedLaw η₀)).prod
        (Measure.pi (fun _ : Fin N ↦ Refined.types.targetMarkedLaw η₁)) from rfl,
        ← Measure.map_prod_map _ _ hobs hobs,
        Measure.pi_map_pi (fun _ ↦ hreadGate.aemeasurable),Measure.pi_map_pi (fun _ ↦ hreadGate.aemeasurable)]
    _ = _ := by
      rw [← Measure.map_prod_map _ _ hlatentS hlatentT,
        Measure.pi_map_pi (fun _ ↦ measurable_pairedActiveSourceRead.aemeasurable),
        Measure.pi_map_pi (fun _ ↦ measurable_pairedActiveTargetRead.aemeasurable)]
      simp_rw [hsMap,htMap]
      rfl

end OTSelector.Reconstruction
