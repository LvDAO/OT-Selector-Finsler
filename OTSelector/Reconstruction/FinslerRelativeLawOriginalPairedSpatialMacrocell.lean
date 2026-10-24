import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedSpatialMean
import OTSelector.Reconstruction.FinslerRelativeLawOriginalTruncatedCanonicalTrace
import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentModelTrace

/-! A fixed original macrocell reads exactly the deterministic retained trace,
then the same optional paired-class iid law. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical BoundedContinuousFunction
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


theorem PopulationLocalPressureCore.actual_original_paired_spatial_macrocell_mean_of_classifier
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {G : Set (ℚ → M)} (hG : MeasurableSet G)
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
    (N : ℕ) (scale tilt : ℝ)
    {Leaf : Type*} [Fintype Leaf] [DecidableEq Leaf] [MeasurableSpace Leaf]
    [MeasurableSingletonClass Leaf]
    (label : (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker → Leaf)
    (hlabel : Measurable label) (leaf : Leaf) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let e := (Module.finBasis ℝ Seed.covector.ker).equivFunL
    let R := populationSeedRootLabelValue Seed a
    let m := (κ C.seedIndex).restrict (R '' (L ∩ G))
    let atomic := clockClassPairMeasure P₀
    let spatial := originalRetainedSpatialLaw m (atomic univ)
    let common := spatial.prod (clockClassJointProbability P₀ hP₀ hmass : Measure (Fin Q.count × Fin Q.count))
    let law := (Measure.pi (fun _ : Fin N ↦ common)).prod (Measure.pi (fun _ : Fin N ↦ common))
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    let original := originalRetainedSeedClassCost a (L ∩ (label ∘ R) ⁻¹' {leaf}) (fun x ↦ R (a x)) e.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
      scale (C.clockClassKinetic Q ref.val) (C.clockClassProbe Q ref.val ref.property f) tilt
    let latent := fun sample ↦ PartialMatching.legalMaximumValue
      (PartialMatching.spatialLegalBlock
        (pairedClassActiveGraph (fun o : Option Seed.covector.ker ↦ o.map (fun _ ↦ ()))
          (C.clockClassAllowed Q) sample.1 sample.2)
        (fun j ↦ label ((sample.1 j).1.elim 0 id))
        (fun k ↦ label ((sample.2 k).1.elim 0 id)) leaf)
      (fun j k ↦ scale * C.clockClassKinetic Q ref.val (sample.1 j).2.1 (sample.2 k).2.2
        (e ((sample.2 k).1.elim 0 id - (sample.1 j).1.elim 0 id)) +
        tilt * C.clockClassProbe Q ref.val ref.property f (sample.1 j).2.1 (sample.2 k).2.2)
    m univ * atomic univ ≤ 1 ∧ IsProbabilityMeasure spatial ∧
      (∀ᵐ o ∂spatial, ∀ w, o = some w → w ∈ R '' C.roots) ∧
      Integrable original (Refined.markedLaw N) ∧ Integrable latent law ∧
      (Refined.markedLaw N).map original = law.map latent ∧
      (∫ sample, original sample ∂Refined.markedLaw N) = ∫ sample, latent sample ∂law := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let e := (Module.finBasis ℝ Seed.covector.ker).equivFunL
  let R := populationSeedRootLabelValue Seed a
  let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
  let ξG := restrictOriginalRetainedResidual χ ξ a G
  let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
  let Refined := Cst.refineSubplan ξG hξG
  have hmean := D.actual_original_paired_spatial_mean_of_classifier hF hcomplete hu ha hinj
    i (hL.inter hG) (inter_subset_left.trans hsub) hG inter_subset_right
    Q classify hm hclass fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf
    (fun z hz j k ↦ hPf z hz.1 j k)
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left hresidual)
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left hrow)
    (ae_restrict_of_ae_restrict_of_subset inter_subset_left hcol)
    cell hcell hdisj K c (inter_subset_left.trans hc) hKc Qglobal hwhole
    hb hη₀inv hη₁inv hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst ref f N scale tilt label hlabel leaf
  have hshared : ∀ᵐ p ∂χ, a p.1 = a p.2 :=
    original_global_retained_shared_labels η₀ η₁ lambda a u ha hu.continuous.measurable b hb
      hη₀inv hη₁inv hlabel0 hlabel1 cell hcell K Qglobal hwhole
  letI : IsFiniteMeasure χ := isFiniteMeasure_of_le πWhole (by
    rw [hsplit]
    exact Measure.le_add_right le_rfl)
  letI : IsFiniteMeasure ξ := isFiniteMeasure_of_le πWhole (by
    rw [hsplit]
    exact Measure.le_add_left le_rfl)
  have hlabels : ∀ᵐ sample ∂Refined.markedLaw N,
      (∀ j, subplanRetentionFlag (sample.1 j).2 = false → a (sample.1 j).1 ∈ G) ∧
      (∀ k, subplanRetentionFlag (sample.2 k).2 = false → a (sample.2 k).1 ∈ G) := by
    have heq : πWhole = χ + ξ := hsplit
    cases heq
    exact Cst.original_truncated_retained_endpoint_labels χ ξ a ha hG hshared N
  let extra := fun (_ : Unit) (sample : (Fin N → M × Option (Bool × T)) ×
      (Fin N → M × Option (Bool × T))) ↦ Finset.univ.filter (fun jk : Fin N × Fin N ↦
    C.clockClassAllowed Q (classify (u (sample.1 jk.1).1)) (classify (u (sample.2 jk.2).1)))
  let score := fun (_ : Unit) (sample : (Fin N → M × Option (Bool × T)) ×
      (Fin N → M × Option (Bool × T))) j k ↦ scale * C.clockClassKinetic Q ref.val
      (classify (u (sample.1 j).1)) (classify (u (sample.2 k).1))
      (e (R (a (sample.2 k).1) - R (a (sample.1 j).1))) +
      tilt * C.clockClassProbe Q ref.val ref.property f
        (classify (u (sample.1 j).1)) (classify (u (sample.2 k).1))
  have htrace : originalRetainedSeedClassCost a ((L ∩ G) ∩ (label ∘ R) ⁻¹' {leaf}) (fun x ↦ R (a x)) e.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
      scale (C.clockClassKinetic Q ref.val) (C.clockClassProbe Q ref.val ref.property f) tilt =ᵐ[
        Refined.markedLaw N]
      originalRetainedSeedClassCost a (L ∩ (label ∘ R) ⁻¹' {leaf}) (fun x ↦ R (a x)) e.toLinearMap
        (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
        scale (C.clockClassKinetic Q ref.val) (C.clockClassProbe Q ref.val ref.property f) tilt := by
    filter_upwards [hlabels] with sample hs
    have hset : ((L ∩ G) ∩ (label ∘ R) ⁻¹' {leaf}) =
        (L ∩ (label ∘ R) ⁻¹' {leaf}) ∩ G := by ext z; simp only [mem_inter_iff]; tauto
    rw [hset]
    change (originalRetainedCellOptimizer a (fun _ : Unit ↦ (L ∩ (label ∘ R) ⁻¹' {leaf}) ∩ G)
      extra score () sample).cost (score () sample) =
      (originalRetainedCellOptimizer a (fun _ : Unit ↦ L ∩ (label ∘ R) ⁻¹' {leaf})
        extra score () sample).cost (score () sample)
    unfold originalRetainedCellOptimizer
    rw [originalRetainedCellGraph_trace_eq a (fun _ : Unit ↦ L ∩ (label ∘ R) ⁻¹' {leaf})
      G extra sample hs.1 hs.2 ()]
  refine ⟨hmean.1,hmean.2.1,hmean.2.2.1,hmean.2.2.2.1.congr htrace,
    hmean.2.2.2.2.1,?_,?_⟩
  · exact (Measure.map_congr htrace).symm.trans hmean.2.2.2.2.2.1
  · exact (integral_congr_ae htrace).symm.trans hmean.2.2.2.2.2.2

end OTSelector.Reconstruction
