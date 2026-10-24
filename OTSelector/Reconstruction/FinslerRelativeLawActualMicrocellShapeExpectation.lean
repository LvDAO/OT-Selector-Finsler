import OTSelector.Reconstruction.FinslerRelativeLawActualTruncatedShapeExpectation
import OTSelector.Reconstruction.FinslerRelativeLawActualTruncatedHaarShapePrefix
import OTSelector.Reconstruction.FinslerRelativeLawOriginalSeedShapeExpectation
import OTSelector.Reconstruction.FinslerRelativeLawActualTruncatedClassObservation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalMarkedHaarShapePrefix
import OTSelector.Reconstruction.FinslerRelativeLawDeterministicLabelRestriction
import OTSelector.Reconstruction.FinslerConcreteUpperActualClassObservation

/-! Exact finite class/Haar prefix laws on the actual original marked sample.
The physical inverse, original weighted clock-bin split, class normalization,
and binomial count mass are all discharged from the original population data. -/

open Set Function MeasureTheory ProbabilityTheory BoxIntegral Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical unitInterval BoundedContinuousFunction
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


/-- The true seed score on an original retained cell's canonical optimizer. -/
def originalRetainedSeedClassCost
    {X Z V A B T : Type*} [AddCommGroup V] [Module ℝ V] {q N : ℕ}
    (a : X → Z) (L : Set Z) (root : X → V) (e : V →ₗ[ℝ] (Fin q → ℝ))
    (markS : X → A) (markT : X → B) (mask : A → B → Prop)
    (scale : ℝ) (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (tilt : ℝ)
    (sample : (Fin N → X × Option (Bool × T)) × (Fin N → X × Option (Bool × T))) : ℝ :=
  let extra := fun (_ : Unit) (cloud : (Fin N → X × Option (Bool × T)) ×
      (Fin N → X × Option (Bool × T))) ↦ Finset.univ.filter (fun jk : Fin N × Fin N ↦
    mask (markS (cloud.1 jk.1).1) (markT (cloud.2 jk.2).1))
  let score := fun (_ : Unit) (cloud : (Fin N → X × Option (Bool × T)) ×
      (Fin N → X × Option (Bool × T))) j k ↦
    scale * kin (markS (cloud.1 j).1) (markT (cloud.2 k).1)
      (e (root (cloud.2 k).1 - root (cloud.1 j).1)) +
      tilt * probe (markS (cloud.1 j).1) (markT (cloud.2 k).1)
  (originalRetainedCellOptimizer a (fun _ : Unit ↦ L) extra score () sample).cost (score () sample)

/-- All literal original microscopic subcells use the same global residual
experiment. Their canonical cost sum is integrable with the exact finite
binomial shape mean, including null cells and arbitrary strict mask codes. -/
theorem PopulationLocalPressureCore.exists_actual_original_microcell_canonical_shape_means
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
    (z₀ : ℚ → M) (hz₀ : z₀ ∈ (D.haar.continuous.coefficient i).roots)
    (f : M × M →ᵇ ℝ)
    (hq : 0 < Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (n : ℕ) [NeZero n]
    (indices : Finset (Fin (Module.finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℤ))
    (hcover : ∀ ν ∈ indices, ∀ z ∈ L,
      (Module.finBasis ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFunL
        (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a z) ∈
          (unitPartition.box n ν : Set _) → z ∈ G)
    (hboxProbability : ∀ ν ∈ indices, ((κ (D.haar.continuous.coefficient i).seedIndex)
      ((Module.finBasis ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFunL ⁻¹'
        (unitPartition.box n ν : Set _)) * (clockClassPairMeasure P₀) univ).toNNReal ≤ 1) :
    let C := D.haar.continuous.coefficient i
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let _instClass := normalizedClockClassPairMeasure_probability P₀ hP₀ hmass
    let α := (normalizedClockClassPairMeasure P₀).map Prod.fst
    let β := (normalizedClockClassPairMeasure P₀).map Prod.snd
    let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
    let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map
      sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    let microcell := fun ν : {ν // ν ∈ indices} ↦
      L ∩ (fun z ↦ e (R z)) ⁻¹' (unitPartition.box n ν.val : Set _)
    let p := fun ν : {ν // ν ∈ indices} ↦ (⟨((κ C.seedIndex)
      (e ⁻¹' (unitPartition.box n ν.val : Set _)) * (clockClassPairMeasure P₀) univ).toNNReal,
      NNReal.coe_nonneg _, (by exact_mod_cast hboxProbability ν.val ν.property)⟩ : unitInterval)
    ∃ classify : {ν // ν ∈ indices} → ℝ → Fin Q.count,
      (∀ ν, Measurable (classify ν) ∧ ∀ j x, x ∈ Q.cell j → classify ν x = j) ∧
      ∀ (source target : Fin Q.count → ℝ),
      (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) →
      ∀ (N : ℕ) (tilt : ℝ),
      let value := fun sample ↦ ∑ ν : {ν // ν ∈ indices},
        originalRetainedSeedClassCost a (microcell ν) (fun x ↦ R (a x)) e.toLinearMap
          (fun x ↦ classify ν (u x)) (fun x ↦ classify ν (u x)) (C.clockClassAllowed Q)
          ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt sample
      Integrable value (Refined.markedLaw N) ∧
        (∫ sample, value sample ∂Refined.markedLaw N) =
          ∑ ν : {ν // ν ∈ indices}, affineClassBinomialShapeExpectation source target α β N (p ν)
            (n : ℝ≥0)⁻¹ (fun l ↦ (ν.val l : ℝ) / n) (originalMicrocellShape e n ν.val (R '' L))
            (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  let e := (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  let microcell := fun ν : {ν // ν ∈ indices} ↦
    L ∩ (fun z ↦ e (R z)) ⁻¹' (unitPartition.box n ν.val : Set _)
  have hR : Measurable R := measurable_populationSeedRootLabelValue (P C.seedIndex).seed hF hcomplete hu ha hinj
  have hmicro (ν : {ν // ν ∈ indices}) : MeasurableSet (microcell ν) :=
    hL.inter ((unitPartition.box n ν.val).measurableSet_coe.preimage (e.continuous.measurable.comp hR))
  have hsubmicro (ν : {ν // ν ∈ indices}) : microcell ν ⊆ L := inter_subset_left
  have hLG (ν : {ν // ν ∈ indices}) : microcell ν ⊆ G :=
    fun z hz ↦ hcover ν.val ν.property z hz.1 hz.2
  have hshape (ν : {ν // ν ∈ indices}) :
      originalMicrocellShape e n ν.val (R '' microcell ν) = originalMicrocellShape e n ν.val (R '' L) := by
    have himage : R '' microcell ν = (R '' L) ∩ e ⁻¹' (unitPartition.box n ν.val : Set _) := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨mem_image_of_mem R hz.1, hz.2⟩
      · rintro ⟨⟨z, hz, rfl⟩, hbox⟩
        exact ⟨z, ⟨hz, hbox⟩, rfl⟩
    rw [himage]
    exact originalMicrocellShape_inter_unitPartition (κ C.seedIndex) e n ν.val (R '' L)
  have hex := fun ν : {ν // ν ∈ indices} ↦
    D.exists_actual_original_truncated_canonical_shape_expectation hF hcomplete hu ha hinj i
      (hmicro ν) ((hsubmicro ν).trans hsub) hG (hLG ν) Q fallbackS fallbackT P₀ hP₀ hmass
      Pf residual hmPf (fun z hz ↦ hPf z hz.1)
      (ae_restrict_of_ae_restrict_of_subset (hsubmicro ν) hresidual)
      (ae_restrict_of_ae_restrict_of_subset (hsubmicro ν) hrow)
      (ae_restrict_of_ae_restrict_of_subset (hsubmicro ν) hcol)
      cell hcell hdisj K c ((hsubmicro ν).trans hc) hKc Qglobal hwhole
      hb hη₀inv hη₁inv hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst z₀ hz₀ f hq n ν.val
      (fun z hz ↦ hz.2) (hboxProbability ν.val ν.property)
  choose classify hm hclass hmean using hex
  refine ⟨classify, fun ν ↦ ⟨hm ν, hclass ν⟩, ?_⟩
  intro source target hcode N tilt
  have hmean' := fun ν : {ν // ν ∈ indices} ↦ hmean ν source target hcode N tilt
  dsimp only at hmean' ⊢
  constructor
  · exact integrable_finsetSum _ (fun ν _ ↦ (hmean' ν).1)
  · refine (integral_finsetSum _ (fun ν _ ↦ (hmean' ν).1)).trans ?_
    apply Finset.sum_congr rfl
    intro ν _
    exact (hmean' ν).2.trans (by rw [hshape ν])

end OTSelector.Reconstruction
