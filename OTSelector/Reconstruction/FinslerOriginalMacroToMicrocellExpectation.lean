import OTSelector.Reconstruction.FinslerOriginalOptionalMacroGeometry
import OTSelector.Reconstruction.FinslerOriginalMacroGridCarriers
import OTSelector.Reconstruction.FinslerOriginalPhysicalMicrocellMean
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedActiveMacrocell

/-! The actual original macrocell maximum-cardinality model mean is bounded
by its literal original microcell means plus the legal parent repair. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical BoundedContinuousFunction
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


/-- All laws, null faces and microcell integrability are produced from the
same original population. The right side keeps the exact original microscopic
canonical values and the true parent-scale repair. -/
theorem PopulationLocalPressureCore.exists_original_macro_to_microcell_expectation_bound
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
    (hzero : ∀ j k, ¬(D.haar.continuous.coefficient i).clockClassAllowed Q j k → P₀ j k = 0) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let root := populationSeedRootLabelValue Seed a
    let basis := Module.finBasis ℝ Seed.covector.ker
    let q := Module.finrank ℝ Seed.covector.ker
    ∃ (R : ℕ) (B : ℝ), 0 < R ∧ 0 ≤ B ∧
    (∀ z ∈ C.roots, labelCubeCoordinates basis R (root z) ∈ unitCube q) ∧
    ∀ (G : Set (ℚ → M)) (hG : MeasurableSet G)
      (n N : ℕ) (hn : 0 < n), 4 < q → 0 < N → ∀ tilt : ℝ,
    let _inst : NeZero n := ⟨hn.ne'⟩
    ∀ (microcells : Finset (Fin q → ℤ)),
      microcells ⊆ Finset.univ.image (originalMacroMicroIndex (q := q) R n) →
      (∀ z ∈ L ∩ G, basis.equivFun (root z) ∈ ⋃ ν ∈ microcells,
        (BoxIntegral.unitPartition.box n ν : Set (Fin q → ℝ))) →
    let χ := (((lambda ⊗ₘ finiteCellPairKernel cell hcell K).map sameLabelPopulationPair).map (Prod.map b b))
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ πWhole := by rw [hsplit]; exact restrictOriginalRetainedResidual_le χ ξ a ha hG
    let Refined := Cst.refineSubplan ξG hξG
    let original := originalRetainedSeedClassCost a L (fun x ↦ root (a x)) basis.equivFunL.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
      ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic Q ref.val)
      (C.clockClassProbe Q ref.val ref.property f) tilt
    let micro := fun ν : Fin q → ℤ ↦ originalRetainedSeedClassCost a
      (L ∩ (basis.equivFunL ∘ root) ⁻¹' (BoxIntegral.unitPartition.box n ν : Set (Fin q → ℝ)))
      (fun x ↦ root (a x)) basis.equivFunL.toLinearMap
      (fun x ↦ classify (u x)) (fun x ↦ classify (u x)) (C.clockClassAllowed Q)
      ((N : ℝ) ^ (2 / (q : ℝ))) (C.clockClassKinetic Q ref.val)
      (C.clockClassProbe Q ref.val ref.property f) tilt
    Integrable original (Refined.markedLaw N) ∧
    (∀ ν ∈ microcells, Integrable (micro ν) (Refined.markedLaw N)) ∧
    (∫ sample, original sample ∂Refined.markedLaw N) / N ≤
      (∑ ν ∈ microcells, ∫ sample, micro ν sample ∂Refined.markedLaw N) / N +
      activeGridRepairError q (legalGridRepairConstant q (Q.count + 1) (Q.count * Q.count))
        B ‖f‖ tilt 1 ((N : ℝ) / ((2 * R * n : ℕ) : ℝ) ^ q) := by
  classical
  obtain ⟨R, B, hR, hB, hroot, hgrid⟩ := D.exists_original_optional_clockClass_grid_geometry
    hF hcomplete hu ha hinj i Q ref f P₀ hP₀ hmass hzero
  dsimp only
  refine ⟨R, B, hR, hB, hroot, ?_⟩
  intro G hG n N hn hq hN tilt
  obtain ⟨depth,hdepth,hdepth2⟩ := exists_gridLevel (2 * R * n) (by positivity)
  letI : NeZero n := ⟨hn.ne'⟩
  intro microcells hfit hcover
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let root := populationSeedRootLabelValue Seed a
  let basis := Module.finBasis ℝ Seed.covector.ker
  let q := Module.finrank ℝ Seed.covector.ker
  let spatial := originalRetainedSpatialLaw ((κ C.seedIndex).restrict (root '' (L ∩ G)))
    ((clockClassPairMeasure P₀) univ)
  let πclass := clockClassJointProbability P₀ hP₀ hmass
  let common := spatial.prod (πclass : Measure (Fin Q.count × Fin Q.count))
  let law := (Measure.pi (fun _ : Fin N ↦ common)).prod (Measure.pi (fun _ : Fin N ↦ common))
  let Sample := (Fin N → Option Seed.covector.ker × (Fin Q.count × Fin Q.count)) ×
    (Fin N → Option Seed.covector.ker × (Fin Q.count × Fin Q.count))
  let graph := fun sample : Sample ↦ pairedClassActiveGraph
    (fun o : Option Seed.covector.ker ↦ o.map (fun _ ↦ ())) (C.clockClassAllowed Q) sample.1 sample.2
  let score := fun (sample : Sample) (j k : Fin N) ↦ (N : ℝ) ^ (2 / (q : ℝ)) *
    C.clockClassKinetic Q ref.val (sample.1 j).2.1 (sample.2 k).2.2
      (basis.equivFun ((sample.2 k).1.elim 0 id - (sample.1 j).1.elim 0 id)) +
    tilt * C.clockClassProbe Q ref.val ref.property f (sample.1 j).2.1 (sample.2 k).2.2
  let z := fun w : Option Seed.covector.ker ↦ labelCubeCoordinates basis R (w.elim 0 id)
  let leafValue := fun sample : Sample ↦ ∑ leaf : Fin q → Fin (2 ^ depth + 1), PartialMatching.legalMaximumValue
    (PartialMatching.spatialLegalBlock (graph sample)
      (fun j ↦ gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth (z (sample.1 j).1))
      (fun k ↦ gridCellLabel q (2 * R * n) depth depth (by positivity) hdepth (z (sample.2 k).1)) leaf)
    (score sample)
  let microValue := fun (ν : Fin q → ℤ) (sample : Sample) ↦ PartialMatching.legalMaximumValue
    ((graph sample).filter (fun edge ↦
      basis.equivFun ((sample.1 edge.1).1.elim 0 id) ∈ BoxIntegral.unitPartition.box n ν ∧
      basis.equivFun ((sample.2 edge.2).1.elim 0 id) ∈ BoxIntegral.unitPartition.box n ν)) (score sample)
  have hmean := D.actual_original_paired_active_macrocell_mean_of_classifier hF hcomplete hu ha hinj
    i hL hsub hG Q classify hm hclass fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf
    hPf hresidual hrow hcol cell hcell hdisj K c hc hKc Qglobal hwhole hb hη₀inv hη₁inv
    hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst ref f N ((N : ℝ) ^ (2 / (q : ℝ))) tilt
  letI : IsProbabilityMeasure spatial := hmean.2.1
  have hparent := hgrid spatial hmean.2.2.1 (2 * R * n) depth N hq hN (by positivity)
    hdepth hdepth2 tilt
  have hmic ν := D.actual_original_physical_microcell_mean hF hcomplete hu ha hinj
    i hL hsub hG Q classify hm hclass fallbackS fallbackT P₀ hP₀ hmass Pf residual hmPf
    hPf hresidual hrow hcol cell hcell hdisj K c hc hKc Qglobal hwhole hb hη₀inv hη₁inv
    hlabel0 hlabel1 πWhole ξ hπWhole hsplit Cst ref f N ((N : ℝ) ^ (2 / (q : ℝ))) tilt n ν
  have hunit : ∀ w ∈ root '' (L ∩ G), labelCubeCoordinates basis R w ∈ unitCubeSet q := by
    rintro w ⟨z,hz,rfl⟩
    exact hroot z (hsub hz.1)
  have hcoverage : ∀ w ∈ root '' (L ∩ G), basis.equivFun w ∈ ⋃ ν ∈ microcells,
      (BoxIntegral.unitPartition.box n ν : Set (Fin q → ℝ)) := by
    rintro w ⟨z,hz,rfl⟩
    exact hcover z hz
  have himage := D.haar.measurable_cell_label_image hcomplete i (hL.inter hG)
    (inter_subset_left.trans hsub)
  have hae := ae_original_paired_macro_leaves_eq_microcells (κ C.seedIndex) basis hR hn hdepth
    himage hunit ((clockClassPairMeasure P₀) univ) hmean.2.1
    (πclass : Measure (Fin Q.count × Fin Q.count)) (C.clockClassAllowed Q) microcells hfit N
  dsimp only at hae
  have heq : leafValue =ᵐ[law] fun sample ↦ ∑ ν ∈ microcells, microValue ν sample := by
    filter_upwards [hae hcoverage] with sample hs
    exact hs (score sample)
  have hsumI : ∀ ν ∈ microcells, Integrable (microValue ν) law := fun ν _ ↦ (hmic ν).2.1
  have hsumEq := integral_finsetSum microcells hsumI
  have hleafEq := (integral_congr_ae heq).trans hsumEq
  refine ⟨hmean.2.2.2.1, fun ν _ ↦ (hmic ν).1, ?_⟩
  calc
    _ = _ := congrArg (fun value : ℝ ↦ value / N) hmean.2.2.2.2.2.2
    _ ≤ _ := hparent
    _ = _ := by
      rw [hleafEq]
      congr 2
      exact Finset.sum_congr rfl (fun ν _ ↦ (hmic ν).2.2.symm)

end OTSelector.Reconstruction
