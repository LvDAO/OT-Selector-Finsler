import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentModelExpectedUpper
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellwiseResidualEnergy
import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentCoarseExpectedUpper
import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentClockClassEndpoints
import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedCellCover
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelObservable
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalExpectedUpper
import OTSelector.Reconstruction.FinslerRelativeLawOriginalTraceFineExperiment
import OTSelector.Reconstruction.FinslerRelativeLawOriginalTraceCompactCarriers
import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineCanonicalIntegral
import OTSelector.Reconstruction.FinslerConcreteUpperRetainedCompactTruncation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalClockClassMembership
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalEndpointAllowed

/-! Literal original conditional class splits discharge all retained endpoint
properties and compatibility needed by the canonical expected upper bound. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- A flattened dependent family of actual original coefficient cells shares
ONE calibrated coupling, original atlas, compact choice and residual repair.
Its upper mean uses the unchanged old-RN canonical observable in all cells. -/
theorem PopulationLocalPressureCore.exists_original_dependent_cellwise_cutoff_expected_upper
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (hlabel0 : μ.map a = lambda) (hlabel1 : ν.map a = lambda)
    {C T : Type*} [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (hI : MeasurableSet I) {globalGap : ℝ}
    (coreIndex : C → Fin D.haar.continuous.count)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (Q : C → FiniteScalarBins I globalGap) (U : C → Set (ℚ → M))
    {A B : Set M} (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (houter : ∀ c j k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j k →
      ∀ s ∈ (Q c).cell j, ∀ t ∈ (Q c).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
          (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
          (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1)
    (hregion : ∀ c,
      ∀ z ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ z' ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
        (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1,
      ∀ t ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
        (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1,
      s < t → D.corePoint (coreIndex c) (z, s) ∈ A → D.corePoint (coreIndex c) (z', t) ∈ B →
        (s, t) ∈ (D.haar.continuous.coefficient (coreIndex c)).window.region)
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (hπ : Vlasov.IsCoupling (χ + ξ) μ ν) {q : ℕ}
    (Cst : PopulationTypedCostData (χ + ξ) μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
    (hcal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂χ + ξ, u p.2 - u p.1 = dist p.1 p.2)
    {forwardGap : ℝ} (hgap : 0 < forwardGap)
    (hforward : ∀ t x y, Cst.sourceGood t x → Cst.targetGood t y →
      forwardGap ≤ u y - u x)
    (cell : C → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c)
    (classify : ∀ c, ℝ → Fin (Q c).count)
    (hmclass : ∀ c, Measurable (classify c))
    (hclass : ∀ c j s, s ∈ (Q c).cell j → classify c s = j)
    (Kcell : C → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (Kcell c)]
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell Kcell z + Qglobal z)
        (condDistrib u a μ z) (condDistrib u a ν z))
    (hχ : χ = (((lambda ⊗ₘ finiteCellPairKernel cell hcell Kcell).map
      sameLabelPopulationPair).map (Prod.map b b)))
    (fallbackS fallbackT : ∀ c, Fin (Q c).count → ℝ)
    (P₀ : ∀ c, Fin (Q c).count → Fin (Q c).count → ℝ)
    (hP₀ : ∀ c j k, 0 ≤ P₀ c j k)
    (density : C → (ℚ → M) → ℝ)
    (residual Pf : ∀ c, (ℚ → M) → Fin (Q c).count → Fin (Q c).count → ℝ)
    (hmPf : ∀ c j k, Measurable (fun z ↦ Pf c z j k))
    (hPf : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j k, Pf c z j k = P₀ c j k / density c z)
    (hdensity : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), 0 < density c z)
    (hresidual : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j k, 0 ≤ residual c z j k)
    (hrow : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j,
      ∑ k, (P₀ c j k / density c z + residual c z j k) =
        (condDistrib u a μ z).real ((Q c).cell j))
    (hcol : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ k,
      ∑ j, (P₀ c j k / density c z + residual c z j k) =
        (condDistrib u a ν z).real ((Q c).cell k))
    (hKcell : ∀ c, Kcell c = finiteClassPopulationKernel (Pf c)
      (fun j ↦ normalizedActualBinKernel (condDistrib u a μ) ((Q c).cell j)
        ((Q c).measurable_cell j) (fallbackS c j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a ν) ((Q c).cell k)
        ((Q c).measurable_cell k) (fallbackT c k)))
    (hzero : ∀ c j k, ¬(D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed
      (Q c) j k → P₀ c j k = 0)
    (f : M × M →ᵇ ℝ) {ρ probeError : ℝ} (hρ : 0 ≤ ρ) (hprobe : 0 ≤ probeError)
    (hgeometry : ∀ c,
      ∀ z ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ z' ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ j k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j k →
      ∀ s ∈ (Q c).cell j, ∀ t ∈ (Q c).cell k,
      D.corePoint (coreIndex c) (z,s) ∈ A → D.corePoint (coreIndex c) (z',t) ∈ B →
      let C₀ := D.haar.continuous.coefficient (coreIndex c)
      let S := (P C₀.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      (s,t) ∈ C₀.window.region ∧
      |populationSeedPairDeficit S (s,t) (R z,R z') -
        C₀.clockClassKinetic (Q c) (reference c).val j k
          ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z))| ≤
        ρ * C₀.clockClassKinetic (Q c) (reference c).val j k
          ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z)) ∧
      |f (D.corePoint (coreIndex c) (z,s),D.corePoint (coreIndex c) (z',t)) -
        C₀.clockClassProbe (Q c) (reference c).val (reference c).property f j k| ≤ 2 * probeError)
    (hq : 4 < q) {θ : ℝ} (hθ : 0 < θ) :
    let cost := fun x y ↦ (F.lengthEDist x y).toReal - u y + u x
    ∃ (K : T → C → Set (DyadicUnitCube q)) (depth : ℕ)
      (hK : ∀ t c, IsCompact (K t c)),
      0 < depth ∧
      (∀ k ≥ depth, ∀ t c c', ∀ x ∈ K t c, ∀ y ∈ K t c',
        dyadicCubeCell k x = dyadicCubeCell k y → c = c') ∧
      ∀ (cutoff : C → Set (ℚ → M)) (hcutoff : ∀ c, MeasurableSet (cutoff c)),
      let G := ⋃ c, cell c ∩ cutoff c
      let hG := MeasurableSet.iUnion fun c ↦ (hcell c).inter (hcutoff c)
      let ηG := restrictOriginalRetainedResidual χ ξ a G
      let hηG := restrictOriginalRetainedResidual_le χ ξ a ha hG
      let coord := fun t (p : M × M) ↦ Cst.sourceCoordinate t p.1
      let goodMacro := Cst.types.rnCellCompactGoodComponent ηG hηG (fun p ↦ a p.1) coord cell K
      let badMacro := Cst.types.rnCellCompactBadComponent ηG hηG (fun p ↦ a p.1) coord cell K
      ∃ hsplitMacro : ∀ t, goodMacro t + ∑ c, badMacro c t =
          (Cst.types.rnSubplanTypes ηG hηG).component (false, t),
      (∑ p : C × T, badMacro p.1 p.2 Set.univ).toReal < θ ∧
      restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ G) = ηG ∧
      let trace := fun c ↦ cell c ∩ G
      let htrace := fun c ↦ (hcell c).inter hG
      let htraceDisj : Pairwise (Disjoint on trace) :=
        fun _ _ hne ↦ (hdisj hne).mono inter_subset_left inter_subset_left
      let ηTrace := restrictOriginalRetainedResidual χ ξ a (⋃ c, trace c)
      let hηTrace := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion htrace)
      let goodTrace := Cst.types.rnCellCompactGoodComponent ηTrace hηTrace (fun p ↦ a p.1) coord trace K
      let badTrace := Cst.types.rnCellCompactBadComponent ηTrace hηTrace (fun p ↦ a p.1) coord trace K
      let hsplitTrace := Cst.types.rn_truncated_compact_split χ ξ a ha trace htrace coord
        (fun t ↦ (Cst.measurable_sourceCoordinate t).comp measurable_fst) htraceDisj K
        (fun t c ↦ (hK t c).measurableSet)
      Cst.types.rnCellRefinedTypes ηTrace hηTrace goodTrace badTrace hsplitTrace =
        Cst.types.rnCellRefinedTypes ηG hηG goodMacro badMacro hsplitMacro ∧
      ∀ n : ℕ, 0 < n →
    let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, trace c)
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion htrace)
    let β := (ξ univ).toReal + ∑ c, (μ.map a).real (cell c \ cutoff c)
    let Refined := Cst.refineSubplan η hη
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    ∀ tilt : ℝ,
    let actualCost := fun (sample : (Fin n → M × Option (Bool × T)) ×
        (Fin n → M × Option (Bool × T))) j k ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      cost (sample.1 j).1 (sample.2 k).1 + tilt * f ((sample.1 j).1, (sample.2 k).1)
    let model := fun c (sample : (Fin n → M × Option (Bool × T)) ×
        (Fin n → M × Option (Bool × T))) j k ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      D.originalClockClassKinetic (coreIndex c) (Q c) (reference c) (classify c) (sample.1 j).1 (sample.2 k).1 +
      tilt * D.originalClockClassProbe (coreIndex c) (Q c) (reference c) (classify c) f (sample.1 j).1 (sample.2 k).1
    let canonical := fun sample c ↦ originalRetainedCellOptimizer a trace
      (originalSubplanPhysicalGraph (fun c ↦ D.originalClockClassAllowed (coreIndex c) (Q c) (classify c)))
      model c sample
    let retainedCost := fun sample ↦ ∑ c, (canonical sample c).cost (actualCost sample)
    let modelCost := fun sample ↦ ∑ c, (canonical sample c).cost (model c sample)
    let value := fun sample : (Fin n → M) × (Fin n → M) ↦ perturbedAssignmentValue
      (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i) (sample.2 j) +
        tilt * f (sample.1 i, sample.2 j)) 0 0
    Integrable value P₀ ∧ Integrable retainedCost (Refined.markedLaw n) ∧
    Integrable modelCost (Refined.markedLaw n) ∧
    (∫ sample, value sample ∂P₀) / (n : ℝ) ≤
      (1+ρ) * ((∫ sample, modelCost sample ∂Refined.markedLaw n) / (n : ℝ)) +
      (|tilt| * (2 * probeError) + ρ * (|tilt| * ‖f‖)) +
      (Cst.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * β ^ (1 - 2 / (q : ℝ)) +
      Cst.globalBound * Real.sqrt (2 * Fintype.card T) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt β +
      2 * |tilt| * ‖f‖ * β) +
      ((n : ℝ) ^ (2 / (q : ℝ)) * Cst.globalBound + |tilt| * ‖f‖) *
        (((Fintype.card T : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ depth + 1) ^ q) +
          (Fintype.card (C × T) : ℝ) *
            Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q)) / (n : ℝ) +
          Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T))) / (n : ℝ)) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  have hum : Measurable u := hu.continuous.measurable
  have hcover : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c := by
    rw [hχ]
    exact original_physical_retained_cell_cover μ ν lambda a u ha hum b hb
      hμinv hνinv hlabel0 hlabel1 cell hcell Kcell Qglobal hwhole
  obtain ⟨K,depth,hK,hd,hsep,hall⟩ :=
    D.exists_original_dependent_clockClass_model_expected_upper γ originalGap
      hF hcomplete hu ha hinj horder hb hμreg hνreg hμinv hνinv hlabel0 hlabel1
      hI coreIndex reference Q U hμA hνB houter hregion χ ξ hπ Cst hcal hgap hforward
      cell hcell hdisj hsub classify hmclass hclass Kcell Qglobal hwhole hχ
      fallbackS fallbackT P₀ hP₀ density residual Pf hmPf hPf hdensity hresidual hrow hcol hKcell hzero
      f hρ hprobe hgeometry hq hθ
  dsimp only
  refine ⟨K,depth,hK,hd,hsep,?_⟩
  intro cutoff hcutoff
  let G := ⋃ c, cell c ∩ cutoff c
  have hG : MeasurableSet G := MeasurableSet.iUnion fun c ↦ (hcell c).inter (hcutoff c)
  obtain ⟨hsplit,hbad,hηeq,hReq,hallN⟩ := hall G hG
  refine ⟨hsplit,hbad,hηeq,hReq,?_⟩
  intro n hn tilt
  obtain ⟨hVI,hPI,hMI,hupper⟩ := hallN n hn tilt
  refine ⟨hVI,hPI,hMI,hupper.trans ?_⟩
  have hbudget := Cst.original_cellwise_cutoff_repair_budget_le χ ξ hπ a ha
    cell cutoff hcell hcutoff hdisj hcover hq n tilt ‖f‖ (norm_nonneg f)
  rw [← hηeq] at hbudget
  exact add_le_add (add_le_add (le_refl _) hbudget) (le_refl _)

end OTSelector.Reconstruction
