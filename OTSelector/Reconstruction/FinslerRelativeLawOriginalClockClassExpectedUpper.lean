import OTSelector.Reconstruction.FinslerRelativeLawOriginalClockClassEndpointProperties
import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedCellCover
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelObservable
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCanonicalExpectedUpper
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
set_option maxHeartbeats 4200000
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

/-- Literal original class kernels and one fixed compact approximation give the
original iid canonical upper expectation, with every law, support, finite selector,
measurability, count-defect and integrability condition discharged internally. -/
theorem PopulationLocalPressureCore.exists_original_clockClass_canonical_expected_upper
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
    (i : Fin D.haar.continuous.count) (hI : MeasurableSet I) {globalGap : ℝ}
    (Q : (D.haar.continuous.coefficient i).roots → FiniteScalarBins I globalGap)
    (U : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    {A B : Set M} (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (houter : ∀ ref j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q ref) j k →
      ∀ s ∈ (Q ref).cell j, ∀ t ∈ (Q ref).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1)
    (hregion : ∀ ref,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      ∀ t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      s < t → D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
        (s, t) ∈ (D.haar.continuous.coefficient i).window.region)
    {C T : Type*} [Fintype C] [Fintype T] [DecidableEq T]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (hπ : Vlasov.IsCoupling (χ + ξ) μ ν) {q : ℕ}
    (Cst : PopulationTypedCostData (χ + ξ) μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
    (hcal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂χ + ξ, u p.2 - u p.1 = dist p.1 p.2)
    {forwardGap : ℝ} (hgap : 0 < forwardGap)
    (hforward : ∀ t x y, Cst.sourceGood t x → Cst.targetGood t y →
      forwardGap ≤ u y - u x)
    (reference : C → (D.haar.continuous.coefficient i).roots)
    (cell : C → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsub : ∀ c, cell c ⊆ (D.haar.continuous.coefficient i).roots ∩ U (reference c))
    (classify : ∀ c, ℝ → Fin (Q (reference c)).count)
    (hmclass : ∀ c, Measurable (classify c))
    (hclass : ∀ c j s, s ∈ (Q (reference c)).cell j → classify c s = j)
    (Kcell : C → Kernel (ℚ → M) (ℝ × ℝ)) [∀ c, IsSFiniteKernel (Kcell c)]
    (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel Qglobal]
    (hwhole : ∀ᵐ z ∂lambda, Vlasov.IsCoupling
      (finiteCellPairKernel cell hcell Kcell z + Qglobal z)
        (condDistrib u a μ z) (condDistrib u a ν z))
    (hχ : χ = (((lambda ⊗ₘ finiteCellPairKernel cell hcell Kcell).map
      sameLabelPopulationPair).map (Prod.map b b)))
    (fallbackS fallbackT : ∀ c, Fin (Q (reference c)).count → ℝ)
    (P₀ : ∀ c, Fin (Q (reference c)).count → Fin (Q (reference c)).count → ℝ)
    (hP₀ : ∀ c j k, 0 ≤ P₀ c j k)
    (density : C → (ℚ → M) → ℝ)
    (residual Pf : ∀ c, (ℚ → M) → Fin (Q (reference c)).count → Fin (Q (reference c)).count → ℝ)
    (hmPf : ∀ c j k, Measurable (fun z ↦ Pf c z j k))
    (hPf : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j k, Pf c z j k = P₀ c j k / density c z)
    (hdensity : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), 0 < density c z)
    (hresidual : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j k, 0 ≤ residual c z j k)
    (hrow : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ j,
      ∑ k, (P₀ c j k / density c z + residual c z j k) =
        (condDistrib u a μ z).real ((Q (reference c)).cell j))
    (hcol : ∀ c, ∀ᵐ z ∂lambda.restrict (cell c), ∀ k,
      ∑ j, (P₀ c j k / density c z + residual c z j k) =
        (condDistrib u a ν z).real ((Q (reference c)).cell k))
    (hKcell : ∀ c, Kcell c = finiteClassPopulationKernel (Pf c)
      (fun j ↦ normalizedActualBinKernel (condDistrib u a μ) ((Q (reference c)).cell j)
        ((Q (reference c)).measurable_cell j) (fallbackS c j))
      (fun k ↦ normalizedActualBinKernel (condDistrib u a ν) ((Q (reference c)).cell k)
        ((Q (reference c)).measurable_cell k) (fallbackT c k)))
    (hzero : ∀ c j k, ¬(D.haar.continuous.coefficient i).clockClassAllowed
      (Q (reference c)) j k → P₀ c j k = 0)
    (f : M × M →ᵇ ℝ) (hq : 4 < q) {θ : ℝ} (hθ : 0 < θ) :
    let cost := fun x y ↦ (F.lengthEDist x y).toReal - u y + u x
    ∃ (K : T → C → Set (DyadicUnitCube q)) (depth : ℕ)
      (hK : ∀ t c, IsCompact (K t c)),
      0 < depth ∧
      (∀ k ≥ depth, ∀ t c c', ∀ x ∈ K t c, ∀ y ∈ K t c',
        dyadicCubeCell k x = dyadicCubeCell k y → c = c') ∧
      let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c)
      let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
      let σ := fun t ↦ (Cst.types.rnSubplanTypes η hη).component (false, t)
      (∑ p : C × T, compactColorBadComponent (σ p.2) (fun z ↦ a z.1)
        (fun z ↦ Cst.sourceCoordinate p.2 z.1) cell (K p.2) p.1 Set.univ).toReal < θ ∧
      ∀ n : ℕ, 0 < n →
    let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c)
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
    let coord := fun t (p : M × M) ↦ Cst.sourceCoordinate t p.1
    let good := Cst.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell K
    let bad := Cst.types.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell K
    let hsplit := Cst.types.rn_truncated_compact_split χ ξ a ha cell hcell coord
      (fun t ↦ (Cst.measurable_sourceCoordinate t).comp measurable_fst) hdisj K (fun t c ↦ (hK t c).measurableSet)
    let R := Cst.types.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    let P₀ := (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    ∀ tilt : ℝ,
    let actualCost := fun sample i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      cost (sample.1 i).1 (sample.2 j).1 + tilt * f ((sample.1 i).1, (sample.2 j).1)
    let canonical := fun (sample : (Fin n → M × Option (CellRefinedType C T)) ×
      (Fin n → M × Option (CellRefinedType C T))) c ↦ PartialMatching.firstLegalOptimalMatching
      (originalAmbientCellLegalGraph (fun i ↦ fineOriginalRetainedCellTag a cell (sample.1 i))
        (fun j ↦ fineOriginalRetainedCellTag a cell (sample.2 j))
        (originalFinePhysicalGraph (fun c ↦ D.originalClockClassAllowed i (Q (reference c)) (classify c)) sample) c)
      (fun sourceIndex targetIndex ↦ ((n : ℝ) ^ (2 / (q : ℝ)) *
        D.originalClockClassKinetic i (Q (reference c)) (reference c) (classify c) (sample.1 sourceIndex).1 (sample.2 targetIndex).1 +
        tilt * D.originalClockClassProbe i (Q (reference c)) (reference c) (classify c) f (sample.1 sourceIndex).1 (sample.2 targetIndex).1))
    let retainedCost := fun sample ↦ ∑ c, (canonical sample c).cost (actualCost sample)
    let value := fun sample : (Fin n → M) × (Fin n → M) ↦ perturbedAssignmentValue
      (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) * cost (sample.1 i) (sample.2 j) +
        tilt * f (sample.1 i, sample.2 j)) 0 0
    Integrable value P₀ ∧ Integrable retainedCost P ∧
    (∫ sample, value sample ∂P₀) / (n : ℝ) ≤
      (∫ sample, retainedCost sample ∂P) / (n : ℝ) +
      (Cst.quadraticConstant * dyadicMatchingConstant q *
        (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (η univ).toReal ^ (1 - 2 / (q : ℝ)) +
      Cst.globalBound * Real.sqrt (2 * Fintype.card T) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (η univ).toReal +
      2 * |tilt| * ‖f‖ * (η univ).toReal) +
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
  have hsreg : ∀ᵐ p ∂χ + ξ, p.1 ∈ F.potentialRegularDomain u :=
    ae_of_ae_map measurable_fst.aemeasurable (hπ.1.symm ▸ hμreg)
  have htreg : ∀ᵐ p ∂χ + ξ, p.2 ∈ F.potentialRegularDomain u :=
    ae_of_ae_map measurable_snd.aemeasurable (hπ.2.symm ▸ hνreg)
  obtain ⟨K, depth, hd, hK, hsep, hall⟩ :=
    Cst.exists_original_retained_compact_truncation_splits χ ξ rfl hF hcomplete hu ha horder
      (hsreg.and htreg) hcal cell hcell hdisj hcover hθ
  obtain ⟨hsplit, hsmall, hcarriers⟩ := hall (⋃ c, cell c) (MeasurableSet.iUnion hcell)
  obtain ⟨hs, ht, hcompat⟩ := D.original_retained_clockClass_endpoint_properties
    γ originalGap hF hcomplete hu ha hinj horder hb hμreg hνreg hμinv hνinv hlabel0 hlabel1
    i hI Q U hμA hνB houter hregion χ ξ hπ Cst hgap hforward reference cell hcell hdisj hsub
    classify hmclass hclass Kcell Qglobal hwhole hχ fallbackS fallbackT P₀ hP₀
    density residual Pf hmPf hPf hdensity hresidual hrow hcol hKcell hzero
  dsimp only
  refine ⟨K, depth, hK, hd, hsep, hsmall, ?_⟩
  intro n hn
  let Ps := fun x ↦ x ∈ A ∧ ∀ c, a x ∈ cell c →
    D.corePoint i (a x, u x) = x ∧ u x ∈ (Q (reference c)).cell (classify c (u x)) ∧
      ∃ k, (D.haar.continuous.coefficient i).clockClassAllowed (Q (reference c)) (classify c (u x)) k
  let Pt := fun y ↦ y ∈ B ∧ ∀ c, a y ∈ cell c →
    D.corePoint i (a y, u y) = y ∧ u y ∈ (Q (reference c)).cell (classify c (u y)) ∧
      ∃ j, (D.haar.continuous.coefficient i).clockClassAllowed (Q (reference c)) j (classify c (u y))
  have hm c := D.measurable_originalClockClass_model hF hcomplete hu ha hinj
    i (Q (reference c)) (reference c) (classify c) (hmclass c) f
  exact Cst.original_compact_canonical_assignment_expectation_le χ ξ hπ a ha u
    horder hμreg hνreg hcal cell hcell hdisj K (fun t c ↦ (hK t c).measurableSet)
    hd hcarriers (hsep depth le_rfl) Ps Pt hs ht
    (fun c ↦ D.originalClockClassAllowed i (Q (reference c)) (classify c))
    (fun c ↦ (hm c).1) hcompat
    (fun tilt c x y ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      D.originalClockClassKinetic i (Q (reference c)) (reference c) (classify c) x y +
      tilt * D.originalClockClassProbe i (Q (reference c)) (reference c) (classify c) f x y)
    (fun tilt c ↦ (hm c).2.2.2 _ tilt) hq hn
    (fun x y ↦ f (x,y)) f.continuous.measurable (norm_nonneg f)
    (Filter.Eventually.of_forall fun p ↦ by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm p)

end OTSelector.Reconstruction
