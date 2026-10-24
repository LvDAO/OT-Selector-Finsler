import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentCellwiseCutoffUpper
import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentModelUniformInput
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelCountError
import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentModelTrace

/-! The original global expected assignment pays relative geometry through one uniform atlas bound. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option linter.style.haveILetI false

/-- All original full-assignment completion discrepancies vanish at the fixed
compact hierarchy depths, including the true residual cardinality discrepancy. -/
theorem tendsto_original_assignment_completion_error_zero
    {C T : Type*} [Fintype C] [Fintype T] {q : ℕ} (hq : 4 < q)
    (B G tilt : ℝ) (depth : ℕ) :
    Filter.Tendsto (fun n : ℕ ↦
      ((n : ℝ) ^ (2 / (q : ℝ)) * B + |tilt| * G) *
        (((Fintype.card T : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ depth + 1) ^ q) +
          (Fintype.card (C × T) : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q)) / n +
          Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T))) / n)) Filter.atTop (𝓝 0) := by
  have hg := tendsto_original_model_good_bad_count_error_zero (C := Unit) hq
    (fun _ ↦ 1) (fun _ ↦ B) G tilt (Fintype.card T) (Fintype.card (C × T)) depth
  have hr := tendsto_original_model_count_price_zero (C := Unit) hq
    (fun _ ↦ 1) (fun _ ↦ B) G tilt (Fintype.card (Option (Bool × T)))
  have h := hg.add hr
  simp only [zero_add] at h
  convert h using 1
  funext n
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul]
  ring

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

/-- The original empirical full assignment has coefficient one on its SAME
canonical model mean. Relative geometry is paid by the original atlas constant;
true residual mass remains the original cellwise label-loss parameter. -/
theorem PopulationLocalPressureCore.original_dependent_cellwise_sharp_expected_upper
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
    (f : M × M →ᵇ ℝ) {ε probeError : ℝ} (hρ : 0 ≤ 3 * ε + 2 * ε ^ 2) (hprobe : 0 ≤ probeError)
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
        (3 * ε + 2 * ε ^ 2) * C₀.clockClassKinetic (Q c) (reference c).val j k
          ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z)) ∧
      |f (D.corePoint (coreIndex c) (z,s),D.corePoint (coreIndex c) (z',t)) -
        C₀.clockClassProbe (Q c) (reference c).val (reference c).property f j k| ≤ 2 * probeError)
    (hq : 4 < q) (hsmall : 3 * ε + 2 * ε ^ 2 < 1) :
    ∀ (cutoff : ℕ → C → Set (ℚ → M))
      (hcutoff : ∀ n c, MeasurableSet (cutoff n c)) (tilt : ℝ),
    let G := fun n ↦ ⋃ c, cell c ∩ cutoff n c
    let hG := fun n ↦ MeasurableSet.iUnion fun c ↦ (hcell c).inter (hcutoff n c)
    let β := fun n ↦ (ξ univ).toReal + ∑ c, (μ.map a).real (cell c \ cutoff n c)
    let law := fun n ↦ (Cst.refineSubplan (restrictOriginalRetainedResidual χ ξ a (G n))
      (restrictOriginalRetainedResidual_le χ ξ a ha (hG n))).markedLaw n
    let model := fun n ↦ D.originalClockClassOldModelValue (q := q) (n := n)
      coreIndex Q reference classify cell f tilt (T := T)
    let iid := fun n ↦ (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
    let assignment := fun n (sample : (Fin n → M) × (Fin n → M)) ↦ perturbedAssignmentValue
      (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
        ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
        tilt * f (sample.1 i,sample.2 j)) 0 0
    (∀ n, 0 < n → Integrable (assignment n) (iid n) ∧ Integrable (model n) (law n)) ∧
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ n in Filter.atTop,
      (∫ sample, assignment n sample ∂iid n) / n ≤
        (∫ sample, model n sample ∂law n) / n +
        (3 * ε + 2 * ε ^ 2) *
          (Cst.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) /
            (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * ‖f‖ + 1) +
        (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)) +
        (Cst.quadraticConstant * dyadicMatchingConstant q *
          (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (β n) ^ (1 - 2 / (q : ℝ)) +
          2 * |tilt| * ‖f‖ * β n) + tolerance := by
  obtain ⟨K,depth,hK,hd,hsep,hall⟩ :=
    D.exists_original_dependent_cellwise_cutoff_expected_upper γ originalGap
      hF hcomplete hu ha hinj horder hb hμreg hνreg hμinv hνinv hlabel0 hlabel1
      hI coreIndex reference Q U hμA hνB houter hregion χ ξ hπ Cst hcal hgap hforward
      cell hcell hdisj hsub classify hmclass hclass Kcell Qglobal hwhole hχ
      fallbackS fallbackT P₀ hP₀ density residual Pf hmPf hPf hdensity hresidual hrow hcol hKcell hzero
      f hρ hprobe hgeometry hq zero_lt_one
  have hkin := fun c z hz z' hz' j k hjk s hs t ht hA hB ↦
    (hgeometry c z hz z' hz' j k hjk s hs t ht hA hB).2.1
  have huniform := D.original_dependent_clockClass_model_eventually_le γ originalGap
    hF hcomplete hu ha hinj horder hb hμreg hνreg hμinv hνinv hlabel0 hlabel1
    hI coreIndex reference Q U hμA hνB houter hregion χ ξ hπ Cst hcal hgap hforward
    cell hcell hdisj hsub classify hmclass hclass Kcell Qglobal hwhole hχ
    fallbackS fallbackT P₀ hP₀ density residual Pf hmPf hPf hdensity hresidual hrow hcol hKcell hzero
    f hsmall hkin hq
  intro cutoff hcutoff tilt
  let G := fun n ↦ ⋃ c, cell c ∩ cutoff n c
  have hG (n : ℕ) : MeasurableSet (G n) :=
    MeasurableSet.iUnion fun c ↦ (hcell c).inter (hcutoff n c)
  let β := fun n ↦ (ξ univ).toReal + ∑ c, (μ.map a).real (cell c \ cutoff n c)
  let law := fun n ↦ (Cst.refineSubplan (restrictOriginalRetainedResidual χ ξ a (G n))
    (restrictOriginalRetainedResidual_le χ ξ a ha (hG n))).markedLaw n
  let model := fun n ↦ D.originalClockClassOldModelValue (q := q) (n := n)
    coreIndex Q reference classify cell f tilt (T := T)
  let iid := fun n ↦ (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
  let assignment := fun n (sample : (Fin n → M) × (Fin n → M)) ↦ perturbedAssignmentValue
    (fun i j ↦ (n : ℝ) ^ (2 / (q : ℝ)) *
      ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
      tilt * f (sample.1 i,sample.2 j)) 0 0
  let mean := fun n ↦ (∫ sample, model n sample ∂law n) / n
  let actual := fun n ↦ (∫ sample, assignment n sample ∂iid n) / n
  let residual := fun n ↦ Cst.quadraticConstant * dyadicMatchingConstant q *
    (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (β n) ^ (1 - 2 / (q : ℝ)) +
    Cst.globalBound * Real.sqrt (2 * Fintype.card T) *
      (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) * Real.sqrt (β n) +
    2 * |tilt| * ‖f‖ * β n
  let mainResidual := fun n ↦ Cst.quadraticConstant * dyadicMatchingConstant q *
    (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) * (β n) ^ (1 - 2 / (q : ℝ)) +
    2 * |tilt| * ‖f‖ * β n
  let completion := fun (n : ℕ) ↦
    ((n : ℝ) ^ (2 / (q : ℝ)) * Cst.globalBound + |tilt| * ‖f‖) *
      (((Fintype.card T : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ depth + 1) ^ q) +
        (Fintype.card (C × T) : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q)) / n +
        Real.sqrt (2 * (n : ℝ) * Fintype.card (Option (Bool × T))) / n)
  have hpoint (n : ℕ) (hn : 0 < n) : Integrable (assignment n) (iid n) ∧
      actual n ≤ (1 + (3 * ε + 2 * ε ^ 2)) * mean n +
        (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)) + residual n + completion n := by
    obtain ⟨_,_,hηeq,_,hallN⟩ := hall (cutoff n) (hcutoff n)
    obtain ⟨hVI,_,_,hBound⟩ := hallN n hn tilt
    refine ⟨hVI,?_⟩
    have hRef :
        Cst.refineSubplan (restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ G n))
          (restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion fun c ↦ (hcell c).inter (hG n))) =
        Cst.refineSubplan (restrictOriginalRetainedResidual χ ξ a (G n))
          (restrictOriginalRetainedResidual_le χ ξ a ha (hG n)) := by
      congr 1
    rw [hRef] at hBound
    have htrace := D.original_dependent_model_trace_integral hcomplete hu ha hb
      hμinv hνinv hlabel0 hlabel1 coreIndex Q reference classify cell hcell
      Kcell Qglobal hwhole χ ξ hχ Cst (hG n) f tilt (n := n)
    change actual n ≤ (1 + (3 * ε + 2 * ε ^ 2)) *
      ((∫ sample, D.originalClockClassOldModelValue (q := q) (n := n)
        coreIndex Q reference classify (fun c ↦ cell c ∩ G n) f tilt (T := T) sample ∂law n) / n) +
      (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)) + residual n + completion n at hBound
    rw [htrace.2] at hBound
    exact hBound
  have hmodel := huniform G hG tilt
  dsimp only
  refine ⟨fun n hn ↦ ⟨(hpoint n hn).1,hmodel.1 n hn⟩,?_⟩
  intro tolerance htolerance
  let βmax := (ξ univ).toReal + (Fintype.card C : ℝ)
  haveI : IsProbabilityMeasure (μ.map a) := Measure.isProbabilityMeasure_map ha.aemeasurable
  have hβmax (n : ℕ) : β n ≤ βmax := by
    change (ξ univ).toReal + (∑ c, (μ.map a).real (cell c \ cutoff n c)) ≤
      (ξ univ).toReal + (Fintype.card C : ℝ)
    apply add_le_add (le_refl ((ξ univ).toReal))
    calc
      (∑ c, (μ.map a).real (cell c \ cutoff n c)) ≤ ∑ _c : C, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ ↦ measureReal_le_one
      _ = (Fintype.card C : ℝ) := by simp
  let error := fun (n : ℕ) ↦ Cst.globalBound * Real.sqrt (2 * Fintype.card T) * Real.sqrt βmax *
      (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) + completion n
  have herror : Filter.Tendsto error Filter.atTop (𝓝 0) := by
    have h1 := tendsto_original_model_energy_count_zero hq
      (Cst.globalBound * Real.sqrt (2 * Fintype.card T) * Real.sqrt βmax)
    have h2 := tendsto_original_assignment_completion_error_zero (C := C) (T := T)
      hq Cst.globalBound ‖f‖ tilt depth
    simpa only [zero_add] using h1.add h2
  have herrorSmall : ∀ᶠ n in Filter.atTop, error n < tolerance :=
    herror.eventually (gt_mem_nhds htolerance)
  have hmodelBound := hmodel.2 1 zero_lt_one
  filter_upwards [Filter.eventually_ge_atTop 1,hmodelBound,herrorSmall] with n hn hm he
  have hnpos : 0 < n := by omega
  have hres : residual n ≤ mainResidual n +
      Cst.globalBound * Real.sqrt (2 * Fintype.card T) * Real.sqrt βmax *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) := by
    have hsqrt : (Cst.globalBound * Real.sqrt (2 * Fintype.card T) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2)) * Real.sqrt (β n) ≤
        (Cst.globalBound * Real.sqrt (2 * Fintype.card T) *
        (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2)) * Real.sqrt βmax :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hβmax n))
      (mul_nonneg (mul_nonneg Cst.bound_nonneg (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    dsimp only [residual,mainResidual]
    nlinarith only [hsqrt]
  have hscaled : (1 + (3 * ε + 2 * ε ^ 2)) * mean n ≤ mean n +
      (3 * ε + 2 * ε ^ 2) *
        (Cst.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) /
          (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * ‖f‖ + 1) := by
    have h := mul_le_mul_of_nonneg_left hm hρ
    change (3 * ε + 2 * ε ^ 2) * mean n ≤ _ at h
    nlinarith only [h]
  have hfinal := (hpoint n hnpos).2.trans
    (add_le_add (add_le_add (add_le_add hscaled
      (le_refl (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖)))) hres)
        (le_refl (completion n)))
  change actual n ≤ _
  dsimp only [error] at he
  dsimp only [mainResidual] at hfinal
  linarith only [hfinal,he]

end OTSelector.Reconstruction
