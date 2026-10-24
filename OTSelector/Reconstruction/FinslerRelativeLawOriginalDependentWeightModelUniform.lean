import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentModelUniformInput
import OTSelector.Reconstruction.FinslerRelativeLawWindowReferenceWeightPopulation
import OTSelector.Reconstruction.FinslerConcreteUpperUniformTypedForward
import OTSelector.Reconstruction.FinslerConcreteUpperClassObservation

/-! One original dependent weight population gives the full canonical model upper bound. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
universe u₁ u₂
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 5000000
set_option linter.style.haveILetI false

variable {E : Type u₁} {M : Type u₂} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The literal unchanged old-RN model mean, uniformly over deterministic
spatial truncations, has only the original atlas in its eventual bound. -/
def PopulationLocalPressureCore.originalWeightModelUniformBound
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    {C T : Type*} [Fintype C] [Fintype T]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    {I : Set ℝ} {gap : ℝ} (coreIndex : C → Fin D.haar.continuous.count)
    (Q : C → FiniteScalarBins I gap)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (classify : ∀ c, ℝ → Fin (Q c).count) (cell : C → Set (ℚ → M))
    (f : M × M →ᵇ ℝ) (ε : ℝ)
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ] {q : ℕ}
    (Cst : PopulationTypedCostData (χ + ξ) μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x)) (ha : Measurable a) : Prop :=
    ∀ (G : ℕ → Set (ℚ → M)) (hG : ∀ n, MeasurableSet (G n)) (tilt : ℝ),
    let value := fun n ↦ D.originalClockClassOldModelValue (q := q) (n := n)
      coreIndex Q reference classify cell f tilt (T := T)
    (∀ n, 0 < n → Integrable (value n)
      ((Cst.refineSubplan (restrictOriginalRetainedResidual χ ξ a (G n))
        (restrictOriginalRetainedResidual_le χ ξ a ha (hG n))).markedLaw n)) ∧
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ n in Filter.atTop,
      (∫ sample, value n sample ∂(Cst.refineSubplan (restrictOriginalRetainedResidual χ ξ a (G n))
        (restrictOriginalRetainedResidual_le χ ξ a ha (hG n))).markedLaw n) / n ≤
      Cst.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) /
        (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * ‖f‖ + tolerance

/-- A single actual full-bin original population, original uniform atlas and
fixed classifier satisfy the reference-independent eventual model bound.
The original physical coupling and its marginals are rebuilt internally; every
later spatial truncation reads the same old-RN experiment. -/
theorem exists_original_dependent_weight_population_model_uniform_bound
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
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
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x)
    (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (πOriginal : Measure (M × M)) (hπOriginal : Vlasov.IsCoupling πOriginal μ ν)
    (hcalOriginal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂πOriginal, u p.2 - u p.1 = dist p.1 p.2)
    (hI : IsCompact I) (hgapOriginal : 0 < originalGap)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (hUopen : ∀ i ref, IsOpen (U i ref)) (hUself : ∀ i ref, ref.val ∈ U i ref)
    (houter : ∀ i ref j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q i ref) j k →
      ∀ s ∈ (Q i ref).cell j, ∀ t ∈ (Q i ref).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1)
    (hregion : ∀ i ref,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U i ref,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U i ref,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      ∀ t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      s < t → D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
        (s, t) ∈ (D.haar.continuous.coefficient i).window.region)
    (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (retentionError splitError : ℝ) (hretention : 0 < retentionError)
    (hretention1 : retentionError < 1) (hsplitError : 0 < splitError)
    (f : M × M →ᵇ ℝ) {ε : ℝ} (hsmall : 3 * ε + 2 * ε ^ 2 < 1)
    (hkin : ∀ i ref,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U i ref,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U i ref,
      ∀ j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q i ref) j k →
      ∀ s ∈ (Q i ref).cell j, ∀ t ∈ (Q i ref).cell k,
      D.corePoint i (z,s) ∈ A → D.corePoint i (z',t) ∈ B →
      let C₀ := D.haar.continuous.coefficient i
      let S := (P C₀.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let vec := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
      |populationSeedPairDeficit S (s,t) (R z,R z') -
        C₀.clockClassKinetic (Q i ref) ref.val j k vec| ≤
          (3 * ε + 2 * ε ^ 2) * C₀.clockClassKinetic (Q i ref) ref.val j k vec)
    (hq : 4 < Module.finrank ℝ E - 1) :
    let q := Module.finrank ℝ E - 1
    let cost := fun x y ↦ (F.lengthEDist x y).toReal - u y + u x
    ∃ (T : Type (max u₁ u₂)) (hT : Fintype T) (quadC Bnd forwardGap : ℝ),
    let _inst : Fintype T := hT
    0 ≤ quadC ∧ 0 ≤ Bnd ∧ 0 < forwardGap ∧
    ∃ (N : Fin D.haar.continuous.count → ℕ)
      (refs : ∀ i, Fin (N i) → (D.haar.continuous.coefficient i).roots)
      (cells : ∀ i, Fin (N i) → Set (ℚ → M))
      (Pf Qf : ∀ i c, (ℚ → M) → Fin (Q i (refs i c)).count → Fin (Q i (refs i c)).count → ℝ)
      (hcells : ∀ i c, MeasurableSet (cells i c)),
      (∀ i c, cells i c ⊆ (D.haar.continuous.coefficient i).roots ∩ U i (refs i c)) ∧
      (∀ i c j k, Measurable (fun z ↦ Pf i c z j k)) ∧
      (∀ i c j k, Measurable (fun z ↦ Qf i c z j k)) ∧
      (∀ i c z, z ∈ cells i c →
        (∀ j k, 0 ≤ Pf i c z j k) ∧ (∀ j k, 0 ≤ Qf i c z j k) ∧
        (∀ j, ∑ k, (Pf i c z j k + Qf i c z j k) =
          (condDistrib u a μ z).real ((Q i (refs i c)).cell j)) ∧
        (∀ k, ∑ j, (Pf i c z j k + Qf i c z j k) =
          (condDistrib u a ν z).real ((Q i (refs i c)).cell k)) ∧
        (∀ j k, ¬ sSup ((Q i (refs i c)).cell j) + originalGap / 2 ≤ sInf ((Q i (refs i c)).cell k) →
          Pf i c z j k = 0 ∧ Qf i c z j k = 0) ∧
        (∑ j, ∑ k, Qf i c z j k) ≤ retentionError + splitError + δ.toReal) ∧
      (∀ i c,
        let P₀ := D.originalWindowReferenceWeights γ originalGap I i (refs i c) (Q i (refs i c)) retentionError
        (∀ j k, 0 ≤ P₀ j k) ∧
        (∀ j k, ¬(D.haar.continuous.coefficient i).clockClassAllowed (Q i (refs i c)) j k → P₀ j k = 0) ∧
        (1 - retentionError) * D.rootIntensity i (refs i c).val * (1 - δ.toReal) ≤ (∑ j, ∑ k, P₀ j k) ∧
        0 < ∑ j, ∑ k, P₀ j k) ∧
      (∀ i c z, z ∈ cells i c → ∀ j k, Pf i c z j k =
        D.originalWindowReferenceWeights γ originalGap I i (refs i c) (Q i (refs i c)) retentionError j k /
          D.rootIntensity i z) ∧
      let C := Sigma (fun i ↦ Fin (N i))
      let coreIndex := fun c : C ↦ c.1
      let reference := fun c : C ↦ refs c.1 c.2
      let cell := fun c : C ↦ cells c.1 c.2
      let hcell := fun c : C ↦ hcells c.1 c.2
      let Q := fun c : C ↦ Q c.1 (reference c)
      let _inst : DecidableEq T := Classical.decEq T
      let _inst : MeasurableSpace (Option T) := ⊤
      let _inst : MeasurableSpace (Option (C × T)) := ⊤
      let _inst : MeasurableSpace (Option (Bool × T)) := ⊤
      let _inst : MeasurableSpace (Option (CellRefinedType C T)) := ⊤
      let α := fun (c : C) j ↦ normalizedActualBinKernel (condDistrib u a μ)
        ((Q c).cell j) ((Q c).measurable_cell j) 0
      let β := fun (c : C) k ↦ normalizedActualBinKernel (condDistrib u a ν)
        ((Q c).cell k) ((Q c).measurable_cell k) 0
      let KP := fun c : C ↦ finiteClassPopulationKernel (Pf c.1 c.2) (α c) (β c)
      let χ := (((μ.map a) ⊗ₘ finiteCellPairKernel cell hcell KP).map
        sameLabelPopulationPair).map (Prod.map b b)
      ∃ _hdisj : Pairwise (Disjoint on cell),
      (⋃ c, cell c) = D.haar.continuous.population.roots ∧
      ∃ (Qglobal : Kernel (ℚ → M) (ℝ × ℝ)) (_hQglobal : IsSFiniteKernel Qglobal),
      (∀ᵐ z ∂μ.map a, Vlasov.IsCoupling
        (finiteCellPairKernel cell hcell KP z + Qglobal z)
        (condDistrib u a μ z) (condDistrib u a ν z)) ∧
      ∃ (ξ : Measure (M × M)) (hχfinite : IsFiniteMeasure χ) (hξfinite : IsFiniteMeasure ξ),
      let _inst : IsFiniteMeasure χ := hχfinite
      let _inst : IsFiniteMeasure ξ := hξfinite
      ∃ _hπ : Vlasov.IsCoupling (χ + ξ) μ ν,
      (let _inst : MetricSpace M := F.metricSpace
        ∀ᵐ p ∂χ + ξ, u p.2 - u p.1 = dist p.1 p.2) ∧
      ξ univ ≤ ENNReal.ofReal (retentionError + splitError + δ.toReal) +
        (μ.map a) D.haar.continuous.population.rootsᶜ ∧
      ∃ Cst : PopulationTypedCostData (χ + ξ) μ ν T q cost,
      Cst.quadraticConstant = quadC ∧ Cst.globalBound = Bnd ∧
      (∀ t x y, Cst.sourceGood t x → Cst.targetGood t y → forwardGap ≤ u y - u x) ∧
      ∃ classify : ∀ c, ℝ → Fin (Q c).count,
      (∀ c, Measurable (classify c)) ∧
      (∀ c j s, s ∈ (Q c).cell j → classify c s = j) ∧
      D.originalWeightModelUniformBound coreIndex Q reference classify cell f ε χ ξ Cst ha := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  letI : BorelSpace (ℚ → M) := inferInstance
  have hum : Measurable u := hu.continuous.measurable
  have hlabelForward := original_calibrated_coupling_labels μ ν πOriginal πOriginal
    hπOriginal le_rfl a u horder hμreg hνreg hcalOriginal
  have hlabel := hlabelForward.mono fun _ h ↦ h.1
  have hforwardOriginal := hlabelForward.mono fun _ h ↦ h.2
  obtain ⟨_, _, hbalance, _, _, _⟩ := exists_original_clockPair_kernel μ ν πOriginal
    hπOriginal a u ha hum hlabel 0
      (hforwardOriginal.mono fun _ h ↦ sub_nonneg.mpr h)
  obtain ⟨T, hT, quadC, Bnd, forwardGap, hquadC, hBnd, hfgap, hatlas⟩ :=
    exists_uniform_forward_populationTypedCostData_of_calibrated_coupling hF hcomplete hu
      ha hinj horder hA hB hAB hμA hνB hμreg hνreg
  letI : Fintype T := hT
  letI : DecidableEq T := Classical.decEq T
  obtain ⟨N, refs, cells, Pf, Qf, hcells, hsub, hmP, hmQ, hflows, hweights, hform, hglobal⟩ :=
    exists_original_clockClass_weight_sampling_population_with_inverse γ originalGap I D
      hcomplete (hF.measurableSet_potentialRegularDomain hcomplete u) ha hum horder
      hμreg hνreg hb hμinv hνinv πOriginal hπOriginal hlabel hforwardOriginal
      hI hgapOriginal Q U hUopen hUself hδ hδ1 retentionError splitError
      hretention hretention1 hsplitError
  let C := Sigma (fun i ↦ Fin (N i))
  let coreIndex := fun c : C ↦ c.1
  let reference := fun c : C ↦ refs c.1 c.2
  let cell := fun c : C ↦ cells c.1 c.2
  let hcell := fun c : C ↦ hcells c.1 c.2
  let Qcell := fun c : C ↦ Q c.1 (reference c)
  let Ucell := fun c : C ↦ U c.1 (reference c)
  let α := fun (c : C) j ↦ normalizedActualBinKernel (condDistrib u a μ)
    ((Qcell c).cell j) ((Qcell c).measurable_cell j) 0
  let β := fun (c : C) k ↦ normalizedActualBinKernel (condDistrib u a ν)
    ((Qcell c).cell k) ((Qcell c).measurable_cell k) 0
  let KP := fun c : C ↦ finiteClassPopulationKernel (Pf c.1 c.2) (α c) (β c)
  let χ := (((μ.map a) ⊗ₘ finiteCellPairKernel cell hcell KP).map
    sameLabelPopulationPair).map (Prod.map b b)
  dsimp only at hglobal
  obtain ⟨hdisj, hunion, Qglobal, hQglobal, hwhole, ξ, hπ, hcal, hξ, hmass⟩ := hglobal
  letI : IsSFiniteKernel Qglobal := hQglobal
  haveI : IsProbabilityMeasure ((χ + ξ).map Prod.fst) := hπ.1.symm ▸ inferInstance
  letI : IsProbabilityMeasure (χ + ξ) := Measure.isProbabilityMeasure_of_map Prod.fst
  letI : IsFiniteMeasure χ := isFiniteMeasure_of_le (χ + ξ) (Measure.le_add_right le_rfl)
  letI : IsFiniteMeasure ξ := isFiniteMeasure_of_le (χ + ξ) (Measure.le_add_left le_rfl)
  obtain ⟨Cst, hCstC, hCstBnd, hforward⟩ := hatlas (χ + ξ) inferInstance hπ hcal
  let P₀ := fun (c : C) ↦ D.originalWindowReferenceWeights γ originalGap I
    (coreIndex c) (reference c) (Qcell c) retentionError
  have hnonempty (c : C) : Nonempty (Fin (Qcell c).count) := by
    by_contra hn
    haveI : IsEmpty (Fin (Qcell c).count) := not_nonempty_iff.mp hn
    have hzero : (∑ j, ∑ k, P₀ c j k) = 0 := by simp
    exact (ne_of_gt (hweights c.1 c.2).2.2.2) hzero
  let classify := fun c : C ↦ (Qcell c).classify (Classical.choice (hnonempty c))
  have hmclass (c : C) : Measurable (classify c) := (Qcell c).measurable_classify _
  have hclass (c : C) (j) (s) (hs : s ∈ (Qcell c).cell j) : classify c s = j :=
    (Qcell c).classify_eq_of_mem _ j hs
  letI : MeasurableSpace (Option T) := ⊤
  letI : MeasurableSpace (Option (C × T)) := ⊤
  letI : MeasurableSpace (Option (Bool × T)) := ⊤
  letI : MeasurableSpace (Option (CellRefinedType C T)) := ⊤
  dsimp only
  refine ⟨T, hT, quadC, Bnd, forwardGap, hquadC, hBnd, hfgap,
    N, refs, cells, Pf, Qf, hcells, hsub, hmP, hmQ, hflows, hweights, hform,
    hdisj, hunion, Qglobal, hQglobal, hwhole, ξ, inferInstance, inferInstance,
    hπ, hcal, hmass, Cst, hCstC, hCstBnd, hforward, classify, hmclass, hclass, ?_⟩
  have hPf (c : C) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ j k,
      Pf c.1 c.2 z j k = P₀ c j k / D.rootIntensity (coreIndex c) z :=
    (ae_restrict_mem (hcell c)).mono fun z hz ↦ hform c.1 c.2 z hz
  have hdensity (c : C) : ∀ᵐ z ∂(μ.map a).restrict (cell c),
      0 < D.rootIntensity (coreIndex c) z := by
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    have hzroots : z ∈ (D.haar.intensity (coreIndex c)).roots := by
      rw [D.haar.intensity_roots]
      exact (hsub c.1 c.2 hz).1
    exact (D.haar.intensity (coreIndex c)).lower_pos.trans_le
      ((D.haar.intensity (coreIndex c)).bounds _ (mem_image_of_mem _ hzroots)).1
  have hresidual (c : C) : ∀ᵐ z ∂(μ.map a).restrict (cell c),
      ∀ j k, 0 ≤ Qf c.1 c.2 z j k :=
    (ae_restrict_mem (hcell c)).mono fun z hz ↦ (hflows c.1 c.2 z hz).2.1
  have hrow (c : C) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ j,
      ∑ k, (P₀ c j k / D.rootIntensity (coreIndex c) z + Qf c.1 c.2 z j k) =
        (condDistrib u a μ z).real ((Qcell c).cell j) := by
    filter_upwards [hPf c, ae_restrict_mem (hcell c)] with z hz hzcell
    simpa only [← hz] using (hflows c.1 c.2 z hzcell).2.2.1
  have hcol (c : C) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ k,
      ∑ j, (P₀ c j k / D.rootIntensity (coreIndex c) z + Qf c.1 c.2 z j k) =
        (condDistrib u a ν z).real ((Qcell c).cell k) := by
    filter_upwards [hPf c, ae_restrict_mem (hcell c)] with z hz hzcell
    simpa only [← hz] using (hflows c.1 c.2 z hzcell).2.2.2.1
  exact D.original_dependent_clockClass_model_eventually_le γ originalGap
    hF hcomplete hu ha hinj horder hb hμreg hνreg hμinv hνinv rfl hbalance.symm
    hI.measurableSet coreIndex reference Qcell Ucell hμA hνB
    (fun c ↦ houter c.1 (reference c)) (fun c ↦ hregion c.1 (reference c)) χ ξ hπ Cst hcal
    hfgap hforward cell hcell hdisj (fun c ↦ hsub c.1 c.2) classify hmclass hclass
    KP Qglobal hwhole rfl (fun _ _ ↦ 0) (fun _ _ ↦ 0) P₀
    (fun c ↦ (hweights c.1 c.2).1) (fun c ↦ D.rootIntensity (coreIndex c))
    (fun c ↦ Qf c.1 c.2) (fun c ↦ Pf c.1 c.2) (fun c ↦ hmP c.1 c.2)
    hPf hdensity hresidual hrow hcol (fun _ ↦ rfl)
    (fun c ↦ (hweights c.1 c.2).2.1) f hsmall (fun c ↦ hkin c.1 (reference c)) hq

end OTSelector.Reconstruction
