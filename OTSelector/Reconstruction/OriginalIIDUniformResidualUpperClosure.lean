import OTSelector.Reconstruction.OriginalIIDActualSupportedUpperErrors

/-!
# Uniform original residual repair across actual refined upper populations

The same whole-pair geometry is fixed before the frozen cores and retained populations.
The original sharp comparison still uses its actual full iid assignment and the exact
rebuilt calibrated population, while its quadratic residual constant is fixed globally.
The empirical limit is taken at each fixed refinement before refinement tends to infinity.
The leading original finite-family pressures remain explicit at each refinement.
-/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
universe u₁ u₂
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
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


/-- The original population packet with a prescribed whole-pair atlas. -/
def PopulationLocalPressureCore.originalFixedAtlasSharpPopulationData
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ) (f : M × M →ᵇ ℝ) (ε probeError : ℝ)
    (ha : Measurable a)
    (T : Type (max u₁ u₂)) [Fintype T] (quadC Bnd forwardGap : ℝ) : Prop :=
    let q := Module.finrank ℝ E - 1
    let cost := fun x y ↦ (F.lengthEDist x y).toReal - u y + u x
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
      D.originalWeightSharpExpectedBound coreIndex Q reference classify cell hcell f ε probeError χ ξ Cst ha


private theorem original_fixed_atlas_sharp_population
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
    {A B : Set M} (_hA : IsCompact A) (_hB : IsCompact B) (_hAB : Disjoint A B)
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
    (f : M × M →ᵇ ℝ) {ε probeError : ℝ} (hρ : 0 ≤ 3 * ε + 2 * ε ^ 2) (hprobe : 0 ≤ probeError)
    (hgeometry : ∀ i ref,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U i ref,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U i ref,
      ∀ j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q i ref) j k →
      ∀ s ∈ (Q i ref).cell j, ∀ t ∈ (Q i ref).cell k,
      D.corePoint i (z,s) ∈ A → D.corePoint i (z',t) ∈ B →
      let C₀ := D.haar.continuous.coefficient i
      let S := (P C₀.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      (s,t) ∈ C₀.window.region ∧
      |populationSeedPairDeficit S (s,t) (R z,R z') -
        C₀.clockClassKinetic (Q i ref) ref.val j k
          ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z))| ≤
        (3 * ε + 2 * ε ^ 2) * C₀.clockClassKinetic (Q i ref) ref.val j k
          ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z)) ∧
      |f (D.corePoint i (z,s),D.corePoint i (z',t)) -
        C₀.clockClassProbe (Q i ref) ref.val ref.property f j k| ≤ 2 * probeError)
    (hq : 4 < Module.finrank ℝ E - 1) (hsmall : 3 * ε + 2 * ε ^ 2 < 1)
    {T : Type (max u₁ u₂)} [Fintype T] (quadC Bnd forwardGap : ℝ) (hfgap : 0 < forwardGap)
    (hatlas : ∀ (π : Measure (M × M)) (hfinite : IsFiniteMeasure π),
      let _inst : IsFiniteMeasure π := hfinite
      Vlasov.IsCoupling π μ ν →
      (let _inst : MetricSpace M := F.metricSpace
        ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2) →
      ∃ Cst : PopulationTypedCostData π μ ν T (Module.finrank ℝ E - 1)
        (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x),
        Cst.quadraticConstant = quadC ∧ Cst.globalBound = Bnd ∧
        ∀ t x y, Cst.sourceGood t x → Cst.targetGood t y → forwardGap ≤ u y - u x) :
    D.originalFixedAtlasSharpPopulationData γ originalGap Q U retentionError splitError
      f ε probeError ha T quadC Bnd forwardGap := by
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
  unfold PopulationLocalPressureCore.originalFixedAtlasSharpPopulationData
  dsimp only
  refine ⟨N, refs, cells, Pf, Qf, hcells, hsub, hmP, hmQ, hflows, hweights, hform,
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
  exact D.original_dependent_cellwise_sharp_expected_upper γ originalGap
    hF hcomplete hu ha hinj horder hb hμreg hνreg hμinv hνinv rfl hbalance.symm
    hI.measurableSet coreIndex reference Qcell Ucell hμA hνB
    (fun c ↦ houter c.1 (reference c)) (fun c ↦ hregion c.1 (reference c)) χ ξ hπ Cst hcal
    hfgap hforward cell hcell hdisj (fun c ↦ hsub c.1 c.2) classify hmclass hclass
    KP Qglobal hwhole rfl (fun _ _ ↦ 0) (fun _ _ ↦ 0) P₀
    (fun c ↦ (hweights c.1 c.2).1) (fun c ↦ D.rootIntensity (coreIndex c))
    (fun c ↦ Qf c.1 c.2) (fun c ↦ Pf c.1 c.2) (fun c ↦ hmP c.1 c.2)
    hPf hdensity hresidual hrow hcol (fun _ ↦ rfl)
    (fun c ↦ (hweights c.1 c.2).2.1) f hρ hprobe
    (fun c ↦ hgeometry c.1 (reference c)) hq hsmall

/-- One original geometric atlas supplies the actual sharp comparison at every frozen
core and every retained population. The constants and type space precede all refinements. -/
theorem exists_uniform_original_sharp_population_factory
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (originalGap : ℝ)
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
    (hq : 4 < Module.finrank ℝ E - 1) :
    ∃ (T : Type (max u₁ u₂)) (hT : Fintype T) (quadC Bnd forwardGap : ℝ),
      let _inst : Fintype T := hT
      0 ≤ quadC ∧ 0 ≤ Bnd ∧ 0 < forwardGap ∧
      ∀ (δ loss : ℝ≥0∞)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (_hUopen : ∀ i ref, IsOpen (U i ref)) (_hUself : ∀ i ref, ref.val ∈ U i ref)
    (_houter : ∀ i ref j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q i ref) j k →
      ∀ s ∈ (Q i ref).cell j, ∀ t ∈ (Q i ref).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1)
    (_hregion : ∀ i ref,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U i ref,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U i ref,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      ∀ t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      s < t → D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
        (s, t) ∈ (D.haar.continuous.coefficient i).window.region)
    (_hδ : δ ≠ ⊤) (_hδ1 : δ.toReal < 1)
    (retentionError splitError : ℝ) (_hretention : 0 < retentionError)
    (_hretention1 : retentionError < 1) (_hsplitError : 0 < splitError)
    (f : M × M →ᵇ ℝ) {ε probeError : ℝ} (_hρ : 0 ≤ 3 * ε + 2 * ε ^ 2) (_hprobe : 0 ≤ probeError)
    (_hgeometry : ∀ i ref,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U i ref,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U i ref,
      ∀ j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q i ref) j k →
      ∀ s ∈ (Q i ref).cell j, ∀ t ∈ (Q i ref).cell k,
      D.corePoint i (z,s) ∈ A → D.corePoint i (z',t) ∈ B →
      let C₀ := D.haar.continuous.coefficient i
      let S := (P C₀.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      (s,t) ∈ C₀.window.region ∧
      |populationSeedPairDeficit S (s,t) (R z,R z') -
        C₀.clockClassKinetic (Q i ref) ref.val j k
          ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z))| ≤
        (3 * ε + 2 * ε ^ 2) * C₀.clockClassKinetic (Q i ref) ref.val j k
          ((Module.finBasis ℝ S.covector.ker).equivFun (R z'-R z)) ∧
      |f (D.corePoint i (z,s),D.corePoint i (z',t)) -
        C₀.clockClassProbe (Q i ref) ref.val ref.property f j k| ≤ 2 * probeError)
    (_hsmall : 3 * ε + 2 * ε ^ 2 < 1),
    D.originalFixedAtlasSharpPopulationData γ originalGap Q U retentionError splitError
      f ε probeError ha T quadC Bnd forwardGap := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instBorelLabels : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨T, hT, quadC, Bnd, forwardGap, hquadC, hBnd, hfgap, hatlas⟩ :=
    exists_uniform_forward_populationTypedCostData_of_calibrated_coupling hF hcomplete hu
      ha hinj horder hA hB hAB hμA hνB hμreg hνreg
  let _inst : Fintype T := hT
  refine ⟨T, hT, quadC, Bnd, forwardGap, hquadC, hBnd, hfgap, ?_⟩
  intro δ loss D Q U hUopen hUself houter hregion hδ hδ1 retentionError splitError
    hretention hretention1 hsplitError f ε probeError hρ hprobe hgeometry hsmall
  exact original_fixed_atlas_sharp_population γ originalGap D hF hcomplete hu ha hinj
    horder hb hμreg hνreg hμinv hνinv hA hB hAB hμA hνB πOriginal hπOriginal
    hcalOriginal hI hgapOriginal Q U hUopen hUself houter hregion hδ hδ1 retentionError
    splitError hretention hretention1 hsplitError f hρ hprobe hgeometry hq hsmall
    quadC Bnd forwardGap hfgap hatlas

/-- The exact deterministic error used by the original full assignment comparison. -/
def originalUniformUpperError (q : ℕ) (A tilt probeNorm ε probeError residual : ℝ) : ℝ :=
  (3 * ε + 2 * ε ^ 2) *
    (A / (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * probeNorm + 1) +
  (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * probeNorm)) +
  (A * residual ^ (1 - 2 / (q : ℝ)) + 2 * |tilt| * probeNorm * residual)

/-- The explicit accuracy is small enough for the original relative geometry estimate. -/
theorem originalUpperRefinementGeometry_small (k : ℕ) :
    0 < originalUpperRefinementAccuracy k / 10 ∧
    0 ≤ 3 * (originalUpperRefinementAccuracy k / 10) +
      2 * (originalUpperRefinementAccuracy k / 10) ^ 2 ∧
    3 * (originalUpperRefinementAccuracy k / 10) +
      2 * (originalUpperRefinementAccuracy k / 10) ^ 2 < 1 := by
  obtain ⟨hp, hlt⟩ := originalUpperRefinementAccuracy_pos_lt_one k
  constructor
  · positivity
  constructor
  · positivity
  nlinarith [sq_nonneg (originalUpperRefinementAccuracy k)]

/-- The literal geometry and discarded-mass errors vanish for the explicitly refined
cores once their actual whole-pair constant is fixed before refinement. -/
theorem tendsto_original_uniform_upper_errors
    (q : ℕ) (hq : 4 < q) (A tilt probeNorm : ℝ)
    (residual : ℕ → ℝ) (hres : ∀ k, 0 ≤ residual k ∧
      residual k ≤ 4 * originalUpperRefinementAccuracy k) :
    Tendsto (fun k ↦
      (3 * (originalUpperRefinementAccuracy k / 10) +
        2 * (originalUpperRefinementAccuracy k / 10) ^ 2) *
        (A / (1 - (3 * (originalUpperRefinementAccuracy k / 10) +
          2 * (originalUpperRefinementAccuracy k / 10) ^ 2)) + |tilt| * probeNorm + 1) +
      (|tilt| * (2 * originalUpperRefinementAccuracy k) +
        (3 * (originalUpperRefinementAccuracy k / 10) +
          2 * (originalUpperRefinementAccuracy k / 10) ^ 2) * (|tilt| * probeNorm)) +
      (A * residual k ^ (1 - 2 / (q : ℝ)) + 2 * |tilt| * probeNorm * residual k))
      atTop (𝓝 0) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hexp : 0 < 1 - 2 / (q : ℝ) := by
    apply sub_pos.mpr
    apply (div_lt_one hqpos).mpr
    exact_mod_cast (by omega : 2 < q)
  have hε := tendsto_originalUpperRefinementAccuracy.div_const 10
  have hρ := (hε.const_mul 3).add ((hε.pow 2).const_mul 2)
  have hρzero : Tendsto (fun k ↦ 3 * (originalUpperRefinementAccuracy k / 10) +
      2 * (originalUpperRefinementAccuracy k / 10) ^ 2) atTop (𝓝 0) := by
    simpa using hρ
  have hreszero : Tendsto residual atTop (𝓝 0) :=
    squeeze_zero (fun k ↦ (hres k).1) (fun k ↦ (hres k).2)
      (by simpa using tendsto_originalUpperRefinementAccuracy.const_mul 4)
  have hp := (Real.continuousAt_rpow_const (0 : ℝ) (1 - 2 / (q : ℝ))
    (Or.inr hexp.le)).tendsto.comp hreszero
  have hpower : Tendsto (fun k ↦ residual k ^ (1 - 2 / (q : ℝ))) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.zero_rpow hexp.ne'] using hp
  have hden := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub hρzero
  have hquot : Tendsto (fun k ↦ A / (1 - (3 * (originalUpperRefinementAccuracy k / 10) +
      2 * (originalUpperRefinementAccuracy k / 10) ^ 2))) atTop (𝓝 A) := by
    have hh := (tendsto_const_nhds (x := A)).div hden (by norm_num : (1 : ℝ) - 0 ≠ 0)
    convert hh using 1
    · funext k
      rfl
    · simp
  have hgeom := hρzero.mul ((hquot.add_const (|tilt| * probeNorm)).add_const 1)
  have hprobe := ((tendsto_originalUpperRefinementAccuracy.const_mul 2).const_mul |tilt|).add
    (hρzero.mul_const (|tilt| * probeNorm))
  have herr := (hpower.const_mul A).add (hreszero.const_mul (2 * |tilt| * probeNorm))
  simpa using (hgeom.add hprobe).add herr
/-- The original frozen-cell unit-density pressure packet with its actual geometric
repair constant retained as a parameter. -/
def PopulationLocalPressureCore.originalFixedAtlasUnitDensityPressureData
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ) (f : M × M →ᵇ ℝ) (ε probeError A : ℝ) : Prop :=
    ∃ (N : Fin D.haar.continuous.count → ℕ)
      (refs : ∀ i, Fin (N i) → (D.haar.continuous.coefficient i).roots)
      (cells : ∀ i, Fin (N i) → Set (ℚ → M))
      (_hcells : ∀ i c, MeasurableSet (cells i c)),
      (∀ i c, cells i c ⊆ (D.haar.continuous.coefficient i).roots ∩ U i (refs i c)) ∧
      let Cell := Sigma (fun i ↦ Fin (N i))
      let coreIndex := fun c : Cell ↦ c.1
      let reference := fun c : Cell ↦ refs c.1 c.2
      let cell := fun c : Cell ↦ cells c.1 c.2
      let Qlocal := fun c : Cell ↦ Q c.1 (reference c)
      let P₀ := fun c : Cell ↦ D.originalWindowReferenceWeights γ originalGap I c.1 (reference c) (Qlocal c) retentionError
      let Seed := fun c : Cell ↦ (P (D.haar.continuous.coefficient c.1).seedIndex).seed
      let q := fun c ↦ Module.finrank ℝ (Seed c).covector.ker
      let coord := fun c ↦ atlasSeedCoord (Seed c) (Module.finBasis ℝ (Seed c).covector.ker).equivFunL a
      ∃ (hP₀ : ∀ c j k, 0 ≤ P₀ c j k) (hmass : ∀ c, 0 < ∑ j, ∑ k, P₀ c j k),
      0 ≤ A ∧ ∃ cHaar : Cell → ℝ≥0, (∀ c, 0 < cHaar c) ∧
      (∀ c, (κ (D.haar.continuous.coefficient c.1).seedIndex).map
        (Module.finBasis ℝ (Seed c).covector.ker).equivFunL =
        (cHaar c : ℝ≥0∞) • (volume : Measure (Fin (q c) → ℝ))) ∧
      ∃ unitPressure : Cell → ℝ → ℝ,
        (∀ c,
          let C := D.haar.continuous.coefficient (coreIndex c)
          let _instClass := normalizedClockClassPairMeasure_probability (P₀ c) (hP₀ c) (hmass c)
          let α := (normalizedClockClassPairMeasure (P₀ c)).map Prod.fst
          let β := (normalizedClockClassPairMeasure (P₀ c)).map Prod.snd
          let _instS : IsProbabilityMeasure α := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
          let _instT : IsProbabilityMeasure β := Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
          ∀ tilt, Tendsto (fun L : ℝ ↦ finiteClassLegalScalePressure (q c)
            (C.clockClassAllowed (Qlocal c)) α β
            (C.clockClassKinetic (Qlocal c) (reference c).val)
            (C.clockClassProbe (Qlocal c) (reference c).val (reference c).property f) L tilt)
            atTop (𝓝 (unitPressure c tilt))) ∧
        ∀ tilt : ℝ,
          let iid := fun n ↦ (Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ ν))
          let assignment := fun n (sample : (Fin n → M) × (Fin n → M)) ↦ perturbedAssignmentValue
            (fun i j ↦ (n : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) *
              ((F.lengthEDist (sample.1 i) (sample.2 j)).toReal - u (sample.2 j) + u (sample.1 i)) +
              tilt * f (sample.1 i,sample.2 j)) 0 0
          let geometry := (3 * ε + 2 * ε ^ 2) *
              (A / (1 - (3 * ε + 2 * ε ^ 2)) + |tilt| * ‖f‖ + 1) +
            (|tilt| * (2 * probeError) + (3 * ε + 2 * ε ^ 2) * (|tilt| * ‖f‖))
          let residual := (ENNReal.ofReal (retentionError + splitError + δ.toReal) +
            (μ.map a) D.haar.continuous.population.rootsᶜ).toReal
          (∀ n, 0 < n → Integrable (assignment n) (iid n)) ∧
          ∀ ζ : ℝ, 0 < ζ → ∀ᶠ n in atTop,
            (∫ sample, assignment n sample ∂iid n) / n ≤
              (∑ c,
                let density : ℝ≥0 := cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
                volume.real ((coord c) '' cell c) * (density : ℝ) ^ (1 - 2 / (q c : ℝ)) *
                  unitPressure c (tilt * (density : ℝ) ^ (2 / (q c : ℝ)))) + geometry +
                (A * residual ^ (1 - 2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)) +
                  2 * |tilt| * ‖f‖ * residual) + ζ

/-- The original exact finite-family pressure producer consumes the same rebuilt
population and keeps the fixed atlas constant throughout minimization and the iid limit. -/
theorem PopulationLocalPressureCore.originalFixedAtlasSharpPopulationData_unit_density
    [∀ j, SigmaFinite (κ j)]
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ) (f : M × M →ᵇ ℝ) (ε probeError : ℝ)
    (ha : Measurable a) (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    (hbalance : ν.map a = μ.map a)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure) (hdim : 6 ≤ Module.finrank ℝ E)
    {T : Type (max u₁ u₂)} [Fintype T] (quadC Bnd forwardGap : ℝ)
    (hdata : D.originalFixedAtlasSharpPopulationData γ originalGap Q U retentionError splitError
      f ε probeError ha T quadC Bnd forwardGap) :
    D.originalFixedAtlasUnitDensityPressureData γ originalGap Q U retentionError splitError
      f ε probeError (quadC * dyadicMatchingConstant (Module.finrank ℝ E - 1) *
        (Fintype.card T : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))) := by
  classical
  rcases hdata with ⟨N,refs,cells,Pf,Qf,hcells,
    hsub,hPfM,hQfM,hfields,hweights,hdensity,hdisj,hcover,Qglobal,hQglobal,hwhole,
    ξ,hχfinite,hξfinite,hπ,hcal,hξmass,Cst,hquadEq,hBEq,hfgood,classify,hclassM,hclass,hsharp⟩
  let Cell := Sigma (fun i ↦ Fin (N i))
  let coreIndex := fun c : Cell ↦ c.1
  let reference := fun c : Cell ↦ refs c.1 c.2
  let cell := fun c : Cell ↦ cells c.1 c.2
  let hcell := fun c : Cell ↦ hcells c.1 c.2
  let Qlocal := fun c : Cell ↦ Q c.1 (reference c)
  let P₀ := fun c : Cell ↦ D.originalWindowReferenceWeights γ originalGap I c.1 (reference c) (Qlocal c) retentionError
  letI : MeasurableSpace (Option (Bool × T)) := ⊤
  letI : MeasurableSingletonClass (Option (Bool × T)) := ⟨fun _ ↦ trivial⟩
  let α := fun (c : Cell) j ↦ normalizedActualBinKernel (condDistrib u a μ)
    ((Qlocal c).cell j) ((Qlocal c).measurable_cell j) 0
  let β := fun (c : Cell) k ↦ normalizedActualBinKernel (condDistrib u a ν)
    ((Qlocal c).cell k) ((Qlocal c).measurable_cell k) 0
  let KP := fun c : Cell ↦ finiteClassPopulationKernel (Pf c.1 c.2) (α c) (β c)
  let χ := (((μ.map a) ⊗ₘ finiteCellPairKernel cell hcell KP).map
    sameLabelPopulationPair).map (Prod.map b b)
  letI : IsFiniteMeasure χ := hχfinite
  letI : IsFiniteMeasure ξ := hξfinite
  letI : IsSFiniteKernel Qglobal := hQglobal
  letI (c : Cell) : (κ (D.haar.continuous.coefficient (coreIndex c)).seedIndex).IsAddHaarMeasure := hκ _
  have hP₀ : ∀ c j k, 0 ≤ P₀ c j k := fun c ↦ (hweights c.1 c.2).1
  have hmass : ∀ c, 0 < ∑ j, ∑ k, P₀ c j k := fun c ↦ (hweights c.1 c.2).2.2.2
  have hres (c : Cell) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ j k, 0 ≤ Qf c.1 c.2 z j k := by
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.1
  have hrow (c : Cell) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ j,
      (∑ k, (Pf c.1 c.2 z j k + Qf c.1 c.2 z j k)) = (condDistrib u a μ z).real ((Qlocal c).cell j) := by
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.2.1
  have hcol (c : Cell) : ∀ᵐ z ∂(μ.map a).restrict (cell c), ∀ k,
      (∑ j, (Pf c.1 c.2 z j k + Qf c.1 c.2 z j k)) = (condDistrib u a ν z).real ((Qlocal c).cell k) := by
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.2.2.1
  obtain ⟨cHaar,hcHaar,hmap,limit,hlimit,hupper⟩ := D.exists_original_sharp_family_assignment_pressure_upper
    hF hcomplete hu ha hinj coreIndex cell hcell (fun c z hz ↦ (hsub c.1 c.2 hz).1)
    hdisj Qlocal reference classify hclassM hclass (fun _ _ ↦ 0) (fun _ _ ↦ 0)
    P₀ hP₀ hmass (fun c ↦ (hweights c.1 c.2).2.1)
    (fun c ↦ Pf c.1 c.2) (fun c ↦ Qf c.1 c.2) (fun c ↦ hPfM c.1 c.2)
    (fun c ↦ hdensity c.1 c.2) hres hrow hcol KP (fun _ ↦ rfl) Qglobal hwhole
    hb hμinv hνinv hbalance χ ξ rfl hπ Cst f hdim ε probeError hsharp
  let Seed := fun c : Cell ↦ (P (D.haar.continuous.coefficient c.1).seedIndex).seed
  let q := fun c : Cell ↦ Module.finrank ℝ (Seed c).covector.ker
  let density := fun c : Cell ↦ cHaar c * (clockClassPairMeasure (P₀ c) univ).toNNReal
  have hq (c : Cell) : 4 < q c := by
    have h := D.original_seed_label_finrank c.1
    change q c = Module.finrank ℝ E - 1 at h
    omega
  have hzero (c : Cell) : ∀ j k,
      ¬(D.haar.continuous.coefficient c.1).clockClassAllowed (Qlocal c) j k →
        P₀ c j k = 0 := by
    intro j k hnot
    simp only [P₀, PopulationLocalPressureCore.originalWindowReferenceWeights, maskedClockFlow,
      hnot, ↓reduceIte]
  have hpressure (c : Cell) :=
    (D.haar.continuous.coefficient c.1).exists_clockClassPressure_unit_density
      (Qlocal c) (reference c).val (reference c).property f (P₀ c) (hP₀ c)
      (hzero c) (hmass c) (hq c)
  choose unitPressure hunit hphysical hconc hlip using hpressure
  have hdensity (c : Cell) : 0 < density c := by
    apply mul_pos (hcHaar c)
    apply ENNReal.toNNReal_pos
    · have hr : 0 < (clockClassPairMeasure (P₀ c)).real univ := by
        rw [clockClassPairMeasure_real_univ (P₀ c) (hP₀ c)]
        exact hmass c
      exact ne_of_gt ((ENNReal.toReal_pos_iff.mp hr).1)
    · exact measure_ne_top _ _
  have hident (c : Cell) (tilt : ℝ) :
      limit c tilt = (density c : ℝ) ^ (1 - 2 / (q c : ℝ)) *
        unitPressure c (tilt * (density c : ℝ) ^ (2 / (q c : ℝ))) := by
    apply tendsto_nhds_unique (hlimit c tilt)
    simpa only [ProbabilityMeasure.toMeasure_map, clockClassJointProbability,
      ProbabilityMeasure.coe_mk, density, P₀, Seed, q, Qlocal, reference] using
      hphysical c (density c) (hdensity c) tilt
  let qGlobal := Module.finrank ℝ E - 1
  let A := quadC * dyadicMatchingConstant qGlobal * (Fintype.card T : ℝ) ^ (2 / (qGlobal : ℝ))
  have hqGlobal : 4 < qGlobal := by dsimp only [qGlobal]; omega
  have hquad : 0 ≤ quadC := hquadEq ▸ Cst.quadratic_nonneg
  have hA : 0 ≤ A := mul_nonneg
    (mul_nonneg hquad (dyadicMatchingConstant_pos hqGlobal).le)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  unfold PopulationLocalPressureCore.originalFixedAtlasUnitDensityPressureData
  refine ⟨N, refs, cells, hcells, hsub, hP₀, hmass, hA, cHaar, hcHaar, hmap,
    unitPressure, ?_, ?_⟩
  · intro c
    simpa only [ProbabilityMeasure.toMeasure_map, clockClassJointProbability,
      ProbabilityMeasure.coe_mk, P₀, Seed, q, Qlocal, reference] using hunit c
  · intro tilt
    refine ⟨(hupper tilt).1, ?_⟩
    intro ζ hζ
    filter_upwards [(hupper tilt).2 ζ hζ] with n hn
    let residual := (ENNReal.ofReal (retentionError + splitError + δ.toReal) +
      (μ.map a) D.haar.continuous.population.rootsᶜ).toReal
    have hξreal : (ξ univ).toReal ≤ residual := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, measure_ne_top _ _⟩) hξmass
    have hexp : 0 ≤ 1 - 2 / (qGlobal : ℝ) := by
      have hqR : (2 : ℝ) ≤ qGlobal := by exact_mod_cast (by omega : 2 ≤ qGlobal)
      have hqpos : (0 : ℝ) < qGlobal := by exact_mod_cast (by omega : 0 < qGlobal)
      exact sub_nonneg.mpr ((div_le_one hqpos).mpr hqR)
    have hrepair : A * (ξ univ).toReal ^ (1 - 2 / (qGlobal : ℝ)) +
        2 * |tilt| * ‖f‖ * (ξ univ).toReal ≤
        A * residual ^ (1 - 2 / (qGlobal : ℝ)) + 2 * |tilt| * ‖f‖ * residual :=
      add_le_add (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow ENNReal.toReal_nonneg hξreal hexp) hA)
        (mul_le_mul_of_nonneg_left hξreal (by positivity))
    simp only [hquadEq] at hn
    have hh := hn.trans (add_le_add (add_le_add (le_refl _) hrepair) (le_refl ζ))
    simpa only [hident, A, qGlobal, density, P₀, Seed, q, Qlocal, coreIndex, reference,
      cell, residual, mul_assoc] using hh

/-- The actual original conditional clocks and screened cores are produced at every
explicit accuracy using one fixed geometric atlas. The original full iid sharp comparison
is retained, and its entire deterministic geometry, probe and residual error tends to zero.
At each fixed refinement the empirical limit is taken first. -/
theorem exists_original_uniform_refined_sharp_upper
    [∀ j, SigmaFinite (κ j)]
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hνreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμinv : ∀ᵐ x ∂μ, b (a x,u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y,u y) = y)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ y ∂ν, y ∈ B)
    (πOriginal : Measure (M × M)) (hπOriginal : Vlasov.IsCoupling πOriginal μ ν)
    (hcalOriginal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂πOriginal, u p.2 - u p.1 = dist p.1 p.2)
    (f : M × M →ᵇ ℝ) (hq : 4 < Module.finrank ℝ E - 1) :
    ∃ (I : Set ℝ), IsCompact I ∧ ∃ originalGap : ℝ, 0 < originalGap ∧
    ∃ γ : Kernel (ℚ → M) (ℝ × ℝ), IsMarkovKernel γ ∧
    ∃ (T : Type (max u₁ u₂)) (hT : Fintype T) (quadC Bnd forwardGap : ℝ),
      let _inst : Fintype T := hT
      0 ≤ quadC ∧ 0 ≤ Bnd ∧ 0 < forwardGap ∧
      ∃ D : ∀ k, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
        (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r
        (ENNReal.ofReal (originalUpperRefinementAccuracy k))
        (ENNReal.ofReal (originalUpperRefinementAccuracy k)),
      ∃ (Q : ∀ k, ∀ i : Fin (D k).haar.continuous.count,
        ((D k).haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
        (U : ∀ k, ∀ i : Fin (D k).haar.continuous.count,
        ((D k).haar.continuous.coefficient i).roots → Set (ℚ → M)),
        (∀ k, (D k).originalFixedAtlasSharpPopulationData γ originalGap (Q k) (U k)
          (originalUpperRefinementAccuracy k) (originalUpperRefinementAccuracy k) f
          (originalUpperRefinementAccuracy k / 10) (originalUpperRefinementAccuracy k)
          ha T quadC Bnd forwardGap) ∧
        (∀ k, (D k).originalFixedAtlasUnitDensityPressureData γ originalGap (Q k) (U k)
          (originalUpperRefinementAccuracy k) (originalUpperRefinementAccuracy k) f
          (originalUpperRefinementAccuracy k / 10) (originalUpperRefinementAccuracy k)
          (quadC * dyadicMatchingConstant (Module.finrank ℝ E - 1) *
            (Fintype.card T : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)))) ∧
        let residual := fun k ↦
          (ENNReal.ofReal (originalUpperRefinementAccuracy k + originalUpperRefinementAccuracy k +
            (ENNReal.ofReal (originalUpperRefinementAccuracy k)).toReal) +
            (μ.map a) (D k).haar.continuous.population.rootsᶜ).toReal
        let A := quadC * dyadicMatchingConstant (Module.finrank ℝ E - 1) *
          (Fintype.card T : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ))
        (∀ k, 0 ≤ residual k ∧ residual k ≤ 4 * originalUpperRefinementAccuracy k) ∧
        ∀ tilt : ℝ, Tendsto (fun k ↦ originalUniformUpperError (Module.finrank ℝ E - 1)
          A tilt ‖f‖ (originalUpperRefinementAccuracy k / 10)
          (originalUpperRefinementAccuracy k) (residual k)) atTop (𝓝 0) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  letI : BorelSpace (ℚ → M) := inferInstance
  have hum : Measurable u := hu.continuous.measurable
  obtain ⟨gap,hgap,hsep⟩ := exists_original_support_gap hA hB hAB
  let I := (u '' A) ∪ (u '' B)
  have hI : IsCompact I := (hA.image hu.continuous).union (hB.image hu.continuous)
  have hμI : ∀ᵐ x ∂μ, u x ∈ I := hμA.mono fun x hx ↦ Or.inl (mem_image_of_mem u hx)
  have hνI : ∀ᵐ y ∂ν, u y ∈ I := hνB.mono fun y hy ↦ Or.inr (mem_image_of_mem u hy)
  have hlabels := original_calibrated_coupling_labels μ ν πOriginal πOriginal
    hπOriginal le_rfl a u horder hμreg hνreg hcalOriginal
  have hπA : ∀ᵐ p ∂πOriginal, p.1 ∈ A :=
    ae_of_ae_map measurable_fst.aemeasurable (hπOriginal.1.symm ▸ hμA)
  have hπB : ∀ᵐ p ∂πOriginal, p.2 ∈ B :=
    ae_of_ae_map measurable_snd.aemeasurable (hπOriginal.2.symm ▸ hνB)
  have hgapClock : ∀ᵐ p ∂πOriginal, gap ≤ u p.2 - u p.1 := by
    filter_upwards [hπA,hπB,hcalOriginal] with p hpA hpB hpCal
    rw [hpCal]
    exact hsep p.1 hpA p.2 hpB
  obtain ⟨γ,hγ,hGood⟩ := exists_original_clockPair_kernel_with_range μ ν πOriginal
    hπOriginal a u ha hum (hlabels.mono fun _ h ↦ h.1) gap hgapClock I hI.measurableSet hμI hνI
  letI : IsMarkovKernel γ := hγ
  obtain ⟨T, hT, quadC, Bnd, forwardGap, hquadC, hBnd, hfgap, hfactory⟩ :=
    exists_uniform_original_sharp_population_factory γ gap hF hcomplete hu ha hinj horder
      hb hμreg hνreg hμinv hνinv hA hB hAB hμA hνB πOriginal hπOriginal hcalOriginal
      hI hgap hq
  let _instT : Fintype T := hT
  obtain ⟨_, _, hbalance, _, _, _⟩ := exists_original_clockPair_kernel μ ν πOriginal
    hπOriginal a u ha hum (hlabels.mono fun _ h ↦ h.1) 0
      (hlabels.mono fun _ h ↦ sub_nonneg.mpr h.2)
  have hrecovery := populationLabelCoreRecoveryLaw_of_inverse μ ν ha hum hb
    (lambda := μ.map a) rfl hbalance.symm hμinv hνinv
  have hstep (k : ℕ) :
      ∃ D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
        (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap I) r
        (ENNReal.ofReal (originalUpperRefinementAccuracy k))
        (ENNReal.ofReal (originalUpperRefinementAccuracy k)),
      ∃ (Q : ∀ i : Fin D.haar.continuous.count,
        (D.haar.continuous.coefficient i).roots → FiniteScalarBins I gap)
        (U : ∀ i : Fin D.haar.continuous.count,
        (D.haar.continuous.coefficient i).roots → Set (ℚ → M)),
      D.originalFixedAtlasSharpPopulationData γ gap Q U
        (originalUpperRefinementAccuracy k) (originalUpperRefinementAccuracy k) f
        (originalUpperRefinementAccuracy k / 10) (originalUpperRefinementAccuracy k)
        ha T quadC Bnd forwardGap := by
    obtain ⟨hτ, hτ1⟩ := originalUpperRefinementAccuracy_pos_lt_one k
    obtain ⟨hε, hρ, hsmall⟩ := originalUpperRefinementGeometry_small k
    obtain ⟨D, hscreen⟩ := hcore.exists_local_core_small_clock_screen
      (δ := ENNReal.ofReal (originalUpperRefinementAccuracy k))
      (loss := ENNReal.ofReal (originalUpperRefinementAccuracy k))
      hrecovery hF hcomplete hu ha hinj hκ hGood (half_pos hgap)
      (ENNReal.ofReal_pos.mpr hτ).ne' (ENNReal.ofReal_pos.mpr hτ).ne'
    have hgeometry (i : Fin D.haar.continuous.count) :=
      D.exists_full_original_clockClass_geometry_with_forward_region hF hcomplete hu ha hinj
        i (⇑f) f.continuous hgap hsep (hscreen i) hI hgap hε hτ
    choose Q U hU houter hregion hgeometry using hgeometry
    refine ⟨D, Q, U, ?_⟩
    exact hfactory _ _ D Q U (fun i ref ↦ (hU i ref).1)
      (fun i ref ↦ (hU i ref).2) houter hregion ENNReal.ofReal_ne_top
      (by simpa only [ENNReal.toReal_ofReal hτ.le] using hτ1)
      _ _ hτ hτ1 hτ f (ε := originalUpperRefinementAccuracy k / 10)
      (probeError := originalUpperRefinementAccuracy k) hρ hτ.le hgeometry hsmall
  choose D Q U hdata using hstep
  have hpressure (k : ℕ) :=
    (D k).originalFixedAtlasSharpPopulationData_unit_density γ gap (Q k) (U k)
      (originalUpperRefinementAccuracy k) (originalUpperRefinementAccuracy k) f
      (originalUpperRefinementAccuracy k / 10) (originalUpperRefinementAccuracy k)
      ha hF hcomplete hu hinj hb hμinv hνinv
      (map_label_eq_of_coupling hπOriginal ha ha (hlabels.mono fun _ h ↦ h.1)).symm
      hκ (by omega) quadC Bnd forwardGap (hdata k)
  refine ⟨I, hI, gap, hgap, γ, hγ, T, hT, quadC, Bnd, forwardGap,
    hquadC, hBnd, hfgap, D, Q, U, hdata, hpressure, ?_⟩
  dsimp only
  let residual := fun k ↦
    (ENNReal.ofReal (originalUpperRefinementAccuracy k + originalUpperRefinementAccuracy k +
      (ENNReal.ofReal (originalUpperRefinementAccuracy k)).toReal) +
      (μ.map a) (D k).haar.continuous.population.rootsᶜ).toReal
  have hbound (k : ℕ) : 0 ≤ residual k ∧ residual k ≤ 4 * originalUpperRefinementAccuracy k := by
    obtain ⟨hτ, _⟩ := originalUpperRefinementAccuracy_pos_lt_one k
    refine ⟨ENNReal.toReal_nonneg, ?_⟩
    have hb := (D k).original_upper_residual_mass_le (originalUpperRefinementAccuracy k)
      (originalUpperRefinementAccuracy k) hτ.le hτ.le ENNReal.ofReal_ne_top
    calc
      residual k ≤ _ := hb
      _ = 4 * originalUpperRefinementAccuracy k := by
        rw [ENNReal.toReal_ofReal hτ.le]
        ring
  refine ⟨hbound, fun tilt ↦ ?_⟩
  simpa only [originalUniformUpperError] using
    tendsto_original_uniform_upper_errors (Module.finrank ℝ E - 1) hq
      (quadC * dyadicMatchingConstant (Module.finrank ℝ E - 1) *
        (Fintype.card T : ℝ) ^ (2 / ((Module.finrank ℝ E - 1 : ℕ) : ℝ)))
      tilt ‖f‖ residual hbound

end OTSelector.Reconstruction
