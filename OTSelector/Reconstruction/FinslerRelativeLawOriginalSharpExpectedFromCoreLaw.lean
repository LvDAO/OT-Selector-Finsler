import OTSelector.Reconstruction.FinslerRelativeLawOriginalDependentWeightSharpUpper
import OTSelector.Reconstruction.FinslerConcreteUpperClassForwardGeometry
import OTSelector.Reconstruction.FinslerPhysicalSceneClockScreenLocal
import OTSelector.Transport.Calibration.CompactClockGap
import OTSelector.Reconstruction.FinslerRelativeLawWindowReferenceWeightPopulation
import OTSelector.Reconstruction.FinslerConcreteUpperUniformTypedForward
import OTSelector.Reconstruction.FinslerConcreteUpperClassObservation

/-! One original dependent weight population gives the full canonical model upper bound. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
universe u₁ u₂
namespace OTSelector.Reconstruction
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

/-- The complete original sampling population and canonical expected upper
packet; every random variable reads the same internally rebuilt physical plan. -/
def PopulationLocalPressureCore.originalWeightSharpPopulationData
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) (originalGap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss)
    (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
    (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (retentionError splitError : ℝ) (f : M × M →ᵇ ℝ) (ε probeError : ℝ)
    (ha : Measurable a) : Prop :=
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
      D.originalWeightSharpExpectedBound coreIndex Q reference classify cell hcell f ε probeError χ ξ Cst ha

/-- Original Haar recovery and the actual original conditional clock law
produce the small-screen core and all clock-class geometry internally, before
constructing one whole original-marginal empirical upper competitor. -/
theorem exists_original_clockClass_sharp_expected_upper
    [∀ j, SigmaFinite (κ j)]
    {I : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (originalGap : ℝ)
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hGood : ∀ᵐ z ∂μ.map a,
      originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I z)
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
    (hI : IsCompact I) (hgapOriginal : 0 < originalGap)
    (hδne : δ ≠ 0) (hlossne : loss ≠ 0) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1)
    (retentionError splitError : ℝ) (hretention : 0 < retentionError)
    (hretention1 : retentionError < 1) (hsplitError : 0 < splitError)
    (f : M × M →ᵇ ℝ) {ε probeError : ℝ} (hε : 0 < ε) (hprobe : 0 < probeError)
    (hsmall : 3 * ε + 2 * ε ^ 2 < 1) (hq : 4 < Module.finrank ℝ E - 1) :
    ∃ D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) originalGap I) r δ loss,
    ∃ (Q : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → FiniteScalarBins I originalGap)
      (U : ∀ i : Fin D.haar.continuous.count,
      (D.haar.continuous.coefficient i).roots → Set (ℚ → M)),
      D.originalWeightSharpPopulationData γ originalGap Q U retentionError splitError f ε probeError ha := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  letI : BorelSpace (ℚ → M) := inferInstance
  have hum : Measurable u := hu.continuous.measurable
  have hlabelForward := original_calibrated_coupling_labels μ ν πOriginal πOriginal
    hπOriginal le_rfl a u horder hμreg hνreg hcalOriginal
  obtain ⟨_,_,hbalance,_,_,_⟩ := exists_original_clockPair_kernel μ ν πOriginal
    hπOriginal a u ha hum (hlabelForward.mono fun _ h ↦ h.1) 0
      (hlabelForward.mono fun _ h ↦ sub_nonneg.mpr h.2)
  have hrecovery := populationLabelCoreRecoveryLaw_of_inverse μ ν ha hum hb
    (lambda := μ.map a) rfl hbalance.symm hμinv hνinv
  obtain ⟨gap,hgap,hsep⟩ := exists_original_support_gap hA hB hAB
  obtain ⟨D,hscreen⟩ := hcore.exists_local_core_small_clock_screen hrecovery hF hcomplete
    hu ha hinj hκ hGood (half_pos hgap) hδne hlossne
  have hgeometry (i : Fin D.haar.continuous.count) :=
    D.exists_full_original_clockClass_geometry_with_forward_region hF hcomplete hu ha hinj
      i (⇑f) f.continuous hgap hsep (hscreen i) hI hgapOriginal hε hprobe
  choose Q U hU houter hregion hgeometry using hgeometry
  refine ⟨D,Q,U,?_⟩
  exact exists_original_dependent_weight_population_sharp_expected_upper γ originalGap D
    hF hcomplete hu ha hinj horder hb hμreg hνreg hμinv hνinv hA hB hAB hμA hνB
    πOriginal hπOriginal hcalOriginal hI hgapOriginal Q U (fun i ref ↦ (hU i ref).1)
    (fun i ref ↦ (hU i ref).2) houter hregion hδ hδ1 retentionError splitError
    hretention hretention1 hsplitError f (by positivity) hprobe.le hgeometry hq hsmall

end OTSelector.Reconstruction
