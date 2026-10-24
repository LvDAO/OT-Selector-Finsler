import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedFamilyMean
import OTSelector.Reconstruction.FinslerRelativeLawOriginalPhysicalSharpExpectedUpper

/-! The original sharp population factory also produces all paired-cell means. -/
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

/-- A fixed original population has the literal global paired-cell mean
identity for every deterministic retained set, sample size and tilt. -/
def PopulationLocalPressureCore.originalWeightPairedMeans
    {Good : (ℚ → M) → Prop}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    {Cell T : Type*} [Fintype Cell] [Fintype T] {I : Set ℝ} {gap : ℝ}
    (coreIndex : Cell → Fin D.haar.continuous.count)
    (Q : Cell → FiniteScalarBins I gap)
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (classify : ∀ c, ℝ → Fin (Q c).count) (cell : Cell → Set (ℚ → M))
    (_hcell : ∀ c, MeasurableSet (cell c)) (f : M × M →ᵇ ℝ)
    (P₀ : ∀ c, Fin (Q c).count → Fin (Q c).count → ℝ)
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {q : ℕ} {cost : M → M → ℝ} (Cst : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (ha : Measurable a)
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))] : Prop :=
  ∀ (G : Set (ℚ → M)) (hG : MeasurableSet G) (N : ℕ) (tilt : ℝ),
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let oldLaw := (Cst.refineSubplan η hη).markedLaw N
    let original := D.originalClockClassOldModelValue (q := q) (n := N)
      coreIndex Q reference classify cell f tilt (T := T)
    let law := fun c ↦ D.originalPairedClockClassLaw (coreIndex c) (Q c) (P₀ c) (cell c) G N
    let value := fun c ↦ D.originalPairedClockClassValue (coreIndex c) (Q c) (reference c) f N
      ((N : ℝ) ^ (2 / (q : ℝ))) tilt
    (∀ c, IsProbabilityMeasure (D.originalPairedClockClassSpatialLaw (coreIndex c) (Q c) (P₀ c) (cell c) G) ∧
      (∀ᵐ o ∂D.originalPairedClockClassSpatialLaw (coreIndex c) (Q c) (P₀ c) (cell c) G,
        ∀ w, o = some w → w ∈ populationSeedRootLabelValue
          (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed a ''
            (D.haar.continuous.coefficient (coreIndex c)).roots)) ∧
    Integrable original oldLaw ∧ (∀ c, Integrable (value c) (law c)) ∧
      (∫ sample, original sample ∂oldLaw) = ∑ c, ∫ sample, value c sample ∂law c

/-- The original sharp population packet keeps the same witnesses and adds
its fully produced paired-cell law identities. -/
def PopulationLocalPressureCore.originalWeightSharpPairedPopulationData
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
      D.originalWeightSharpExpectedBound coreIndex Q reference classify cell hcell f ε probeError χ ξ Cst ha ∧
      D.originalWeightPairedMeans coreIndex Q reference classify cell hcell f
        (fun c ↦ D.originalWindowReferenceWeights γ originalGap I c.1 (reference c) (Q c) retentionError)
        χ ξ Cst ha

/-- The fixed population metadata already supplied by the original sharp
factory discharges every paired-law input, without changing its plan or classifier. -/
theorem PopulationLocalPressureCore.originalWeightSharpPopulationData_paired_means
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
    (hdata : D.originalWeightSharpPopulationData γ originalGap Q U retentionError splitError f ε probeError ha) :
    D.originalWeightSharpPairedPopulationData γ originalGap Q U retentionError splitError f ε probeError ha := by
  classical
  rcases hdata with ⟨T,hT,quadC,Bnd,forwardGap,hquad,hB,hfg,N,refs,cells,Pf,Qf,hcells,
    hsub,hPfM,hQfM,hfields,hweights,hdensity,hdisj,hcover,Qglobal,hQglobal,hwhole,
    ξ,hχfinite,hξfinite,hπ,hcal,hξmass,Cst,hquadEq,hBEq,hfgood,classify,hclassM,hclass,hsharp⟩
  letI : Fintype T := hT
  let C := Sigma (fun i ↦ Fin (N i))
  let coreIndex := fun c : C ↦ c.1
  let reference := fun c : C ↦ refs c.1 c.2
  let cell := fun c : C ↦ cells c.1 c.2
  let hcell := fun c : C ↦ hcells c.1 c.2
  let Qlocal := fun c : C ↦ Q c.1 (reference c)
  letI : MeasurableSpace (Option (Bool × T)) := ⊤
  letI : MeasurableSingletonClass (Option (Bool × T)) := ⟨fun _ ↦ trivial⟩
  let α := fun (c : C) j ↦ normalizedActualBinKernel (condDistrib u a μ)
    ((Qlocal c).cell j) ((Qlocal c).measurable_cell j) 0
  let β := fun (c : C) k ↦ normalizedActualBinKernel (condDistrib u a ν)
    ((Qlocal c).cell k) ((Qlocal c).measurable_cell k) 0
  let KP := fun c : C ↦ finiteClassPopulationKernel (Pf c.1 c.2) (α c) (β c)
  let χ := (((μ.map a) ⊗ₘ finiteCellPairKernel cell hcell KP).map
    sameLabelPopulationPair).map (Prod.map b b)
  letI : IsFiniteMeasure χ := hχfinite
  letI : IsFiniteMeasure ξ := hξfinite
  letI : IsSFiniteKernel Qglobal := hQglobal
  refine ⟨T,hT,quadC,Bnd,forwardGap,hquad,hB,hfg,N,refs,cells,Pf,Qf,hcells,
    hsub,hPfM,hQfM,hfields,hweights,hdensity,hdisj,hcover,Qglobal,hQglobal,hwhole,
    ξ,hχfinite,hξfinite,hπ,hcal,hξmass,Cst,hquadEq,hBEq,hfgood,classify,hclassM,hclass,hsharp,?_⟩
  intro G hG n tilt
  refine D.actual_original_paired_family_mean_of_classifier hF hcomplete hu ha hinj
    coreIndex Qlocal reference cell hcell hdisj
    (fun c z hz ↦ (hsub c.1 c.2 hz).1) classify hclassM hclass
    (fun _ _ ↦ 0) (fun _ _ ↦ 0)
    (fun c ↦ D.originalWindowReferenceWeights γ originalGap I c.1 (reference c) (Qlocal c) retentionError)
    (fun c ↦ (hweights c.1 c.2).1) (fun c ↦ (hweights c.1 c.2).2.2.2)
    (fun c ↦ Pf c.1 c.2) (fun c ↦ Qf c.1 c.2) (fun c ↦ hPfM c.1 c.2)
    (fun c ↦ hdensity c.1 c.2) ?_ ?_ ?_ KP (fun _ ↦ rfl) Qglobal hwhole
    hb hμinv hνinv rfl hbalance (χ + ξ) ξ hπ rfl Cst hG f n tilt
  · intro c
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.1
  · intro c
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.2.1
  · intro c
    filter_upwards [ae_restrict_mem (hcell c)] with z hz
    exact (hfields c.1 c.2 z hz).2.2.2.1

end OTSelector.Reconstruction
