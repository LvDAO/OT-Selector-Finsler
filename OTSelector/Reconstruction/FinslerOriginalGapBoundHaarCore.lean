import OTSelector.Reconstruction.FinslerOriginalGapBoundContinuousCore
import OTSelector.Reconstruction.FinslerPopulationHaarPressureCore

/-! Actual moment and Haar intensity refinement preserves the rational-window
gap certificate already produced from the original separated populations. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Internal compact refinement supplies positive continuous original intensities
and uniform inverse-moment bounds while keeping exact original physical recovery. -/
theorem PopulationFinitePressureCoreLaw.exists_haar_core_with_original_gap
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    (hcore : PopulationFinitePressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hmoments : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instHaarCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam)
    (r : ℝ) (Good : (ℚ → M) → Prop) (hGood : ∀ᵐ z ∂lambda, Good z)
    (δ : ℝ≥0∞) (hδ : δ ≠ 0) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε,
      ∀ i, (D.continuous.coefficient i).roots.Nonempty →
        ((D.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap := by
  let _instHaarCoreMetric : MetricSpace M := F.metricSpace
  let _instHaarCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instHaarCorePolish : PolishSpace M := inferInstance
  let _instHaarCoreBorel : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨D,hgapD⟩ := hcore.exists_continuous_core_with_original_gap hrecovery hmoments hcover
    hF hcomplete hu ha hinj hgap hsep Good hGood δ hδ (ε / 2) (ENNReal.half_pos hε).ne'
  obtain ⟨τ, hτ, hsum⟩ := ENNReal.exists_pos_sum_of_countable'
    (ENNReal.half_pos hε).ne' (Fin D.count)
  choose J hJloss using fun i ↦ (D.coefficient i).exists_uniformMomentCore
    hF hcomplete hu ha hinj r (ENNReal.half_pos (hτ i).ne').ne'
  let I (i : Fin D.count) : PopulationSeedIntensityCore P a κ lambda
      (D.coefficient i).seedIndex (J i).roots (τ i / 2) :=
    Classical.choice (exists_populationSeedIntensityCore P a κ lambda
      hF hcomplete hu ha hinj (D.coefficient i).seedIndex (J i).compact.measurableSet
        ((J i).subset.trans (D.coefficient i).roots_subset_piece)
        (ENNReal.half_pos (hτ i).ne').ne')
  let C : Fin D.count → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ :=
    fun i ↦ (D.coefficient i).restrictRoots (I i).compact
      ((I i).roots_subset.trans (J i).subset)
  have hloss (i : Fin D.count) : lambda ((D.coefficient i).roots \ (I i).roots) < τ i := by
    have hsub : (D.coefficient i).roots \ (I i).roots ⊆
        ((D.coefficient i).roots \ (J i).roots) ∪ ((J i).roots \ (I i).roots) := by
      intro z hz
      by_cases h : z ∈ (J i).roots
      · exact Or.inr ⟨h, hz.2⟩
      · exact Or.inl ⟨hz.1, h⟩
    exact ((measure_mono hsub).trans (measure_union_le _ _)).trans_lt
      (by simpa only [ENNReal.add_halves] using
        ENNReal.add_lt_add (hJloss i) (I i).small_loss)
  have hsub : (⋃ i, (C i).roots) ⊆ D.population.roots := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    rw [← D.union_eq]
    exact mem_iUnion.mpr ⟨i, (J i).subset ((I i).roots_subset hi)⟩
  have hdiff : D.population.roots \ (⋃ i, (C i).roots) ⊆
      ⋃ i, (D.coefficient i).roots \ (I i).roots := by
    rintro z ⟨hz, hnot⟩
    rw [← D.union_eq] at hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨i, hi, fun h ↦ hnot (mem_iUnion.mpr ⟨i, h⟩)⟩
  have hlossTotal : lambda (D.population.roots \ (⋃ i, (C i).roots)) < ε / 2 :=
    ((measure_mono hdiff).trans (measure_iUnion_le _)).trans_lt
      ((ENNReal.tsum_le_tsum fun i ↦ (hloss i).le).trans_lt hsum)
  have hsmall : lambda (⋃ i, (C i).roots)ᶜ < ε := by
    have hcover : (⋃ i, (C i).roots)ᶜ ⊆
        D.population.rootsᶜ ∪ (D.population.roots \ (⋃ i, (C i).roots)) := by
      intro z hz
      by_cases h : z ∈ D.population.roots
      · exact Or.inr ⟨h, hz⟩
      · exact Or.inl h
    exact ((measure_mono hcover).trans (measure_union_le _ _)).trans_lt
      (by simpa only [ENNReal.add_halves] using
        ENNReal.add_lt_add D.population.complement_small hlossTotal)
  have hcompact : IsCompact (⋃ i, (C i).roots) :=
    isCompact_iUnion (fun i ↦ (I i).compact)
  have hdisjoint : Pairwise (fun i j ↦ Disjoint (C i).roots (C j).roots) :=
    fun i j hij ↦ (D.disjoint hij).mono
      ((I i).roots_subset.trans (J i).subset) ((I j).roots_subset.trans (J j).subset)
  refine ⟨{
    continuous := {
      population := D.population.refine hrecovery hcomplete ha hu.continuous.measurable
        hcompact hsub hsmall
      count := D.count
      coefficient := C
      disjoint := hdisjoint
      union_eq := rfl
      recovery := hrecovery.finite_recovery ha hu.continuous.measurable _
        (fun i ↦ (I i).compact.measurableSet) hdisjoint }
    intensity := fun i ↦ (I i).onOwnRoots
    intensity_roots := fun _ ↦ rfl
    moment := fun i ↦ {
      roots := (I i).roots
      subset := Subset.rfl
      compact := (I i).compact
      bound := (J i).bound
      bound_nonneg := (J i).bound_nonneg
      envelope_le := fun z hz ↦ (J i).envelope_le z ((I i).roots_subset hz) }
    moment_roots := fun _ ↦ rfl },?_⟩
  intro i hnonempty
  exact hgapD i (hnonempty.mono ((I i).roots_subset.trans (J i).subset))

end OTSelector.Reconstruction
