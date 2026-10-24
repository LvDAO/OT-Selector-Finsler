import OTSelector.Reconstruction.FinslerPopulationContinuousPressureCore
import OTSelector.Reconstruction.FinslerPopulationSeedIntensityLaw
import OTSelector.Reconstruction.FinslerRootMomentCore

/-!
# Finite original population cores for local Haar pressure

The finite actual coefficient cores are refined simultaneously to continuous
positive Haar intensities and common original inverse-moment bounds. The same
original conditional kernels and exact finite physical recovery are retained.
-/

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

/-- Finite original population cores carrying the exact Haar intensity and a
uniform inverse-moment envelope on each actual coefficient piece. -/
structure PopulationHaarPressureCore (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ)
    (b : (ℚ → M) × ℝ → M) (Good : (ℚ → M) → Prop) (r : ℝ) (δ ε : ℝ≥0∞) where
  continuous : PopulationContinuousPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good δ ε
  intensity : ∀ i : Fin continuous.count,
    PopulationSeedIntensityCore P a κ lambda (continuous.coefficient i).seedIndex
      (continuous.coefficient i).roots 1
  intensity_roots : ∀ i, (intensity i).roots = (continuous.coefficient i).roots
  moment : ∀ i : Fin continuous.count, (continuous.coefficient i).UniformMomentCore r
  moment_roots : ∀ i, (moment i).roots = (continuous.coefficient i).roots

/-- The original laws admit finite local Haar pressure cores at every desired
accuracy, retaining arbitrary original almost-everywhere properties. -/
def PopulationHaarPressureCoreLaw (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ)
    (b : (ℚ → M) × ℝ → M) (r : ℝ) : Prop :=
  ∀ (Good : (ℚ → M) → Prop), (∀ᵐ z ∂lambda, Good z) →
    ∀ δ : ℝ≥0∞, δ ≠ 0 → ∀ ε : ℝ≥0∞, ε ≠ 0 →
      Nonempty (PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)

/-- Internal compact refinement supplies positive continuous original intensities
and uniform inverse-moment bounds while keeping exact original physical recovery. -/
theorem PopulationContinuousPressureCoreLaw.haar_core
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    (hcore : PopulationContinuousPressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instHaarCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (r : ℝ) : PopulationHaarPressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b r := by
  let _instHaarCoreMetric : MetricSpace M := F.metricSpace
  let _instHaarCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instHaarCorePolish : PolishSpace M := inferInstance
  let _instHaarCoreBorel : BorelSpace (ℚ → M) := inferInstance
  intro Good hGood δ hδ ε hε
  obtain ⟨D⟩ := hcore Good hGood δ hδ (ε / 2) (ENNReal.half_pos hε).ne'
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
    moment_roots := fun _ ↦ rfl }⟩

/-- Further compact restrictions keep the same seed/window coefficients, original
intensities and uniform moment bounds, together with exact physical recovery. -/
def PopulationHaarPressureCore.refine
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda] {η₀ η₁ : Measure M}
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε ε' : ℝ≥0∞}
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (ha : Measurable a) (hu : Measurable u)
    {K : Fin D.continuous.count → Set (ℚ → M)}
    (hK : ∀ i, IsCompact (K i))
    (hsub : ∀ i, K i ⊆ (D.continuous.coefficient i).roots)
    (hsmall : lambda (⋃ i, K i)ᶜ < ε') :
    PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε' := by
  let _instHaarRefineMetric : MetricSpace M := F.metricSpace
  let _instHaarRefineProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instHaarRefinePolish : PolishSpace M := inferInstance
  let _instHaarRefineBorel : BorelSpace (ℚ → M) := inferInstance
  have hpop : (⋃ i, K i) ⊆ D.continuous.population.roots := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    exact D.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, hsub i hi⟩
  have hd : Pairwise (fun i j ↦ Disjoint (K i) (K j)) :=
    fun i j hij ↦ (D.continuous.disjoint hij).mono (hsub i) (hsub j)
  exact {
    continuous := {
      population := D.continuous.population.refine hrecovery hcomplete ha hu
        (isCompact_iUnion hK) hpop hsmall
      count := D.continuous.count
      coefficient := fun i ↦ (D.continuous.coefficient i).restrictRoots (hK i) (hsub i)
      disjoint := hd
      union_eq := rfl
      recovery := hrecovery.finite_recovery ha hu K (fun i ↦ (hK i).measurableSet) hd }
    intensity := fun i ↦ (D.intensity i).restrictRoots (hK i)
      (by rw [D.intensity_roots]; exact hsub i)
    intensity_roots := fun _ ↦ rfl
    moment := fun i ↦ {
      roots := K i
      subset := Subset.rfl
      compact := hK i
      bound := (D.moment i).bound
      bound_nonneg := (D.moment i).bound_nonneg
      envelope_le := fun z hz ↦ (D.moment i).envelope_le z
        (by rw [D.moment_roots]; exact hsub i hz) }
    moment_roots := fun _ ↦ rfl }

/-- Both original colors have exactly the same retained Haar base intensity and
their own unchanged original conditional clock kernels on each finite piece. -/
theorem PopulationHaarPressureCore.joint_laws
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instHaarJointMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    let intensity := ((κ C.seedIndex).restrict (R '' C.roots)).withDensity
      (populationSeedPieceHaarDensity P a κ lambda C.seedIndex)
    (η₀.restrict (a ⁻¹' C.roots)).map (fun x ↦ (R (a x), u x)) =
        intensity ⊗ₘ populationSeedCoordinateClockKernel (P C.seedIndex).seed a ha
          (condDistrib u a η₀) ∧
      (η₁.restrict (a ⁻¹' C.roots)).map (fun x ↦ (R (a x), u x)) =
        intensity ⊗ₘ populationSeedCoordinateClockKernel (P C.seedIndex).seed a ha
          (condDistrib u a η₁) := by
  let _instHaarJointMetric : MetricSpace M := F.metricSpace
  let _instHaarJointProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instHaarJointPolish : PolishSpace M := inferInstance
  let _instHaarJointBorel : BorelSpace (ℚ → M) := inferInstance
  exact ⟨original_seed_core_joint_eq_compProd_of_joint P a κ lambda hF hcomplete hu ha hinj
      η₀ (D.continuous.coefficient i).seedIndex (D.continuous.recovery.measurable i)
        (D.continuous.coefficient i).roots_subset_piece (D.continuous.recovery.source_joint i),
    original_seed_core_joint_eq_compProd_of_joint P a κ lambda hF hcomplete hu ha hinj
      η₁ (D.continuous.coefficient i).seedIndex (D.continuous.recovery.measurable i)
        (D.continuous.coefficient i).roots_subset_piece (D.continuous.recovery.target_joint i)⟩

end OTSelector.Reconstruction
