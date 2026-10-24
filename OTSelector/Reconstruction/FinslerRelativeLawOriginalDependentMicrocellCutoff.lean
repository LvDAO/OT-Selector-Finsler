import OTSelector.Reconstruction.FinslerRelativeLawOriginalFixedMicrocellShapeExpectation
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellwiseCutoff

/-! Dependent original seed-coordinate microboxes define one retained-label set. -/
open Set Function MeasureTheory ProbabilityTheory BoxIntegral Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- One deterministic label set joins the prescribed microboxes of all fixed
reference cells, in their own original seed coordinate maps. -/
def PopulationLocalPressureCore.originalClockClassMicrocellLabels
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    {C : Type*} (coreIndex : C → Fin D.haar.continuous.count)
    (cell : C → Set (ℚ → M)) (order : C → ℕ) [∀ c, NeZero (order c)]
    (indices : ∀ c, Finset (Fin (Module.finrank ℝ
      (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed.covector.ker) → ℤ)) :
    Set (ℚ → M) :=
  ⋃ c, cell c ∩ (fun z ↦
    (Module.finBasis ℝ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed.covector.ker).equivFunL
      (populationSeedRootLabelValue (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed a z)) ⁻¹'
        (⋃ ν ∈ indices c, (unitPartition.box (order c) ν : Set _))

/-- Original regularity proves this global cutoff measurable, and every literal
original microcell is retained by it. Fixed cells recover exactly their own
prescribed coordinate-box union. -/
theorem PopulationLocalPressureCore.original_clockClass_microcell_labels_properties
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    {C : Type*} [Fintype C] (coreIndex : C → Fin D.haar.continuous.count)
    (cell : C → Set (ℚ → M)) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (order : C → ℕ) [∀ c, NeZero (order c)]
    (indices : ∀ c, Finset (Fin (Module.finrank ℝ
      (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed.covector.ker) → ℤ)) :
    let coord := fun c z ↦
      (Module.finBasis ℝ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed.covector.ker).equivFunL
        (populationSeedRootLabelValue (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed a z)
    let G := D.originalClockClassMicrocellLabels coreIndex cell order indices
    MeasurableSet G ∧
      (∀ c ν, ν ∈ indices c → ∀ z ∈ cell c, coord c z ∈ (unitPartition.box (order c) ν : Set _) → z ∈ G) ∧
      ∀ c, cell c ∩ G = cell c ∩ (coord c) ⁻¹'
        (⋃ ν ∈ indices c, (unitPartition.box (order c) ν : Set _)) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let coord := fun c z ↦
    (Module.finBasis ℝ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed.covector.ker).equivFunL
      (populationSeedRootLabelValue (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed a z)
  let cutoff := fun c ↦ (coord c) ⁻¹' (⋃ ν ∈ indices c, (unitPartition.box (order c) ν : Set _))
  have hmcoord (c : C) : Measurable (coord c) :=
    ((Module.finBasis ℝ (P (D.haar.continuous.coefficient (coreIndex c)).seedIndex).seed.covector.ker).equivFunL.continuous.measurable).comp
      (measurable_populationSeedRootLabelValue _ hF hcomplete hu ha hinj)
  have hmcutoff (c : C) : MeasurableSet (cutoff c) :=
    (MeasurableSet.iUnion fun ν ↦ MeasurableSet.iUnion fun _ ↦
      (unitPartition.box (order c) ν).measurableSet_coe).preimage (hmcoord c)
  refine ⟨MeasurableSet.iUnion fun c ↦ (hcell c).inter (hmcutoff c),?_,?_⟩
  · intro c ν hν z hz hbox
    exact mem_iUnion.mpr ⟨c,hz,mem_iUnion.mpr ⟨ν,mem_iUnion.mpr ⟨hν,hbox⟩⟩⟩
  · intro c
    exact original_cellwise_cutoff_trace cell cutoff hdisj c

end OTSelector.Reconstruction
