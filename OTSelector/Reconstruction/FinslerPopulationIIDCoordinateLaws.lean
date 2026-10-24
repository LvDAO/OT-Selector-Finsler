import OTSelector.Reconstruction.FinslerPopulationHaarCellLaws
import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact original iid restrictions in the retained Haar-clock coordinates. -/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The probability mass of any prescribed finite core assignment is the product
of its original root masses, separately for each physical color. -/
theorem FiniteLabelCoreRecovery.iid_assignment_mass
    {X Z I J : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype I] [Fintype J]
    {u : X → ℝ} {a : X → Z} {b : Z × ℝ → X} {lambda : Measure Z}
    {η₀ η₁ : Measure X} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {K : J → Set Z}
    (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K) (assignment : I → J) :
    (Measure.pi (fun _ : I ↦ η₀)) (univ.pi (fun i ↦ a ⁻¹' K (assignment i))) =
        ∏ i, lambda (K (assignment i)) ∧
    (Measure.pi (fun _ : I ↦ η₁)) (univ.pi (fun i ↦ a ⁻¹' K (assignment i))) =
        ∏ i, lambda (K (assignment i)) := by
  constructor
  · simp_rw [Measure.pi_pi, D.source_mass]
  · simp_rw [Measure.pi_pi, D.target_mass]

variable {E M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [Fintype I] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Restricting each original iid sample to its assigned actual core and then
reading its seed label and clock gives the product of the original Haar-clock
laws. Each sample may be assigned a different core, with its original mass. -/
theorem PopulationHaarPressureCore.iid_coordinate_laws_on_subsets
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instIIDCoordinateMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (assignment : I → Fin D.continuous.count) (L : I → Set (ℚ → M))
    (hL : ∀ i, MeasurableSet (L i))
    (hsub : ∀ i, L i ⊆ (D.continuous.coefficient (assignment i)).roots) :
    let C := fun i ↦ D.continuous.coefficient (assignment i)
    let S := fun i ↦ (P (C i).seedIndex).seed
    let R := fun i ↦ populationSeedRootLabelValue (S i) a
    let coordinate := fun (i : I) (x : M) ↦ (R i (a x), u x)
    let localLaw (η : Measure M) [IsFiniteMeasure η] (i : I) :=
      (((κ (C i).seedIndex).restrict (R i '' L i)).withDensity
        (populationSeedPieceHaarDensity P a κ lambda (C i).seedIndex)) ⊗ₘ
          populationSeedCoordinateClockKernel (S i) a ha (condDistrib u a η)
    (((Measure.pi (fun _ : I ↦ η₀)).restrict
      (univ.pi (fun i ↦ a ⁻¹' L i))).map (fun x i ↦ coordinate i (x i)) =
        Measure.pi (localLaw η₀)) ∧
    (((Measure.pi (fun _ : I ↦ η₁)).restrict
      (univ.pi (fun i ↦ a ⁻¹' L i))).map (fun x i ↦ coordinate i (x i)) =
        Measure.pi (localLaw η₁)) := by
  let _instIIDCoordinateMetric : MetricSpace M := F.metricSpace
  let _instIIDCoordinateProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instIIDCoordinatePolish : PolishSpace M := inferInstance
  let _instIIDCoordinateBorel : BorelSpace (ℚ → M) := inferInstance
  dsimp only
  have hmeas (i : I) : Measurable (fun x ↦
      (populationSeedRootLabelValue (P (D.continuous.coefficient (assignment i)).seedIndex).seed
        a (a x), u x)) :=
    ((measurable_populationSeedRootLabelValue _ hF hcomplete hu ha hinj).comp ha).prodMk
      hu.continuous.measurable
  have hjoint (i : I) :=
    D.cell_joint_laws hF hcomplete hu ha hinj (assignment i) (hL i) (hsub i)
  constructor
  · rw [Measure.restrict_pi_pi, Measure.pi_map_pi (fun i ↦ (hmeas i).aemeasurable)]
    congr 1
    funext i
    exact (hjoint i).1
  · rw [Measure.restrict_pi_pi, Measure.pi_map_pi (fun i ↦ (hmeas i).aemeasurable)]
    congr 1
    funext i
    exact (hjoint i).2

/-- Restricting each original iid sample to its assigned actual core and then
reading its seed label and clock gives the product of the original Haar-clock
laws. Each sample may be assigned a different core, with its original mass. -/
theorem PopulationHaarPressureCore.iid_coordinate_laws
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ ε : ℝ≥0∞}
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instIIDCoordinateMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (assignment : I → Fin D.continuous.count) :
    let C := fun i ↦ D.continuous.coefficient (assignment i)
    let S := fun i ↦ (P (C i).seedIndex).seed
    let R := fun i ↦ populationSeedRootLabelValue (S i) a
    let coordinate := fun (i : I) (x : M) ↦ (R i (a x), u x)
    let localLaw (η : Measure M) [IsFiniteMeasure η] (i : I) :=
      (((κ (C i).seedIndex).restrict (R i '' (C i).roots)).withDensity
        (populationSeedPieceHaarDensity P a κ lambda (C i).seedIndex)) ⊗ₘ
          populationSeedCoordinateClockKernel (S i) a ha (condDistrib u a η)
    (((Measure.pi (fun _ : I ↦ η₀)).restrict
      (univ.pi (fun i ↦ a ⁻¹' (C i).roots))).map (fun x i ↦ coordinate i (x i)) =
        Measure.pi (localLaw η₀)) ∧
    (((Measure.pi (fun _ : I ↦ η₁)).restrict
      (univ.pi (fun i ↦ a ⁻¹' (C i).roots))).map (fun x i ↦ coordinate i (x i)) =
        Measure.pi (localLaw η₁)) := by
  exact D.iid_coordinate_laws_on_subsets hF hcomplete hu ha hinj assignment
    (fun i ↦ (D.continuous.coefficient (assignment i)).roots)
    (fun i ↦ D.continuous.recovery.measurable (assignment i)) (fun _ ↦ Subset.rfl)

end OTSelector.Reconstruction
