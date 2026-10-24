import OTSelector.Reconstruction.FinslerConcreteUpperMicrocellMass
import OTSelector.Reconstruction.FinslerOriginalMacroFilterCoordinates

/-! The actual original measurable-cell microcube producer can be filtered to
the actual macro-grid range with the same original root loss and vanishing
added coordinate volume. -/

open Set Function MeasureTheory ProbabilityTheory Filter Manifold BoxIntegral
open OTSelector.Geometry
open scoped Topology ContDiff ENNReal Classical

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The same prescribed microscopic grids approximate an original Finsler
cell by disjoint boxes belonging to the actual macro leaf range. Filtering
preserves the original loss exactly and decreases the added full-box volume. -/
theorem PopulationLocalPressureCore.exists_cell_macro_fitting_microscopic_cubes_with_two_mass_controls
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots)
    {q : ℕ} (basis : Module.Basis (Fin q) ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    {R : ℕ} (hR : 0 < R)
    (hunit : ∀ z ∈ L, labelCubeCoordinates basis (R : ℝ)
      (populationSeedRootLabelValue
        (P (D.haar.continuous.coefficient i).seedIndex).seed a z) ∈ unitCubeSet q)
    {ε : ℝ≥0∞} (hε : 0 < ε)
    (order : ℕ → ℕ) [∀ N, NeZero (order N)] (horder : Tendsto order atTop atTop) :
    let Seed := (P (D.haar.continuous.coefficient i).seedIndex).seed
    let coord := atlasSeedCoord Seed basis.equivFunL a
    ∃ C : ℕ → Finset (Fin q → ℤ),
      (∀ N, Set.PairwiseDisjoint (↑(C N) : Set (Fin q → ℤ))
        (fun ν ↦ (unitPartition.box (order N) ν : Set (Fin q → ℝ)))) ∧
      (∀ N, lambda (L \ coord ⁻¹' (⋃ ν ∈ C N,
        (unitPartition.box (order N) ν : Set (Fin q → ℝ)))) < ε) ∧
      (∀ N, volume ((coord '' L) \ (⋃ ν ∈ C N,
        (unitPartition.box (order N) ν : Set (Fin q → ℝ)))) < ε) ∧
      Tendsto (fun N ↦ volume ((⋃ ν ∈ C N,
        (unitPartition.box (order N) ν : Set (Fin q → ℝ))) \ (coord '' L)))
        atTop (𝓝 0) ∧
      (∀ N, C N ⊆ Finset.univ.image (originalMacroMicroIndex (q := q) R (order N))) := by
  classical
  let Seed := (P (D.haar.continuous.coefficient i).seedIndex).seed
  let root := populationSeedRootLabelValue Seed a
  let coord := atlasSeedCoord Seed basis.equivFunL a
  obtain ⟨C, hdisjoint, hloss, hmissing, hfill⟩ :=
    D.exists_cell_microscopic_cubes_with_two_mass_controls hF hcomplete hu ha hinj i hL hsub
      basis.equivFunL hε order horder
  let fitted := fun N ↦ originalMeetingMicrocells (order N) (coord '' L) (C N)
  refine ⟨fitted, ?_, ?_, ?_, ?_, ?_⟩
  · intro N
    apply (hdisjoint N).subset
    intro ν hν
    exact (Finset.mem_filter.mp hν).1
  · intro N
    have heq : L \ coord ⁻¹' (⋃ ν ∈ fitted N,
        (unitPartition.box (order N) ν : Set (Fin q → ℝ))) =
        L \ coord ⁻¹' (⋃ ν ∈ C N,
          (unitPartition.box (order N) ν : Set (Fin q → ℝ))) := by
      ext z
      constructor
      · rintro ⟨hz, hnot⟩
        refine ⟨hz, fun hmem ↦ hnot ?_⟩
        exact (originalMeetingMicrocells_image_mem_iUnion_iff
          (order N) coord L (C N) hz).mpr hmem
      · rintro ⟨hz, hnot⟩
        refine ⟨hz, fun hmem ↦ hnot ?_⟩
        exact (originalMeetingMicrocells_image_mem_iUnion_iff
          (order N) coord L (C N) hz).mp hmem
    rw [heq]
    exact hloss N
  · intro N
    have heq : (coord '' L) \ (⋃ ν ∈ fitted N,
        (unitPartition.box (order N) ν : Set (Fin q → ℝ))) =
        (coord '' L) \ (⋃ ν ∈ C N,
          (unitPartition.box (order N) ν : Set (Fin q → ℝ))) := by
      ext x
      constructor
      · rintro ⟨hx,hnot⟩
        exact ⟨hx,fun hm ↦ hnot ((originalMeetingMicrocells_mem_iUnion_iff
          (order N) (coord '' L) (C N) hx).mpr hm)⟩
      · rintro ⟨hx,hnot⟩
        exact ⟨hx,fun hm ↦ hnot ((originalMeetingMicrocells_mem_iUnion_iff
          (order N) (coord '' L) (C N) hx).mp hm)⟩
    rw [heq]
    exact hmissing N
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hfill (fun _ ↦ bot_le)
    intro N
    exact measure_mono (originalMeetingMicrocells_added_subset (order N) (coord '' L) (C N))
  · intro N
    exact originalMeetingMicrocells_labelImage_subset_macro_range basis root hR L hunit (C N)

end OTSelector.Reconstruction
