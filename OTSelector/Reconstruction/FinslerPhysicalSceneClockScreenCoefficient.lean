import OTSelector.Reconstruction.FinslerPopulationLocalPressureCore

/-!
# Smaller clock screens on the same original cores

The rational clock gap can be placed below any positive numerical threshold,
with an arbitrarily small loss of original root mass. The original scalar
interval, seed data, conditional laws and retained recovery are preserved.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z] [PolishSpace Z] [BorelSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z} [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- Decreasing the actual rational pair-gap screen preserves the outer scalar
interval and original coupling loss, after an arbitrarily small original-root
refinement that supplies continuity on the enlarged legal pair region. -/
theorem OriginalPopulationCoefficientCore.exists_smaller_clock_screen_refinement
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {θ : ℝ} (hθ : 0 < θ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C' : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ,
      C'.seedIndex = C.seedIndex ∧ C'.window.val.1 = C.window.val.1 ∧
      C'.window.val.2.1 = C.window.val.2.1 ∧ (C'.window.val.2.2 : ℝ) ≤ θ ∧
      C'.roots ⊆ C.roots ∧ lambda (C.roots \ C'.roots) < ε := by
  obtain ⟨e, he0, heθ⟩ := exists_rat_btwn hθ
  have he0q : (0 : ℚ) < e := by exact_mod_cast he0
  let q : RationalScalarPairWindow := ⟨(C.window.val.1, C.window.val.2.1,
    min C.window.val.2.2 e), C.window.property.1, lt_min C.window.property.2 he0q⟩
  have hqold : (q.val.2.2 : ℝ) ≤ C.window.val.2.2 := by
    exact_mod_cast (min_le_left C.window.val.2.2 e)
  have hqθ : (q.val.2.2 : ℝ) ≤ θ := by
    exact (show (q.val.2.2 : ℝ) ≤ e by exact_mod_cast (min_le_right C.window.val.2.2 e)).trans heθ.le
  have hregion : C.window.region ⊆ q.region :=
    fun p hp ↦ ⟨hp.1, hqold.trans hp.2⟩
  let S := (P C.seedIndex).seed
  have hroots : MeasurableSet C.roots := C.roots_compact.measurableSet
  have hgood : ∀ᵐ z ∂lambda.restrict C.roots,
      HasOriginalSeedPairWindow S a (condDistrib u a η₀) (condDistrib u a η₁)
        C.window.val.1 C.window.val.2.1 z ∧ True := by
    filter_upwards [ae_restrict_mem hroots] with z hz
    exact ⟨C.original_window z hz, trivial⟩
  have hlr : (C.window.val.1 : ℝ) ≤ C.window.val.2.1 := by
    exact_mod_cast C.window.property.1.le
  obtain ⟨K, hsub, hK, hloss, hcont, hwindow⟩ :=
    exists_populationSeedRootCoefficient_compact_core S hF hcomplete hu ha hinj hroots
      (measure_ne_top lambda C.roots) hlr q.isCompact_region q.region_subset hgood hε
  let C' : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ := {
    seedIndex := C.seedIndex
    window := q
    roots := K
    roots_compact := hK
    roots_subset_piece := hsub.trans C.roots_subset_piece
    coefficient_continuous := hcont
    original_window := fun z hz ↦ (hwindow z hz).1
    coefficient_posDef := fun z hz p hp ↦
      ((hwindow z hz).1).posDef_rootCoefficient S hF hcomplete hu ha hinj (q.region_subset hp)
    coupling_loss := fun z hz π hπ horder ↦
      (measure_mono (compl_subset_compl.mpr hregion)).trans_lt
        (C.coupling_loss z (hsub hz) π hπ horder) }
  exact ⟨C', rfl, rfl, rfl, hqθ, hsub, hloss⟩

end OTSelector.Reconstruction
