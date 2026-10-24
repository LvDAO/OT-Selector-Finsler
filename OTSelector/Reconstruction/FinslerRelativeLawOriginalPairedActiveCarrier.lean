import OTSelector.Reconstruction.FinslerRelativeLawOriginalPairedActiveLaw
import OTSelector.Reconstruction.FinslerConcreteUpperActualClassObservation

/-! Actual retained spatial laws carry the same original compact root coordinates. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-- Taking the optional spatial law preserves every almost-everywhere carrier
of the unnormalized retained law, without a nonzero-mass assumption. -/
theorem originalRetainedSpatialLaw_ae_some_mem {W : Type*} [MeasurableSpace W] [Zero W]
    (m : Measure W) (classMass : ℝ≥0∞) {s : Set W}
    (hs : MeasurableSet s) (hm : ∀ᵐ w ∂m, w ∈ s) :
    ∀ᵐ o ∂originalRetainedSpatialLaw m classMass, ∀ w, o = some w → w ∈ s := by
  have hp : MeasurableSet {o : Option W | ∀ w, o = some w → w ∈ s} := by
    have heq : {o : Option W | ∀ w, o = some w → w ∈ s} =
        {o | o.isSome = false} ∪ {o | o.elim 0 id ∈ s} := by
      ext o
      cases o <;> simp
    rw [heq]
    exact (measurableSet_eq_fun MeasureTheory.Option.measurable_isSome measurable_const).union
      (hs.preimage (MeasureTheory.Option.measurable_elim 0 measurable_id))
  rw [originalRetainedSpatialLaw,ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hp).mpr (by intro w hw; cases hw)
  · apply Measure.ae_smul_measure
    apply (ae_map_iff MeasureTheory.Option.measurable_some.aemeasurable hp).mpr
    filter_upwards [hm] with x hx
    intro w hw
    exact (Option.some.inj hw) ▸ hx

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

/-- The nullable spatial factor automatically has the compact root carrier
required by the actual original macro-grid theorem. -/
theorem PopulationLocalPressureCore.original_retained_spatial_root_carrier
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (i : Fin D.haar.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.haar.continuous.coefficient i).roots) (classMass : ℝ≥0∞) :
    let C := D.haar.continuous.coefficient i
    let R := populationSeedRootLabelValue (P C.seedIndex).seed a
    ∀ᵐ o ∂originalRetainedSpatialLaw ((κ C.seedIndex).restrict (R '' L)) classMass,
      ∀ w, o = some w → w ∈ R '' C.roots := by
  let C := D.haar.continuous.coefficient i
  let R := populationSeedRootLabelValue (P C.seedIndex).seed a
  have himage : MeasurableSet (R '' L) := D.haar.measurable_cell_label_image hcomplete i hL hsub
  have h := originalRetainedSpatialLaw_ae_some_mem
    ((κ C.seedIndex).restrict (R '' L)) classMass himage (ae_restrict_mem himage)
  filter_upwards [h] with o ho
  intro w hw
  exact image_mono hsub (ho w hw)

end OTSelector.Reconstruction
