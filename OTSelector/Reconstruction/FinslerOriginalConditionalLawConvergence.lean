import OTSelector.Reconstruction.FinslerPopulationPressureCore
import OTSelector.MeasureTheory.VariationObservation
import OTSelector.MeasureTheory.RetainedMarginalVariation

/-! Actual conditional-law variation on the original Finsler continuity cores
passes exactly through scalar-range lifts and arbitrary retained pairings. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {loss : ℝ≥0∞}

/-- The original stored L1 continuity proves actual full conditional-law
variation convergence at every original root of a retained continuity core. -/
theorem PopulationPressureCore.original_clock_law_variation_tendsto
    (D : PopulationPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good loss)
    (z : ℕ → D.roots) (ref : D.roots) (hz : Tendsto z atTop (𝓝 ref))
    (color : Fin 2) :
    Tendsto (fun n ↦
      ((populationTwoColorClockKernel u a μ ν color (z n).val).toSignedMeasure -
        (populationTwoColorClockKernel u a μ ν color ref.val).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
  have hclass := D.continuous_class.domRestrict.continuousAt.tendsto.comp hz
  have hcolor := (continuous_apply color).continuousAt.tendsto.comp hclass
  have hnorm := (hcolor.sub_const (D.densityClass color ref.val)).norm
  change Tendsto (fun n ↦ ‖D.densityClass color (z n).val - D.densityClass color ref.val‖)
    atTop (𝓝 ‖D.densityClass color ref.val - D.densityClass color ref.val‖) at hnorm
  have heq n :
      ((populationTwoColorClockKernel u a μ ν color (z n).val).toSignedMeasure -
        (populationTwoColorClockKernel u a μ ν color ref.val).toSignedMeasure).totalVariation.real univ =
        ‖D.densityClass color (z n).val - D.densityClass color ref.val‖ := by
    rw [measureReal_def,D.variation color _ (z n).property _ ref.property,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  simpa only [heq,sub_self,norm_zero] using hnorm

/-- Exact original scalar-range lifts have precisely the same actual
conditional-law convergence. No variation estimate on a chosen pair coupling
is required. -/
theorem PopulationPressureCore.original_lifted_clock_law_variation_tendsto
    (D : PopulationPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good loss)
    (z : ℕ → D.roots) (ref : D.roots) (hz : Tendsto z atTop (𝓝 ref))
    (color : Fin 2) {range : Set ℝ} (hrange : MeasurableSet range)
    (αn : ℕ → ProbabilityMeasure range) (α : ProbabilityMeasure range)
    (hmapn : ∀ n, (αn n : Measure range).map Subtype.val =
      populationTwoColorClockKernel u a μ ν color (z n).val)
    (hmap : (α : Measure range).map Subtype.val =
      populationTwoColorClockKernel u a μ ν color ref.val) :
    Tendsto (fun n ↦
      ((αn n : Measure range).toSignedMeasure - (α : Measure range).toSignedMeasure).totalVariation.real univ)
      atTop (𝓝 0) := by
  have heq n := original_totalVariation_real_map_eq (αn n : Measure range) (α : Measure range)
    Subtype.val (MeasurableEmbedding.subtype_coe hrange)
  have hactual := D.original_clock_law_variation_tendsto z ref hz color
  apply hactual.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    simpa only [hmapn n,hmap] using heq n

end OTSelector.Reconstruction
