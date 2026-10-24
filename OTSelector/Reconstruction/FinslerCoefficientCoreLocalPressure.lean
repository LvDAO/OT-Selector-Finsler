import OTSelector.Reconstruction.FinslerPopulationLocalPressureCore
import OTSelector.Reconstruction.FinslerCoefficientCoreTaylorCover

/-!
# Taylor neighborhoods from the original local pressure core

The retained actual Haar intensities already provide continuous inverse labels.
Together with the core's actual geometric remainder this yields finite Taylor
neighborhoods with no further root restriction or additional assumption.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Every retained original coefficient piece has a finite Taylor and freezing
cover, with its original masses, intensities and conditional laws unchanged. -/
theorem PopulationLocalPressureCore.nonempty_taylorRootCover
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instLocalTaylorMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (i : Fin D.haar.continuous.count) {ε : ℝ} (hε : 0 < ε) :
    Nonempty ((D.haar.continuous.coefficient i).TaylorRootCover ε) := by
  let _instLocalTaylorMetric : MetricSpace M := F.metricSpace
  let _instLocalTaylorProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instLocalTaylorPolish : PolishSpace M := inferInstance
  have hlabel : ContinuousOn
      (populationSeedRootLabelValue (P (D.haar.continuous.coefficient i).seedIndex).seed a)
      (D.haar.continuous.coefficient i).roots := by
    rw [← D.haar.intensity_roots i]
    exact (D.haar.intensity i).continuous_label
  exact (D.haar.continuous.coefficient i).exists_taylorRootCover hlabel
    (D.source_remainder_on_piece hF hcomplete hu ha hinj i) hε

end OTSelector.Reconstruction
