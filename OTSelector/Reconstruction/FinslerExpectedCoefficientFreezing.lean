import OTSelector.Reconstruction.FinslerCoefficientPressureFreezing

/-!
# Expected pressure on original coefficient freezing neighborhoods

The actual Borel root coefficient gives measurable quadratic sample costs. The
same finite root cover transfers integrability and expected-pressure bounds to
both the variable quadratic cost and an actual cost with the prescribed remainder.
-/

open Set Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
  {Ω : Type*} [MeasurableSpace Ω]

/-- Quadratic sample costs are measurable in the original root, clock pair and
vector displacement, by the actual joint Borel coefficient producer. -/
theorem measurable_quadratic_cost [T2Space M] [PreconnectedSpace M] [BorelSpace M]
    [MeasurableSpace.CountablySeparated Z]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFreezingMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {z : Ω → Z} {p : Ω → ℝ × ℝ}
    {v : Ω → Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ}
    (hz : Measurable z) (hp : Measurable p) (hv : Measurable v) :
    Measurable (fun ξ ↦ matrixQuadratic (C.matrix (z ξ) (p ξ)) (v ξ)) := by
  have hm := (measurable_populationSeedRootCoefficient (P C.seedIndex).seed
    hF hcomplete hu ha hinj (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker)).comp
      (hz.prodMk hp)
  exact continuous_matrixQuadratic.measurable.comp (hm.prodMk hv)

namespace RelativeRootCover

variable {C} {ε : ℝ} (D : C.RelativeRootCover ε)
  {Q : Measure Ω} [IsProbabilityMeasure Q]

/-- The original variable quadratic coefficient and its frozen reference have the
expected-pressure comparison. The compared pressure's integrability is derived. -/
theorem expected_assignment_pressure_comparison
    [T2Space M] [PreconnectedSpace M] [BorelSpace M]
    [MeasurableSpace.CountablySeparated Z]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instExpectedFreezingMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {N : ℕ} (hN : 0 < N) {z₀ : Z} (hz₀ : z₀ ∈ D.centers)
    (z : Ω → Fin N → Fin N → Z) (p : Ω → Fin N → Fin N → ℝ × ℝ)
    (v : Ω → Fin N → Fin N → Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
    (hz : ∀ i j, Measurable (fun ξ ↦ z ξ i j))
    (hp : ∀ i j, Measurable (fun ξ ↦ p ξ i j))
    (hv : ∀ i j, Measurable (fun ξ ↦ v ξ i j))
    (hroot : ∀ᵐ ξ ∂Q, ∀ i j, z ξ i j ∈ C.roots ∩ D.neighborhood z₀)
    (hpair : ∀ᵐ ξ ∂Q, ∀ i j, p ξ i j ∈ C.window.region)
    (g h : Ω → Matrix (Fin N) (Fin N) ℝ) (t G B : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hh : ∀ᵐ ξ ∂Q, ∀ i j, |h ξ i j| ≤ G)
    (hgh : ∀ᵐ ξ ∂Q, ∀ i j, |g ξ i j - h ξ i j| ≤ B)
    (hdi : Integrable (fun ξ ↦ perturbedAssignmentValue
      (fun i j ↦ matrixQuadratic (C.matrix z₀ (p ξ i j)) (v ξ i j)) (h ξ) t / N) Q) :
    let c := fun ξ i j ↦ matrixQuadratic (C.matrix (z ξ i j) (p ξ i j)) (v ξ i j)
    let d := fun ξ i j ↦ matrixQuadratic (C.matrix z₀ (p ξ i j)) (v ξ i j)
    Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t / N) Q ∧
      |(∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t / N ∂Q) -
        ∫ ξ, perturbedAssignmentValue (d ξ) (h ξ) t / N ∂Q| ≤
      ε * ((∫ ξ, perturbedAssignmentValue (d ξ) (h ξ) t / N ∂Q) + |t| * G) + |t| * B := by
  apply expected_perturbedAssignmentValue_div_abs_sub_le_relative hN _ g _ h t ε G B hε0 hε1
    (fun i j ↦ C.measurable_quadratic_cost hF hcomplete hu ha hinj (hz i j) (hp i j) (hv i j))
    hg hdi _ hh hgh
  filter_upwards [hroot, hpair] with ξ hrootξ hpairξ
  exact fun i j ↦ D.relative z₀ hz₀ (z ξ i j) (hrootξ i j) (p ξ i j) (hpairξ i j) (v ξ i j)

omit [BorelSpace E] in
/-- Expected pressure for the actual distance-cost array follows from its same-kernel
quadratic remainder, with no additional optimizer moment or integrability hypothesis. -/
theorem expected_distance_assignment_pressure_comparison
    {N : ℕ} (hN : 0 < N) {z₀ : Z} (hz₀ : z₀ ∈ D.centers)
    (z : Ω → Fin N → Fin N → Z) (p : Ω → Fin N → Fin N → ℝ × ℝ)
    (v : Ω → Fin N → Fin N → Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
    (hroot : ∀ᵐ ξ ∂Q, ∀ i j, z ξ i j ∈ C.roots ∩ D.neighborhood z₀)
    (hpair : ∀ᵐ ξ ∂Q, ∀ i j, p ξ i j ∈ C.window.region)
    (c g h : Ω → Matrix (Fin N) (Fin N) ℝ) (t G B : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : 2 * ε ≤ 1)
    (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (hg : ∀ i j, Measurable (fun ξ ↦ g ξ i j))
    (hcost : ∀ᵐ ξ ∂Q, ∀ i j,
      |c ξ i j - matrixQuadratic (C.matrix (z ξ i j) (p ξ i j)) (v ξ i j)| ≤
        ε * D.lowerBound * ‖v ξ i j‖ ^ 2)
    (hh : ∀ᵐ ξ ∂Q, ∀ i j, |h ξ i j| ≤ G)
    (hgh : ∀ᵐ ξ ∂Q, ∀ i j, |g ξ i j - h ξ i j| ≤ B)
    (hdi : Integrable (fun ξ ↦ perturbedAssignmentValue
      (fun i j ↦ matrixQuadratic (C.matrix z₀ (p ξ i j)) (v ξ i j)) (h ξ) t / N) Q) :
    let d := fun ξ i j ↦ matrixQuadratic (C.matrix z₀ (p ξ i j)) (v ξ i j)
    Integrable (fun ξ ↦ perturbedAssignmentValue (c ξ) (g ξ) t / N) Q ∧
      |(∫ ξ, perturbedAssignmentValue (c ξ) (g ξ) t / N ∂Q) -
        ∫ ξ, perturbedAssignmentValue (d ξ) (h ξ) t / N ∂Q| ≤
      (2 * ε) * ((∫ ξ, perturbedAssignmentValue (d ξ) (h ξ) t / N ∂Q) + |t| * G) + |t| * B := by
  apply expected_perturbedAssignmentValue_div_abs_sub_le_relative hN c g _ h t (2 * ε) G B
    (mul_nonneg (by norm_num) hε0) hε1 hc hg hdi _ hh hgh
  filter_upwards [hroot, hpair, hcost] with ξ hrootξ hpairξ hcostξ
  exact fun i j ↦ D.relative_cost_of_quadratic_remainder hε0 hz₀ (hrootξ i j)
    (hpairξ i j) (v ξ i j) (hcostξ i j)

end RelativeRootCover
end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
