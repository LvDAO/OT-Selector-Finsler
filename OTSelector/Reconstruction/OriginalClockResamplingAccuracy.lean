import OTSelector.Reconstruction.FinslerOriginalRangeClockResamplingData

/-! The same original bins retain their actual resampling certificate when
reported under a larger allowed width or larger error budget. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-- Report the same literal scalar cells under a larger admissible width. -/
def FiniteScalarBins.relaxWidth {range : Set ℝ} {width width' : ℝ}
    (Q : FiniteScalarBins range width) (hwidth : width ≤ width') : FiniteScalarBins range width' where
  count := Q.count
  cell := Q.cell
  measurable_cell := Q.measurable_cell
  subset := Q.subset
  disjoint := Q.disjoint
  union_eq := Q.union_eq
  diameter := fun i x hx y hy ↦ (Q.diameter i x hx y hy).trans
    (div_le_div_of_nonneg_right hwidth (by norm_num))

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}
  {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ}
  {range : Set ℝ} {width width' : ℝ} {Q : FiniteScalarBins range width}
  {z : Z} {hz : z ∈ C.roots} {f : M × M →ᵇ ℝ} {ε η ε' η' : ℝ}

/-- The same actual resampling data, with unchanged clocks and costs, survive
a larger reported width. Only its diameter budget changes. -/
def OriginalRangeClockResamplingData.relaxWidth
    (D : OriginalRangeClockResamplingData C Q z hz f ε η) (hwidth : width ≤ width') :
    OriginalRangeClockResamplingData C (Q.relaxWidth hwidth) z hz f ε η where
  kineticConstant := D.kineticConstant
  kineticConstant_nonneg := D.kineticConstant_nonneg
  kinetic_nonneg := D.kinetic_nonneg
  kinetic_bound := D.kinetic_bound
  relative := D.relative
  probe_error := D.probe_error

/-- An actual nonnegative reference kinetic coefficient allows larger
relative and physical-probe tolerances without changing the model. -/
def OriginalRangeClockResamplingData.increaseErrors
    (D : OriginalRangeClockResamplingData C Q z hz f ε η) (hε : ε ≤ ε') (hη : η ≤ η') :
    OriginalRangeClockResamplingData C Q z hz f ε' η' where
  kineticConstant := D.kineticConstant
  kineticConstant_nonneg := D.kineticConstant_nonneg
  kinetic_nonneg := D.kinetic_nonneg
  kinetic_bound := D.kinetic_bound
  relative := fun x y hxy v ↦ (D.relative x y hxy v).trans
    (mul_le_mul_of_nonneg_right hε (C.clockClassKinetic_nonneg Q z hz _ _ v))
  probe_error := fun x y hxy ↦ (D.probe_error x y hxy).trans hη

end OTSelector.Reconstruction
