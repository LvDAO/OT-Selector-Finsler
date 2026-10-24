import OTSelector.Reconstruction.FinslerOriginalUpperPoolReverseBound

/-!
# The lower-bound half of the upper pool bridge

`UpperPoolLowerBound q m pc datum` is the lower-bound half of the bridge: by
`upperPoolLowerBound_iff_le_I2` it is equivalent to the pointwise inequality
`endgameUpperPressure_actual q m pc f t ≤ (datum f).I2 t` for all `f`, `t`
(direction confirmed by its use as the first argument of `le_antisymm` in
`actualUpperReadout_iff_lowerBound_and_reverseBound`).

This module records the exact interface and provides both conversion directions.
A producer must connect the physical block pool to the same stationary datum,
for example through blockwise weak duality. Squared coercion of the stationary
datum alone cannot bound an unrelated pool; the checked obstruction is
`exists_not_poolI2Inequality` in `FinslerOriginalPoolLowerBoundPointwise`.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Topology TopologicalSpace
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex OTSelector.Pressure Module
open scoped Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {μ ν : ProbabilityMeasure M}
  {A B : Set M} {W : Type*} {G Cb : ℝ} {q m : ℕ}
  {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
  {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}

/-- **The pointwise pool ≤ I2 inequality produces the lower-bound half.** -/
theorem upperPoolLowerBound_of_le_I2
    (h : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      endgameUpperPressure_actual q m pc f t ≤ (datum f).I2 t) :
    UpperPoolLowerBound q m pc datum :=
  (upperPoolLowerBound_iff_le_I2 q m pc datum).mpr h

/-- **Extraction direction.**  The lower-bound half gives the pointwise pool ≤ I2
inequality. -/
theorem le_I2_of_upperPoolLowerBound
    (hl : UpperPoolLowerBound q m pc datum) (f : FinalProbeSpace A B) (t : ℝ) :
    endgameUpperPressure_actual q m pc f t ≤ (datum f).I2 t :=
  (upperPoolLowerBound_iff_le_I2 q m pc datum).mp hl f t

end OTSelector.Reconstruction
