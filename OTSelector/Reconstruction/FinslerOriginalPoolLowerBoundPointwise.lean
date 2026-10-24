import OTSelector.Reconstruction.FinslerOriginalPoolLowerBoundFromCoercion

/-!
# Pointwise and competitor formulations of the upper pool lower bound

`PoolI2Inequality`, `PoolCompetitorInequality` and `UpperPoolLowerBound` are
proved equivalent. The infimum passage uses the nonempty second-moment class;
the converse uses its bounded-below tilted costs. These facts are supplied by
`StationaryPressureDatum` and the existing upper pool envelope interface.

This completes the conversion between the interfaces, but does not construct the
pool comparison from the physical data. A condition on the stationary datum alone,
such as squared probe-kinetic coercion, cannot imply the comparison for an unrelated
block pool: `exists_not_poolI2Inequality` constructs a pool equal to `I2 + 1` for any
datum. A producer must relate the block pool to that same stationary datum, as in
the blockwise weak-duality interface.
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

/-- The pointwise pool ≤ second-moment-infimum inequality: the single named paper
input of the lower-bound half. -/
def PoolI2Inequality (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ),
    endgameUpperPressure_actual q m pc f t ≤ (datum f).I2 t

/-- The named inequality is exactly the lower-bound half. -/
theorem upperPoolLowerBound_of_poolI2Inequality
    (h : PoolI2Inequality (G := G) (Cb := Cb) q m pc datum) :
    UpperPoolLowerBound q m pc datum :=
  upperPoolLowerBound_of_le_I2 h

/-- Converse: the lower-bound half yields the named inequality. -/
theorem poolI2Inequality_of_upperPoolLowerBound
    (hl : UpperPoolLowerBound q m pc datum) :
    PoolI2Inequality (G := G) (Cb := Cb) q m pc datum :=
  fun f t => le_I2_of_upperPoolLowerBound hl f t

/-- The pool is below the stationary value of every second-moment competitor. -/
def PoolCompetitorInequality (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ) (w : W), w ∈ (datum f).C2 →
    endgameUpperPressure_actual q m pc f t ≤ (datum f).K w + t * (datum f).P w

/-- Taking the infimum of the competitor inequalities gives the pointwise bound. -/
theorem poolI2Inequality_of_poolCompetitorInequality
    (h : PoolCompetitorInequality (G := G) (Cb := Cb) q m pc datum) :
    PoolI2Inequality (G := G) (Cb := Cb) q m pc datum :=
  poolI2Inequality_of_upperPoolLowerBound h

/-- The infimum bound controls every competitor, since its costs are bounded below. -/
theorem poolCompetitorInequality_of_poolI2Inequality
    (h : PoolI2Inequality (G := G) (Cb := Cb) q m pc datum) :
    PoolCompetitorInequality (G := G) (Cb := Cb) q m pc datum :=
  upperPoolLowerBound_of_poolI2Inequality h

/-- The pointwise and competitor formulations carry exactly the same condition. -/
theorem poolCompetitorInequality_iff_poolI2Inequality :
    PoolCompetitorInequality (G := G) (Cb := Cb) q m pc datum ↔
      PoolI2Inequality (G := G) (Cb := Cb) q m pc datum :=
  ⟨poolI2Inequality_of_poolCompetitorInequality,
    poolCompetitorInequality_of_poolI2Inequality⟩

omit [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- The named competitor condition is the existing lower-bound interface. -/
theorem poolCompetitorInequality_iff_upperPoolLowerBound :
    PoolCompetitorInequality (G := G) (Cb := Cb) q m pc datum ↔
      UpperPoolLowerBound q m pc datum := Iff.rfl

/-- For any stationary datum an unrelated constant-in-block pool can violate the
comparison. Thus assumptions on the datum alone cannot produce the comparison. -/
theorem exists_not_poolI2Inequality (hm : 0 < m) (f₀ : FinalProbeSpace A B) :
    ∃ pc' : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ,
      ¬ PoolI2Inequality (G := G) (Cb := Cb) q m pc' datum := by
  let pc' : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ :=
    fun f t _ ↦ (datum f).I2 t + 1
  refine ⟨pc', ?_⟩
  intro h
  have hpool := endgameUpperPressure_actual_eq_of_constBlock hm pc'
    (fun f t ↦ (datum f).I2 t + 1) (fun _ _ _ ↦ rfl) f₀ 0
  have hbad := h f₀ 0
  rw [hpool] at hbad
  linarith

end OTSelector.Reconstruction
