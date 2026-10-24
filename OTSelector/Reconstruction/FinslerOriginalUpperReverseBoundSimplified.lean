import OTSelector.Reconstruction.FinslerOriginalUpperPoolReverseBound
import OTSelector.Reconstruction.FinslerOriginalUpperAndSmallNResiduals

/-!
# Upper reverse bound reduction for the V9 residual bundle

`UpperSmallNResiduals` (FinslerOriginalUpperAndSmallNResiduals) still contains the
typed reverse bound `hRB : UpperPoolReverseBound qU mU pc datum`.  This module
discharges the off-radius part of that statement: by
`exists_upperPoolReverseBound_extension_of_onRadius` it suffices to provide the
on-radius reverse bound `UpperPoolReverseBoundOnRadius q m pc datum radius`; the
resulting `pc'` agrees with `pc` on the perturbation interval and satisfies the
unconditional reverse bound.  The remaining bundle components are then reassembled
with `upperSmallNResiduals_of_reverseBound`.
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

/-- **Off-radius reverse bound discharged.**  Given the on-radius reverse bound and
`0 < m`, the off-radius part of `UpperPoolReverseBound` is a convention on the local
limits: extending the pool off the perturbation interval gives a modified `pc'`,
equal to `pc` on the interval, satisfying the unconditional reverse bound. -/
theorem exists_upperPoolReverseBound_of_onRadius {hm : 0 < m}
    {radius : FinalRadiusField A B}
    (hon : UpperPoolReverseBoundOnRadius q m pc datum radius) :
    ∃ pc' : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ,
      (∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m),
        |t| < radius f → pc' f t c = pc f t c) ∧
      UpperPoolReverseBound q m pc' datum :=
  exists_upperPoolReverseBound_extension_of_onRadius (hm := hm) hon

/-- **Reassembly.**  Once the reverse bound (at the possibly extended pool `pc'`) and
the other four residuals are supplied, the V9 bundle is assembled. -/
theorem upperSmallNResiduals_of_reverseBound {hLB hcell hsmall hpcIntr hRB : Prop}
    (h1 : hLB) (h2 : hcell) (h3 : hsmall) (h4 : hpcIntr) (h5 : hRB) :
    UpperSmallNResiduals hLB hcell hsmall hpcIntr hRB :=
  ⟨h1, h2, h3, h4, h5⟩

end OTSelector.Reconstruction