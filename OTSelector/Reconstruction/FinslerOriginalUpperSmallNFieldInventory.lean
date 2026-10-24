import OTSelector.Reconstruction.FinslerOriginalUpperReverseBoundSimplified
import OTSelector.Reconstruction.FinslerOriginalUpperAndSmallNResiduals

/-!
# Field inventory of the upper/small-n residual bundle

`UpperSmallNResiduals hLB hcell hsmall hpcIntr hRB` has five fields (exact types
recorded in the report of this wave).  The reverse-bound field is now reducible:
`exists_upperPoolReverseBound_of_onRadius` turns an on-radius reverse bound into an
unconditional reverse bound at a pool `pc'` agreeing with `pc` on the perturbation
interval.  This module adds the four-field constructor, so a caller only supplies
`hLB`, `hcell`, `hsmall`, `hpcIntr` together with the on-radius reverse-bound data.

Producers existing in the repository (for the report): none of the four remaining
fields has a completed producer in the current tree; the paper-proven side
statements are still the residual inputs.
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

/-- **Four-field constructor.**  The V9 bundle from `hLB`, `hcell`, `hsmall`,
`hpcIntr` and the on-radius reverse bound: the reverse-bound field is produced from
the on-radius data, with the extended pool `pc'` (equal to `pc` on the perturbation
interval). -/
theorem upperSmallNResiduals_of_fourFields {hm : 0 < m} {radius : FinalRadiusField A B}
    (hon : UpperPoolReverseBoundOnRadius q m pc datum radius)
    {hLB hcell hsmall hpcIntr : Prop} (h1 : hLB) (h2 : hcell) (h3 : hsmall)
    (h4 : hpcIntr) :
    ∃ pc' : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ,
      (∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m),
        |t| < radius f → pc' f t c = pc f t c) ∧
      UpperSmallNResiduals hLB hcell hsmall hpcIntr (UpperPoolReverseBound q m pc' datum) := by
  obtain ⟨pc', heq, hrb⟩ :=
    exists_upperPoolReverseBound_extension_of_onRadius (hm := hm) hon
  exact ⟨pc', heq, upperSmallNResiduals_of_reverseBound h1 h2 h3 h4 hrb⟩

/-- **Four-field constructor at an already supplied reverse bound.**  If the
reverse-bound field is available at some `pc'`, the bundle is assembled from it and
the remaining four fields. -/
theorem upperSmallNResiduals_of_fourFields_givenReverseBound {hLB hcell hsmall hpcIntr hRB : Prop}
    (h1 : hLB) (h2 : hcell) (h3 : hsmall) (h4 : hpcIntr) (h5 : hRB) :
    UpperSmallNResiduals hLB hcell hsmall hpcIntr hRB :=
  upperSmallNResiduals_of_reverseBound h1 h2 h3 h4 h5

end OTSelector.Reconstruction
