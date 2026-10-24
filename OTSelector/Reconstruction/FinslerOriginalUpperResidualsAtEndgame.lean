import OTSelector.Reconstruction.FinslerOriginalUpperSmallNFieldInventory

/-!
# Upper/small-n residuals at the endgame

Integration of the four-field constructor with the endgame interface:

* `upperSmallNResiduals_of_onRadiusData` — the endgame-shaped constructor: from the
  four Props `hLB hcell hsmall hpcIntr` and `UpperPoolReverseBoundOnRadius` at the
  endgame's `pc`/`consolidatedStationaryDatum`/`radius` (with `0 < m`), produces
  `∃ pc'` agreeing with `pc` on `|t| < radius f` and the bundle at `pc'`.
* `upperSmallNResiduals_onRadius_of_bundle` — the converse extraction: the full
  reverse-bound field of an assembled bundle implies the on-radius reverse bound at
  the same pool (definitionally, by restricting to `|t| < radius f`).

Note on consuming the bundle at the endgame: `UpperPoolReverseBound q m pc' datum`
is `∀ f t, (datum f).I2 t ≤ endgameUpperPressure_actual q m pc' f t`, a statement
about ALL `t`; the extension `pc'` differs from `pc` only off the radius interval, so
the only V16 call-site condition to check is that the endgame readout uses pool
values at the on-radius points `|t| < radius f` (otherwise the `pc'`-modified pool
must be substituted consistently in `hLB`/`hpcIntr` as well).
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

/-- **Endgame-shaped constructor.**  The four fields plus the on-radius reverse bound
(at the endgame `pc`, datum and radius) give the bundle, with a pool extension that
agrees with `pc` on the perturbation interval. -/
theorem upperSmallNResiduals_of_onRadiusData {hm : 0 < m}
    {radius : FinalRadiusField A B}
    (hon : UpperPoolReverseBoundOnRadius q m pc datum radius)
    {hLB hcell hsmall hpcIntr : Prop} (h1 : hLB) (h2 : hcell) (h3 : hsmall)
    (h4 : hpcIntr) :
    ∃ pc' : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ,
      (∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m),
        |t| < radius f → pc' f t c = pc f t c) ∧
      UpperSmallNResiduals hLB hcell hsmall hpcIntr (UpperPoolReverseBound q m pc' datum) :=
  upperSmallNResiduals_of_fourFields (hm := hm) hon h1 h2 h3 h4

/-- **Converse extraction.**  The full reverse-bound field of an assembled bundle
restricts to the on-radius reverse bound at the same pool and radius. -/
theorem upperSmallNResiduals_onRadius_of_bundle {hLB hcell hsmall hpcIntr : Prop}
    (b : UpperSmallNResiduals hLB hcell hsmall hpcIntr
      (UpperPoolReverseBound q m pc datum))
    (radius : FinalRadiusField A B) :
    UpperPoolReverseBoundOnRadius q m pc datum radius := by
  intro f t _
  exact b.reverseBound f t

end OTSelector.Reconstruction