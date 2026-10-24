import OTSelector.Reconstruction.FinslerOriginalUpperResidualsAtEndgame

/-!
# Upper/small-n residuals from pressure data

Final reduction of the V9 residual bundle: the reverse-bound field is produced from
the paper's pressure estimates (`upperPoolReverseBoundOnRadius_of_pressure_data`) and
then fed to the four-field constructor (`upperSmallNResiduals_of_onRadiusData`).
The resulting variant has residual list `hLB`, `hcell`, `hsmall`, `hpcIntr` plus the
pressure-data hypotheses; `hRB` is gone (absorbed into the produced on-radius bound
and the off-radius convention).
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

/-- **Bundle from the pressure data.**  The exact binder list of
`upperPoolReverseBoundOnRadius_of_pressure_data` (FinslerOriginalUpperPoolReverseBound
line 396) produces the on-radius reverse bound, which the four-field constructor
turns into the V9 bundle (with the off-radius pool extension `pc'`). -/
theorem upperSmallNResiduals_of_pressureData
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Fin (n + 1) → Ω n → M}
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hφ : let _instPressureComparison : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    {pressureLower : FinalPressureField A B}
    {radius : FinalRadiusField A B}
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hL : LowerStationaryReadout pressureLower datum)
    (hscreen : StationaryScreening datum)
    (hm : 0 < m)
    {hLB hcell hsmall hpcIntr : Prop} (h1 : hLB) (h2 : hcell) (h3 : hsmall)
    (h4 : hpcIntr) :
    ∃ pc' : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ,
      (∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m),
        |t| < radius f → pc' f t c = pc f t c) ∧
      UpperSmallNResiduals hLB hcell hsmall hpcIntr (UpperPoolReverseBound q m pc' datum) :=
  upperSmallNResiduals_of_onRadiusData (hm := hm)
    (upperPoolReverseBoundOnRadius_of_pressure_data hA hB hμA hνB
      hcomplete hX hY hXlaw hYlaw hφ hLoc hprob hL hscreen)
    h1 h2 h3 h4

/-- **Bundle from pressure data, given the reverse bound already at hand.**  When the
on-radius bound at some pool `pc'` is available (e.g. produced by the pressure-data
theorem elsewhere), assemble the bundle directly. -/
theorem upperSmallNResiduals_of_pressureData_givenBound
    {radius : FinalRadiusField A B}
    (hon : UpperPoolReverseBoundOnRadius q m pc datum radius) (hm : 0 < m)
    {hLB hcell hsmall hpcIntr : Prop} (h1 : hLB) (h2 : hcell) (h3 : hsmall)
    (h4 : hpcIntr) :
    ∃ pc' : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ,
      (∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m),
        |t| < radius f → pc' f t c = pc f t c) ∧
      UpperSmallNResiduals hLB hcell hsmall hpcIntr (UpperPoolReverseBound q m pc' datum) :=
  upperSmallNResiduals_of_onRadiusData (hm := hm) hon h1 h2 h3 h4

end OTSelector.Reconstruction
