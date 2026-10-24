import OTSelector.Reconstruction.FinslerOriginalSeedReadoutAffine

/-!
# Concrete population-seed label readout

This module instantiates the abstract affine-readout mark lane of
`FinslerOriginalSeedReadoutAffine` for the CONCRETE population-seed label readout
`z ↦ bW.equivFun (w (a z))` of the coefficient lane.  Since the mark space `Z` is
only a measurable space (not normed), affineness is stated on a normed chart
parameterization `Φ : E → Z` of the retained roots?that is exactly the chart
readout `local_data` of the seed window?so the transfer theorem takes the affine
seed-label structure on the chart parameter and returns the mark-Lipschitz
constants for the concrete frozen quadratic kinetic/probe forms.

Remaining identification inputs (stated, not silently assumed): (i) affineness of
`e ↦ C.populationSeedReadout (Φ e)` on the parameter domain (seed window label
structure on the chart), and (ii) the identification of the probe functional with a
linear/quadratic readout of the label difference.  Given those, the composition
with the mark-pairing identification gives `HasMarkLipschitzConstantsOn` for the
actual kin/g and the mark modulus transfer applies.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator NNReal

noncomputable section
namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The concrete population-seed label readout: the population seed root label
value of the mark in seed basis coordinates. -/
def OriginalPopulationCoefficientCore.populationSeedReadout
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (z : Z) :
    Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ :=
  (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
    (populationSeedRootLabelValue (P C.seedIndex).seed a z)

/-- **Concrete seed readout via a chart parameterization.**  On a normed parameter
domain `E` mapped to the marked points by `Φ`, the concrete seed readout is affine. -/
def OriginalPopulationCoefficientCore.SeedReadoutParameterizedAffineOn
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (Φ : E → Z)
    (K : Set E) : Prop :=
  SeedReadoutAffineOn E K (fun e => C.populationSeedReadout (Φ e))

omit [BorelSpace E] in
/-- **Mark-Lipschitz constants for the concrete frozen quadratic forms.**  If the
concrete population-seed readout is affine on the chart parameter domain, then the
concrete frozen quadratic kinetic and probe forms (quadratic forms of the seed
readout) have the mark-Lipschitz constants, with no Lipschitz constant assumed. -/
theorem OriginalPopulationCoefficientCore.hasMarkLipschitzConstantsOn_of_parameterizedSeedReadoutAffine
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K) (Φ : E → Z)
    (A B : Matrix (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker))
      (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) ℝ)
    (haff : C.SeedReadoutParameterizedAffineOn Φ K) :
    HasMarkLipschitzConstantsOn E K
      (fun e => matrixQuadratic A (C.populationSeedReadout (Φ e)))
      (fun e => matrixQuadratic B (C.populationSeedReadout (Φ e))) := by
  exact hasMarkLipschitzConstantsOn_of_seedReadoutAffine hK hne hconv A B haff haff
    (fun _ _ => rfl) (fun _ _ => rfl)

end OTSelector.Reconstruction
