import OTSelector.Reconstruction.FinslerOriginalSeedReadoutProducers
import OTSelector.Reconstruction.FinslerOriginalKinPairingIdentification

/-!
# Height-slice pairing identification of the frozen physical cost

This module packages the height-slice pairing identification of
`FinslerOriginalKinPairingIdentification` in the exact readout form consumed by the
mark-Lipschitz lane: on a fixed height slice `(u x, u y) = q` the frozen physical
cost is the fixed coefficient quadratic form `C.matrix z₀ q` evaluated at the
DIFFERENCE of the Φ or label readout at the two marked points.

`labelReadout` is the readout `bW.equivFun (populationSeedRootLabelValue …)`; it
agrees definitionally with the concrete `populationSeedReadout` of
`FinslerOriginalSeedReadoutConcrete`, so the factorization below is the pointwise
`kin e = matrixQuadratic A (f e)` input of
`hasMarkLipschitzConstantsOn_of_contDiff_readouts` once the mark pair is represented
by the source readout (the target readout enters as an affine shift, absorbed by
the affine/C1 readout hypothesis).

Remaining named inputs are listed in the module doc of the calling assembly: C1 (or
affine) of the concrete readout along the chart parameter Φ, and the probe readout
identification.
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

/-- The label readout of a mark: seed-basis coordinates of the population seed root
label value. -/
def OriginalPopulationCoefficientCore.labelReadout
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (z : Z) :
    Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ :=
  (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
    (populationSeedRootLabelValue (P C.seedIndex).seed a z)

omit [BorelSpace E] in
/-- The concrete population seed readout is the label readout. -/
theorem OriginalPopulationCoefficientCore.populationSeedReadout_eq_labelReadout
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (z : Z) :
    C.populationSeedReadout z = C.labelReadout z := rfl

omit [BorelSpace E] in
/-- **Height-slice pairing identification as a readout-difference quadratic form.**
On the height slice `(u x, u y) = q` the frozen physical cost is the fixed
coefficient quadratic form of the difference of the two label readouts. -/
theorem OriginalPopulationCoefficientCore.frozenPhysicalCost_heightSlice_as_readoutDifference
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (z₀ : Z) (x y : M)
    (q : ℝ × ℝ) (hq : (u x, u y) = q) :
    C.frozenPhysicalCost z₀ x y =
      matrixQuadratic (C.matrix z₀ q) (C.labelReadout (a y) - C.labelReadout (a x)) := by
  rw [C.frozenPhysicalCost_heightSlice z₀ x y q hq]
  simp only [OriginalPopulationCoefficientCore.labelReadout, map_sub]

end OTSelector.Reconstruction