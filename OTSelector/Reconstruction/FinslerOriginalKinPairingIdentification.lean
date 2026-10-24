import OTSelector.Reconstruction.FinslerFiniteTilePressure
import OTSelector.Reconstruction.FinslerOriginalKinIdentification

/-!
# Mark-pairing identification of the frozen physical cost

This module carries out the mark-pairing identification left in
`FinslerOriginalKinIdentification`.  The frozen physical cost `frozenPhysicalCost`
uses the coefficient matrix at the HEIGHT PAIR `(u x, u y)` of the two marked
points and the seed label difference of the two marks.  Along the mark pairing
(two-mark readout: the label difference `w (a y) - w (a x)`, with a fixed height
slice `(u x, u y) = q`) the cost is therefore definitionally the quadratic form
`matrixQuadratic (C.matrix z₀ q)` evaluated at the label-difference readout.

The two theorems below record this factorization exactly as it arises in the
coefficient lane.  The only remaining identification input is the affineness of
the seed label readout on the retained root family (mark ↦ `w (a ·)` linear up to a
constant, which is the seed window structure), together with the corresponding
identification of the probe functional; given those, the mark-pairing
identification feeds `hasMarkLipschitzConstantsOn_of_eqOn_affine_quadratic_readouts`
and hence the mark modulus transfer.
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

omit [BorelSpace E] in
/-- **Mark-pairing factorization of the frozen physical cost.**  The frozen cost is
the height-pair coefficient quadratic form evaluated at the seed label-difference
readout of the two marks. -/
theorem OriginalPopulationCoefficientCore.frozenPhysicalCost_pairingReadout
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (z₀ : Z) (x y : M) :
    C.frozenPhysicalCost z₀ x y =
      matrixQuadratic (C.matrix z₀ (u x, u y))
        ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
          (populationSeedRootLabelValue (P C.seedIndex).seed a (a y) -
            populationSeedRootLabelValue (P C.seedIndex).seed a (a x))) := rfl

omit [BorelSpace E] in
/-- **Fixed height slice.**  On the height slice `(u x, u y) = q` the coefficient
matrix is the fixed `C.matrix z₀ q`, so the frozen cost is the fixed quadratic
form of the mark-pairing label-difference readout. -/
theorem OriginalPopulationCoefficientCore.frozenPhysicalCost_heightSlice
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (z₀ : Z) (x y : M)
    (q : ℝ × ℝ) (hq : (u x, u y) = q) :
    C.frozenPhysicalCost z₀ x y =
      matrixQuadratic (C.matrix z₀ q)
        ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
          (populationSeedRootLabelValue (P C.seedIndex).seed a (a y) -
            populationSeedRootLabelValue (P C.seedIndex).seed a (a x))) := by
  rw [C.frozenPhysicalCost_pairingReadout z₀ x y, hq]

omit [BorelSpace E] in
/-- **Mark-pairing identification, packaged.**  The frozen cost equals the fixed
height-slice quadratic form of the pairing label readout; this is the equality
consumed by the affine quadratic readout transfer. -/
theorem OriginalPopulationCoefficientCore.frozenPhysicalCost_pairing_identification
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (z₀ : Z) (x y : M)
    (q : ℝ × ℝ) (hq : (u x, u y) = q) :
    C.frozenPhysicalCost z₀ x y =
        matrixQuadratic (C.matrix z₀ q)
          ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
            (populationSeedRootLabelValue (P C.seedIndex).seed a (a y) -
              populationSeedRootLabelValue (P C.seedIndex).seed a (a x))) ∧
      matrixQuadratic (C.matrix z₀ (u x, u y))
          ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
            (populationSeedRootLabelValue (P C.seedIndex).seed a (a y) -
              populationSeedRootLabelValue (P C.seedIndex).seed a (a x))) =
        matrixQuadratic (C.matrix z₀ q)
          ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
            (populationSeedRootLabelValue (P C.seedIndex).seed a (a y) -
              populationSeedRootLabelValue (P C.seedIndex).seed a (a x))) := by
  constructor
  · exact C.frozenPhysicalCost_heightSlice z₀ x y q hq
  · rw [hq]

end OTSelector.Reconstruction