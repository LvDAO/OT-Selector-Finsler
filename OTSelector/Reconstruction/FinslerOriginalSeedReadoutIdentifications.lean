import OTSelector.Reconstruction.FinslerOriginalMarkModulusTransfer

/-!
# Seed readout identifications

This module sharpens the three named inputs of
`FinslerOriginalMarkModulusTransfer` into their exact analytic forms and records the
direct composition with the mark modulus transfer.

`SeedReadoutParameterizedAffineOn` is reduced to its explicit existentials (the
chart parameter form consumed by the transfer theorem), and the mark-Lipschitz
constants for the actual kin/g are derived directly from the three identification
inputs.  The remaining analytic work is exactly: (i) producing those existentials
from the seed window chart data (the population seed labels being linear coordinates
on the chart parameter Φ), (ii) the height-slice pairing identification of the
actual frozenPhysicalCost-based kin/g with the quadratic readouts, and (iii) the
probe readout identification.  No other input is needed for the mark modulus
transfer.
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
/-- Explicit form of the concrete seed readout affineness input: on the chart
parameter domain `K` the concrete readout is a continuous linear label coordinate
plus a constant seed offset. -/
theorem OriginalPopulationCoefficientCore.seedReadoutParameterizedAffineOn_iff
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (Φ : E → Z)
    (K : Set E) :
    C.SeedReadoutParameterizedAffineOn Φ K ↔
      ∃ (L : E →L[ℝ]
          (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ))
        (c : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ),
        ∀ e ∈ K, C.populationSeedReadout (Φ e) = L e + c := Iff.rfl

omit [BorelSpace E] in
/-- **Direct composition with the mark modulus transfer.**  The three identification
inputs (concrete seed readout affine on the chart parameter, and the two pointwise
identifications of the actual kin and g with the concrete frozen quadratic readouts
on the retained roots) give the mark-Lipschitz constants for the actual kin/g. -/
theorem OriginalPopulationCoefficientCore.hasMarkLipschitzConstantsOn_of_seedReadoutIdentifications
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K) (Φ : E → Z)
    (A B : Matrix (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker))
      (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) ℝ)
    {kin g : E → ℝ}
    (haff : C.SeedReadoutParameterizedAffineOn Φ K)
    (hkin : ∀ e ∈ K, kin e = matrixQuadratic A (C.populationSeedReadout (Φ e)))
    (hg : ∀ e ∈ K, g e = matrixQuadratic B (C.populationSeedReadout (Φ e))) :
    HasMarkLipschitzConstantsOn E K kin g :=
  C.hasMarkLipschitzConstantsOn_of_frozenMarkPairingIdentification hK hne hconv Φ A B
    haff hkin hg

end OTSelector.Reconstruction
