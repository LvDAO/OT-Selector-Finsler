import OTSelector.Reconstruction.FinslerOriginalSeedReadoutMatching

/-!
# C1 shifted readout pairing transfer

This module delivers the final composition of the mark lane with the height-slice
pairing identification.  On a height slice the frozen physical cost is
`matrixQuadratic (C.matrix z₀ q) (labelReadout (a y) - labelReadout (a x))`, a
quadratic form of the explicit seed readout SHIFTED by the constant target readout.
Hence the C1 hypothesis of the transfer is exactly
`ContDiff ℝ 1 (fun e => C.labelReadout (Φ e) + c)` for the constant shift `c`.

Both theorems reduce the mark-Lipschitz constants for the actual kin/g to (i) C1 of
the shifted concrete readout along the chart parameter, plus (ii) the pointwise
identifications of the actual kin/g with the quadratic readouts.  The probe is the
same quadratic readout with matrix B; a genuinely linear probe still needs the
dotProduct continuous-linear-map API.
-/

open Set Function Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator NNReal

noncomputable section
namespace OTSelector.Reconstruction

/-- **Shifted C1 readout pairing transfer.**  If the readout shifted by a constant
is C1 and the actual kin/g agree on the compact convex retained-root family with the
frozen quadratic forms of that shifted readout, then kin and g have the
mark-Lipschitz constants. -/
theorem hasMarkLipschitzConstantsOn_of_shiftedReadoutPairing {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K) {n : Type*} [Fintype n]
    (f : E → n → ℝ) (c : n → ℝ) (A B : Matrix n n ℝ) {kin g : E → ℝ}
    (hf : ContDiff ℝ 1 (fun e => f e + c))
    (hkin : ∀ e ∈ K, kin e = matrixQuadratic A (f e + c))
    (hg : ∀ e ∈ K, g e = matrixQuadratic B (f e + c)) :
    HasMarkLipschitzConstantsOn E K kin g :=
  hasMarkLipschitzConstantsOn_of_contDiff_readouts hK hne hconv hf hkin hg

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

omit [BorelSpace E] in
/-- **Concrete label readout pairing transfer.**  The same transfer for the concrete
seed label readout along the chart parameter `Φ`, with constant shift `c` (the
target mark readout on the height slice). -/
theorem OriginalPopulationCoefficientCore.hasMarkLipschitzConstantsOn_of_labelReadoutPairing
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K) (Φ : E → Z)
    (c : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
    (A B : Matrix (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker))
      (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) ℝ)
    {kin g : E → ℝ}
    (hf : ContDiff ℝ 1 (fun e : E => C.labelReadout (Φ e) + c))
    (hkin : ∀ e ∈ K, kin e = matrixQuadratic A (C.labelReadout (Φ e) + c))
    (hg : ∀ e ∈ K, g e = matrixQuadratic B (C.labelReadout (Φ e) + c)) :
    HasMarkLipschitzConstantsOn E K kin g :=
  hasMarkLipschitzConstantsOn_of_shiftedReadoutPairing hK hne hconv
    (fun e => C.labelReadout (Φ e)) c A B hf hkin hg

end OTSelector.Reconstruction
