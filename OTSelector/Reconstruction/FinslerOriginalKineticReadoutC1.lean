import OTSelector.Reconstruction.FinslerOriginalSeedChartRegularity

/-!
# Concrete kinetic readout C1 from chart coordinates

This module isolates the last regularity input of the mark lane with its exact type:
the concrete seed label readout along the chart parameter is a CONTINUOUS LINEAR
coordinate map of the chart parameter.  Under that identity the C1 statement
`ContDiff ℝ 1 (fun e => C.labelReadout (Φ e))` is immediate (continuous linear maps
are C1), the constant shift is handled by `ContDiff.add contDiff_const`, and the
linear-probe mark-Lipschitz transfer applies.

Residual input, stated exactly: a continuous linear map `L : E →L[ℝ] (Fin (finrank ℝ
ker) → ℝ)` with `∀ e, C.labelReadout (Φ e) = L e` (the seed window chart data:
label coordinates as chart coordinate projections), together with the lane's
pointwise identifications of the actual kin/g with the quadratic/linear readouts.
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
/-- **C1 of the concrete label readout from a continuous linear chart coordinate.**
If the concrete readout along the chart parameter equals a continuous linear map of
the parameter, it is C1. -/
theorem OriginalPopulationCoefficientCore.contDiff_one_labelReadout_comp
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (Φ : E → Z)
    (L : E →L[ℝ] (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ))
    (hlabel : ∀ e : E, C.labelReadout (Φ e) = L e) :
    ContDiff ℝ 1 (fun e : E => C.labelReadout (Φ e)) := by
  have hfun : (fun e : E => C.labelReadout (Φ e)) = fun e => L e := funext hlabel
  rw [hfun]
  exact L.contDiff

omit [BorelSpace E] in
/-- **Concrete kinetic readout C1 with the constant shift.**  The shifted readout
consumed by the mark lane is C1. -/
theorem OriginalPopulationCoefficientCore.contDiff_one_labelReadout_shift
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (Φ : E → Z)
    (L : E →L[ℝ] (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ))
    (hlabel : ∀ e : E, C.labelReadout (Φ e) = L e)
    (c : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) :
    ContDiff ℝ 1 (fun e : E => C.labelReadout (Φ e) + c) :=
  (C.contDiff_one_labelReadout_comp Φ L hlabel).add contDiff_const

omit [BorelSpace E] in
/-- **Mark-Lipschitz constants for the concrete kinetic and linear-probe readouts.**
With the chart-coordinate identity for the concrete seed readout, a continuous
linear chart coordinate map, and the lane's pointwise identifications, the quadratic
kinetic readout and the linear probe have the mark-Lipschitz constants. -/
theorem OriginalPopulationCoefficientCore.hasMarkLipschitzConstantsOn_of_chartLabelReadout
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K) (Φ : E → Z)
    (L : E →L[ℝ] (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ))
    (hlabel : ∀ e : E, C.labelReadout (Φ e) = L e)
    (c b : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) (d : ℝ)
    (A : Matrix (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker))
      (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) ℝ)
    {kin g : E → ℝ}
    (hkin : ∀ e ∈ K, kin e = matrixQuadratic A (C.labelReadout (Φ e) + c))
    (hg : ∀ e ∈ K, g e = linearProbe (fun e : E => C.labelReadout (Φ e)) c b d e) :
    HasMarkLipschitzConstantsOn E K kin g :=
  hasMarkLipschitzConstantsOn_of_linearProbe hK hne hconv
    (fun e : E => C.labelReadout (Φ e)) c b d A
    (C.contDiff_one_labelReadout_comp Φ L hlabel) hkin hg
    (contDiff_one_linearProbe (C.contDiff_one_labelReadout_comp Φ L hlabel) c b d)

end OTSelector.Reconstruction
