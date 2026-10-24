import OTSelector.Reconstruction.FinslerOriginalKineticReadoutC1

/-!
# Seed chart identification: named residual input and its C1 consequence

This module names, with its exact type, the last structural input of the mark lane
and proves everything downstream of it: the concrete seed label readout along the
chart parameter `Φ` is a continuous linear coordinate map of the parameter.  The
predicate `LabelReadoutChartLinear C Φ` is exactly that statement; from it the C1 of
the readout (with constant shift) and the mark-Lipschitz constants for the concrete
kinetic and linear-probe readouts follow unconditionally.

Residual input, exact type: `LabelReadoutChartLinear C Φ`, i.e. existence of
`L : E →L[ℝ] (Fin (finrank ℝ ker) → ℝ)` with `∀ e, C.labelReadout (Φ e) = L e`.
This must be produced from the seed window chart data (`populationSeedRootLabelValue`,
seed basis, chart label map) — the definitional identification of the label readout
with chart coordinate projections.
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

/-- Named residual structural input: on the chart parameter `Φ` the concrete seed
label readout is a continuous linear coordinate map. -/
def OriginalPopulationCoefficientCore.LabelReadoutChartLinear
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (Φ : E → Z) : Prop :=
  ∃ L : E →L[ℝ] (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ),
    ∀ e : E, C.labelReadout (Φ e) = L e

omit [BorelSpace E] in
/-- The exact connective form of the named input. -/
theorem OriginalPopulationCoefficientCore.labelReadoutChartLinear_iff
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (Φ : E → Z) :
    C.LabelReadoutChartLinear Φ ↔
      ∃ L : E →L[ℝ] (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ),
        ∀ e : E, C.labelReadout (Φ e) = L e := Iff.rfl

omit [BorelSpace E] in
/-- From the chart-coordinate identity the concrete label readout is C1. -/
theorem OriginalPopulationCoefficientCore.contDiff_one_labelReadout_of_chartLinear
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) (Φ : E → Z)
    (h : C.LabelReadoutChartLinear Φ) :
    ContDiff ℝ 1 (fun e : E => C.labelReadout (Φ e)) := by
  obtain ⟨L, hlabel⟩ := h
  exact C.contDiff_one_labelReadout_comp Φ L hlabel

omit [BorelSpace E] in
/-- **Concrete mark-Lipschitz constants from the named chart input.**  With the
chart-coordinate identity and the lane's pointwise identifications, the concrete
kinetic and linear-probe readouts have the mark-Lipschitz constants. -/
theorem OriginalPopulationCoefficientCore.hasMarkLipschitzConstantsOn_of_chartLinearData
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ) {K : Set E}
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K) (Φ : E → Z)
    (hlin : C.LabelReadoutChartLinear Φ)
    (c b : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) (d : ℝ)
    (A : Matrix (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker))
      (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) ℝ)
    {kin g : E → ℝ}
    (hkin : ∀ e ∈ K, kin e = matrixQuadratic A (C.labelReadout (Φ e) + c))
    (hg : ∀ e ∈ K, g e = linearProbe (fun e : E => C.labelReadout (Φ e)) c b d e) :
    HasMarkLipschitzConstantsOn E K kin g := by
  obtain ⟨L, hlabel⟩ := hlin
  exact C.hasMarkLipschitzConstantsOn_of_chartLabelReadout hK hne hconv Φ L hlabel c b d A
    hkin hg

end OTSelector.Reconstruction
