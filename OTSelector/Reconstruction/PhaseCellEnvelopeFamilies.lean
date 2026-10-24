import OTSelector.Reconstruction.MarkedPhaseSourceCellVolume
import Mathlib.Data.Fintype.BigOperators

/-!
# Original source envelopes for finite coded phase-cell families

Marked phase-cell volumes are independent of their deterministic centers.
Every finite union therefore has its original intensity bounded by its number
of cells times one original determinant-envelope intensity.
-/
open Set Function Matrix MeasureTheory
open scoped ENNReal Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

/-- The original-input envelope for finitely many deterministic phase cells. -/
def phaseCellEnvelopeFamily (L : Matrix ι ι ℝ) (U : ℝ → Matrix ι ι ℝ)
    (c : J → ℝ → (ι → ℝ)) (B : Set ℝ) (R : ℝ) : Set ((ι → ℝ) × ℝ) :=
  ⋃ j, markedPhaseSourceCell L U (c j) B R

/-- A finite deterministic phase family is a fixed Borel original-input set. -/
theorem measurableSet_phaseCellEnvelopeFamily
    (L : Matrix ι ι ℝ) {U : ℝ → Matrix ι ι ℝ} (hU : Measurable U)
    {c : J → ℝ → (ι → ℝ)} (hc : ∀ j, Measurable (c j))
    {B : Set ℝ} (hB : MeasurableSet B) (R : ℝ) :
    MeasurableSet (phaseCellEnvelopeFamily L U c B R) :=
  MeasurableSet.iUnion (fun j ↦ measurableSet_markedPhaseSourceCell L hU (hc j) hB R)

/-- The true original cell intensity is independent of its deterministic marked center. -/
theorem prod_volume_markedPhaseSourceCell_eq_center_zero
    {L : Matrix ι ι ℝ} (hL : IsUnit L.det) {U : ℝ → Matrix ι ι ℝ}
    (hUm : Measurable U) (hU : ∀ a, (U a).PosSemidef)
    {c : ℝ → (ι → ℝ)} (hc : Measurable c) {B : Set ℝ} (hB : MeasurableSet B)
    (μ : Measure ℝ) [SFinite μ] (R : ℝ) :
    ((volume : Measure (ι → ℝ)).prod μ) (markedPhaseSourceCell L U c B R) =
      ((volume : Measure (ι → ℝ)).prod μ) (markedPhaseSourceCell L U 0 B R) := by
  rw [prod_volume_markedPhaseSourceCell hL hUm hU hc hB μ R,
    prod_volume_markedPhaseSourceCell (c := (0 : ℝ → (ι → ℝ)))
      hL hUm hU measurable_const hB μ R]

/-- Every finite family has at most its actual number of cells times one original cell intensity.
Overlaps between cells and dependence between their original counts require no correction. -/
theorem prod_volume_phaseCellEnvelopeFamily_le
    {L : Matrix ι ι ℝ} (hL : IsUnit L.det) {U : ℝ → Matrix ι ι ℝ}
    (hUm : Measurable U) (hU : ∀ a, (U a).PosSemidef)
    {c : J → ℝ → (ι → ℝ)} (hc : ∀ j, Measurable (c j)) {B : Set ℝ} (hB : MeasurableSet B)
    (μ : Measure ℝ) [SFinite μ] (R : ℝ) :
    ((volume : Measure (ι → ℝ)).prod μ) (phaseCellEnvelopeFamily L U c B R) ≤
      (Fintype.card J : ℝ≥0∞) *
        ((volume : Measure (ι → ℝ)).prod μ) (markedPhaseSourceCell L U 0 B R) := by
  apply (measure_iUnion_fintype_le _ _).trans
  simp_rw [prod_volume_markedPhaseSourceCell_eq_center_zero hL hUm hU (hc _) hB μ R]
  simp

/-- Finite original phase-cell intensity is retained by every finite coded union. -/
theorem prod_volume_phaseCellEnvelopeFamily_lt_top
    {L : Matrix ι ι ℝ} (hL : IsUnit L.det) {U : ℝ → Matrix ι ι ℝ}
    (hUm : Measurable U) (hU : ∀ a, (U a).PosSemidef)
    {c : J → ℝ → (ι → ℝ)} (hc : ∀ j, Measurable (c j)) {B : Set ℝ} (hB : MeasurableSet B)
    (μ : Measure ℝ) [SFinite μ] (R : ℝ)
    (hfin : ((volume : Measure (ι → ℝ)).prod μ) (markedPhaseSourceCell L U 0 B R) < ∞) :
    ((volume : Measure (ι → ℝ)).prod μ) (phaseCellEnvelopeFamily L U c B R) < ∞ :=
  (prod_volume_phaseCellEnvelopeFamily_le hL hUm hU hc hB μ R).trans_lt
    (ENNReal.mul_lt_top (by simp) hfin)

end OTSelector.Reconstruction
