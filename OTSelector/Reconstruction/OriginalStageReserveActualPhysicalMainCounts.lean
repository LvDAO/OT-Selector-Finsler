import OTSelector.Reconstruction.OriginalStageResidualDensityActualPhysicalWindowArrays
import OTSelector.Reconstruction.OriginalStageResidualDensityExcessEndpoints
import Mathlib.MeasureTheory.Function.Floor

/-! Exact measurable original input counts in the chosen actual physical window. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- A physical-window array representation internally determines the actual two colour
counts of the unchanged original input. -/
theorem IsOriginalStageMainPhysicalWindowArrays.actual_counts {q : ℕ} {K : Set (Fin q → ℝ)}
    {scene : LegalMarkedOptimalInputScene q} {sourceMain targetMain : MarkedCloudSpace q ℝ}
    (h : IsOriginalStageMainPhysicalWindowArrays K scene sourceMain targetMain) :
    (legalInputColorMeasure q scene.2 0).real {p | p.1 ∈ K} = (sourceMain.1 : ℝ) ∧
    (legalInputColorMeasure q scene.2 1).real {p | p.1 ∈ K} = (targetMain.1 : ℝ) := by
  have hs := congrArg (fun π : Measure (LegalMarkedPhysicalPoint q) ↦ π.real univ) h.1
  have ht := congrArg (fun π : Measure (LegalMarkedPhysicalPoint q) ↦ π.real univ) h.2
  rw [originalStageRemainingReserveMeasure_mass, Finset.card_univ, Fintype.card_fin] at hs ht
  simpa only [measureReal_def, Measure.restrict_apply_univ] using And.intro hs ht

/-- The genuine original coloured count is read measurably without choosing an array. -/
def originalStageMainPhysicalWindowCount {q : ℕ} (K : Set (Fin q → ℝ)) (c : Fin 2)
    (scene : LegalMarkedOptimalInputScene q) : ℕ :=
  ⌊(scene.2 : Measure (LegalColoredInputPoint q)).real ((K ×ˢ (univ : Set ℝ)) ×ˢ {c})⌋₊

theorem measurable_originalStageMainPhysicalWindowCount {q : ℕ} {K : Set (Fin q → ℝ)}
    (hK : MeasurableSet K) (c : Fin 2) :
    Measurable (originalStageMainPhysicalWindowCount (q := q) K c) := by
  have hU : MeasurableSet ((K ×ˢ (univ : Set ℝ)) ×ˢ ({c} : Set (Fin 2))) :=
    (hK.prod MeasurableSet.univ).prod (measurableSet_singleton c)
  exact (((Measure.measurable_coe hU).comp
    (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal).nat_floor

/-- The total measurable readout equals the original main-array length on the actual
same-scene integer event, for both colours. -/
theorem IsOriginalStageMainPhysicalWindowArrays.mainWindowCounts {q : ℕ} {K : Set (Fin q → ℝ)}
    {scene : LegalMarkedOptimalInputScene q} {sourceMain targetMain : MarkedCloudSpace q ℝ}
    (h : IsOriginalStageMainPhysicalWindowArrays K scene sourceMain targetMain) (hK : MeasurableSet K) :
    originalStageMainPhysicalWindowCount K 0 scene = sourceMain.1 ∧
    originalStageMainPhysicalWindowCount K 1 scene = targetMain.1 := by
  have hs := h.actual_counts.1
  have ht := h.actual_counts.2
  have hW : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.1 ∈ K} := hK.preimage measurable_fst
  have hcolor (c : Fin 2) : (scene.2 : Measure (LegalColoredInputPoint q)).real ((K ×ˢ univ) ×ˢ {c}) =
      (legalInputColorMeasure q scene.2 c).real {p | p.1 ∈ K} := by
    rw [measureReal_def, measureReal_def, legalInputColorMeasure_apply_prod q _ c hW]
    have he : K ×ˢ (univ : Set ℝ) = {p : LegalMarkedPhysicalPoint q | p.1 ∈ K} := by ext p; simp
    rw [he]
  simp only [originalStageMainPhysicalWindowCount, hcolor, hs, ht, Nat.floor_natCast, and_self]

end OTSelector.Reconstruction
