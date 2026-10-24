import OTSelector.Reconstruction.OriginalStageResidualDensityFiniteCountingArray
import OTSelector.Reconstruction.OriginalActualInputBoundaryLawTransfer
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowColors

/-! The same full original scene produces original arrays on every compact physical window. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

local instance actualPhysicalWindowArraysColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

/-- These are representations of precisely the original colored spatial-window measures;
positions, clocks and their original multiplicities are preserved. -/
def IsOriginalStageMainPhysicalWindowArrays {q : ℕ} (K : Set (Fin q → ℝ)) (scene : LegalMarkedOptimalInputScene q)
    (sourceMain targetMain : MarkedCloudSpace q ℝ) : Prop :=
  (legalInputColorMeasure q scene.2 0).restrict {p | p.1 ∈ K} =
      originalStageRemainingReserveMeasure sourceMain Finset.univ ∧
  (legalInputColorMeasure q scene.2 1).restrict {p | p.1 ∈ K} =
      originalStageRemainingReserveMeasure targetMain Finset.univ

/-- A genuine original integer scene and its actual finite spatial window yield an array for
each color. This supplies the actual main arrays used by mark/index excess removal. -/
theorem LegalWeightedStationaryPoissonMatching.ae_exists_originalStageMainPhysicalWindowArrays
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (K : Set (Fin q → ℝ)) (hK : IsCompact K) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∃ sourceMain targetMain : MarkedCloudSpace q ℝ,
        IsOriginalStageMainPhysicalWindowArrays K scene sourceMain targetMain := by
  filter_upwards [Q.full_matching, Q.ae_finite_fullSpatialInput (K := K) hK] with scene hfull hfinite
  have hcolor (c : Fin 2) : ∃ z : MarkedCloudSpace q ℝ,
      (legalInputColorMeasure q scene.2 c).restrict {p | p.1 ∈ K} =
        originalStageRemainingReserveMeasure z Finset.univ := by
    let U : Set (LegalColoredInputPoint q) := (K ×ˢ univ) ×ˢ {c}
    let ρ : LocalFiniteMeasure (LegalColoredInputPoint q) :=
      ⟨(scene.2 : Measure (LegalColoredInputPoint q)).restrict U, inferInstance⟩
    have hρcount : IsLegalCountingMeasure (0 : LegalColoredInputPoint q) ρ :=
      isLegalCountingMeasure_restrict _ scene.2
        ((isLegalSimpleCountingMeasure_iff _ _).mp hfull.simple_inputs).1 U
    have hρfinite : (ρ : Measure (LegalColoredInputPoint q)) univ < ∞ := by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono (by
        intro x hx
        exact ⟨hx.1, mem_univ _⟩)) hfinite
    obtain ⟨n, points, hpoints⟩ := exists_originalFiniteCountingArray _ ρ hρcount hρfinite
    apply exists_originalFiniteMarkedCloud
    refine ⟨n, fun i ↦ (points i).1, ?_⟩
    have hmap : (legalInputColorMeasure q scene.2 c).restrict {p | p.1 ∈ K} =
        (ρ : Measure (LegalColoredInputPoint q)).map Prod.fst := by
      ext V hV
      have hwindow : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.1 ∈ K} :=
        hK.measurableSet.preimage measurable_fst
      rw [Measure.restrict_apply hV, legalInputColorMeasure_apply_prod q scene.2 c
          (hV.inter hwindow),
        Measure.map_apply measurable_fst hV,
        Measure.restrict_apply (hV.preimage measurable_fst)]
      congr 1
      ext x
      simp only [U, mem_prod, mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_univ,
        and_true, mem_singleton_iff]
      tauto
    rw [hmap, hpoints, Measure.map_finset_sum measurable_fst.aemeasurable]
    simp only [Measure.map_dirac]
  obtain ⟨sourceMain, hs⟩ := hcolor 0
  obtain ⟨targetMain, ht⟩ := hcolor 1
  exact ⟨sourceMain, targetMain, hs, ht⟩

end OTSelector.Reconstruction
