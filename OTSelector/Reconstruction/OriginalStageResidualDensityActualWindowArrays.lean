import OTSelector.Reconstruction.OriginalStageResidualDensityFiniteCountingArray
import OTSelector.Reconstruction.OriginalActualInputBoundaryLawTransfer
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowColors

/-! The same full original scene produces finite original arrays on the actual physical cube. -/
open Set Function Filter MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Probability

local instance actualWindowArraysColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)

/-- These are representations of precisely the original colored spatial-window measures;
positions, clocks and their original multiplicities are preserved. -/
def IsOriginalStageMainWindowArrays {q : ℕ} (R : ℝ) (scene : LegalMarkedOptimalInputScene q)
    (sourceMain targetMain : MarkedCloudSpace q ℝ) : Prop :=
  (legalInputColorMeasure q scene.2 0).restrict {p | p.1 ∈ haarRootCube (Fin q) R} =
      originalStageRemainingReserveMeasure sourceMain Finset.univ ∧
  (legalInputColorMeasure q scene.2 1).restrict {p | p.1 ∈ haarRootCube (Fin q) R} =
      originalStageRemainingReserveMeasure targetMain Finset.univ

/-- A genuine original integer scene and its actual finite spatial window yield an array for
each color. This supplies the actual main arrays used by mark/index excess removal. -/
theorem LegalWeightedStationaryPoissonMatching.ae_exists_originalStageMainWindowArrays
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (R : ℝ) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∃ sourceMain targetMain : MarkedCloudSpace q ℝ,
        IsOriginalStageMainWindowArrays R scene sourceMain targetMain := by
  filter_upwards [Q.full_matching, Q.ae_finite_fullSpatialInput (K := haarRootCube (Fin q) R)
    isCompact_Icc] with scene hfull hfinite
  have hcolor (c : Fin 2) : ∃ z : MarkedCloudSpace q ℝ,
      (legalInputColorMeasure q scene.2 c).restrict {p | p.1 ∈ haarRootCube (Fin q) R} =
        originalStageRemainingReserveMeasure z Finset.univ := by
    let U : Set (LegalColoredInputPoint q) := (haarRootCube (Fin q) R ×ˢ univ) ×ˢ {c}
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
    have hmap : (legalInputColorMeasure q scene.2 c).restrict {p | p.1 ∈ haarRootCube (Fin q) R} =
        (ρ : Measure (LegalColoredInputPoint q)).map Prod.fst := by
      ext V hV
      have hwindow : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.1 ∈ haarRootCube (Fin q) R} :=
        measurableSet_Icc.preimage measurable_fst
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
