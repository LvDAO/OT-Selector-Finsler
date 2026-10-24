import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryPoissonCandidate
import OTSelector.MeasureTheory.LocalFiniteMeasureCompactness
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests

/-! Compact original edge readouts are dominated by compact immutable input readouts. -/
open Set Function MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- A compact test equal to one on the actual source projection bounds the
whole signed edge observation using the same complete original input marginal. -/
theorem abs_original_edgeTest_le_inputTest
    (q : ℕ) (s : LegalMarkedOptimalInputScene q) (hs : IsFullOriginalInputMatching q s)
    (H : C_c(LegalMarkedPhysicalEdge q, ℝ))
    (η : C_c(LegalColoredInputPoint q, ℝ)) (hη : ∀ x, 0 ≤ η x)
    (hηone : ∀ e ∈ tsupport H, η (e.1, 0) = 1) :
    |LocalFiniteMeasure.testIntegral s.1.1 H| ≤
      ‖H.toBoundedContinuousFunction‖ * LocalFiniteMeasure.testIntegral s.2 η := by
  let K : Set (LegalMarkedPhysicalPoint q) := Prod.fst '' tsupport H
  let K0 : Set (LegalColoredInputPoint q) := K ×ˢ {(0 : Fin 2)}
  have hK : IsCompact K := H.hasCompactSupport.image continuous_fst
  have hK0 : IsCompact K0 := hK.prod isCompact_singleton
  have hfinite : (s.2 : Measure (LegalColoredInputPoint q)) K0 ≠ ∞ := hK0.measure_ne_top
  have hmass : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (tsupport H) ≤
      (s.2 : Measure (LegalColoredInputPoint q)) K0 := by
    calc
      _ ≤ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (Prod.fst ⁻¹' K) :=
        measure_mono (fun e he ↦ ⟨e, he, rfl⟩)
      _ = (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst K := by
        rw [Measure.fst, Measure.map_apply measurable_fst hK.measurableSet]
      _ = legalInputColorMeasure q s.2 0 K := by rw [hs.source_marginal]
      _ = _ := by
        rw [legalInputColorMeasure, Measure.map_apply measurable_fst hK.measurableSet,
          Measure.restrict_apply (hK.measurableSet.preimage measurable_fst)]
        congr 1
  have hηK0 : ∀ x ∈ K0, η x = 1 := by
    rintro ⟨x, c⟩ ⟨hx, hc⟩
    have hc0 : c = 0 := hc
    subst c
    obtain ⟨e, he, rfl⟩ := hx
    exact hηone e he
  have hmassRead : (s.2 : Measure (LegalColoredInputPoint q)).real K0 ≤
      LocalFiniteMeasure.testIntegral s.2 η := by
    have hI : Integrable (K0.indicator (fun _ : LegalColoredInputPoint q ↦ (1 : ℝ)))
        (s.2 : Measure (LegalColoredInputPoint q)) :=
      (integrable_indicator_iff hK0.measurableSet).mpr (integrableOn_const hfinite)
    have hle := integral_mono hI η.integrable (fun x ↦ ?_)
    · simpa only [integral_indicator_const _ hK0.measurableSet, smul_eq_mul, mul_one,
        LocalFiniteMeasure.testIntegral] using hle
    · by_cases hx : x ∈ K0
      · rw [indicator_of_mem hx, hηK0 x hx]
      · rw [indicator_of_notMem hx]
        exact hη x
  let C : ℝ≥0 := ((s.2 : Measure (LegalColoredInputPoint q)) K0).toNNReal
  have hbound : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) (tsupport H) ≤ C := by
    simpa only [C, ENNReal.coe_toNNReal hfinite] using hmass
  have htest := LocalFiniteMeasure.abs_testIntegral_le_localMass s.1.1 H
    (Subset.refl (tsupport H)) hbound
  exact htest.trans (mul_le_mul_of_nonneg_left hmassRead (norm_nonneg _))

/-- The original compact edge test supplies its own nonnegative compact input
majorant. Its choice depends on the test, before any scene law or sample. -/
theorem exists_original_edgeTest_input_majorant
    (q : ℕ) (H : C_c(LegalMarkedPhysicalEdge q, ℝ)) :
    ∃ η : C_c(LegalColoredInputPoint q, ℝ), (∀ x, 0 ≤ η x) ∧
      ∀ s : LegalMarkedOptimalInputScene q, IsFullOriginalInputMatching q s →
        |LocalFiniteMeasure.testIntegral s.1.1 H| ≤
          ‖H.toBoundedContinuousFunction‖ * LocalFiniteMeasure.testIntegral s.2 η := by
  let K : Set (LegalMarkedPhysicalPoint q) := Prod.fst '' tsupport H
  have hK : IsCompact K := H.hasCompactSupport.image continuous_fst
  obtain ⟨η, hηone, hη⟩ := LocalFiniteMeasure.exists_compact_cutoff
    (hK.prod (isCompact_singleton (x := (0 : Fin 2))))
  refine ⟨η, fun x ↦ (hη x).1, fun s hs ↦ ?_⟩
  apply abs_original_edgeTest_le_inputTest q s hs H η (fun x ↦ (hη x).1)
  intro e he
  exact hηone ⟨⟨e, he, rfl⟩, rfl⟩

end OTSelector.Reconstruction
