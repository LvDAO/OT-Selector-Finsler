import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryReserveInput
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryClockShiftMatching

/-!
# The actual dilated retained plan has exactly the original unused reserve

Dilation preserves the entire genuine integer matching. After actual original
input superposition, its two whole endpoint marginals have the independently
dilated reserve as their exact unused complement. No selected port process is
assigned a probability law.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalStationaryReserveCoreColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance markedStationaryValueLegalStationaryReserveCoreInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryReserveCorePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Whole immutable-color marginals commute with actual measure addition. -/
theorem legalInputColorMeasure_localFiniteMeasureSum (q : ℕ)
    (μ ν : LocalFiniteMeasure (LegalColoredInputPoint q)) (k : Fin 2) :
    legalInputColorMeasure q (legalLocalFiniteMeasureSum (μ, ν)) k =
      legalInputColorMeasure q μ k + legalInputColorMeasure q ν k := by
  unfold legalInputColorMeasure
  change (((μ : Measure (LegalColoredInputPoint q)) + ν).restrict {x | x.2 = k}).map Prod.fst = _
  rw [Measure.restrict_add, Measure.map_add _ _ measurable_fst]

/-- The actual colored input dilation pushes each unchanged original color
by the same original physical point homeomorphism. -/
theorem legalInputColorMeasure_dilation (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (μ : LocalFiniteMeasure (LegalColoredInputPoint q)) (k : Fin 2) :
    legalInputColorMeasure q (localFiniteMapHomeomorph (legalColoredInputDilation q c hc) μ) k =
      (legalInputColorMeasure q μ k).map (legalMarkedPointDilation q c hc) := by
  have hC : MeasurableSet {x : LegalColoredInputPoint q | x.2 = k} :=
    measurable_snd (measurableSet_singleton k)
  have hpre : legalColoredInputDilation q c hc ⁻¹' {x | x.2 = k} = {x | x.2 = k} := rfl
  unfold legalInputColorMeasure
  rw [coe_localFiniteMapHomeomorph,
    Measure.restrict_map (legalColoredInputDilation q c hc).continuous.measurable hC, hpre,
    Measure.map_map measurable_fst (legalColoredInputDilation q c hc).continuous.measurable,
    Measure.map_map (legalMarkedPointDilation q c hc).continuous.measurable measurable_fst]
  rfl

/-- Both complete original endpoint marginals undergo the actual dilation. -/
theorem marginals_map_legalMarkedEdgeDilation (q : ℕ) (c : ℝ) (hc : c ≠ 0)
    (μ : Measure (LegalMarkedPhysicalEdge q)) :
    (μ.map (legalMarkedEdgeDilation q c hc)).fst =
        μ.fst.map (legalMarkedPointDilation q c hc) ∧
      (μ.map (legalMarkedEdgeDilation q c hc)).snd =
        μ.snd.map (legalMarkedPointDilation q c hc) := by
  constructor
  · change (μ.map (legalMarkedEdgeDilation q c hc)).map Prod.fst =
      (μ.map Prod.fst).map (legalMarkedPointDilation q c hc)
    rw [Measure.map_map measurable_fst (legalMarkedEdgeDilation q c hc).continuous.measurable,
      Measure.map_map (legalMarkedPointDilation q c hc).continuous.measurable measurable_fst]
    rfl
  · change (μ.map (legalMarkedEdgeDilation q c hc)).map Prod.snd =
      (μ.map Prod.snd).map (legalMarkedPointDilation q c hc)
    rw [Measure.map_map measurable_snd (legalMarkedEdgeDilation q c hc).continuous.measurable,
      Measure.map_map (legalMarkedPointDilation q c hc).continuous.measurable measurable_snd]
    rfl

/-- The same actual full integer matching survives physical dilation. -/
theorem IsFullOriginalInputMatching.dilation {q : ℕ} {s : LegalMarkedOptimalInputScene q}
    (hs : IsFullOriginalInputMatching q s) (c : ℝ) (hc : c ≠ 0) :
    IsFullOriginalInputMatching q (legalMarkedInputSceneDilation q c hc s) := by
  apply isFullOriginalInputMatching_of_counting_simple_marginals
  · exact isLegalCountingMeasure_mapHomeomorph _ _ _
      ((isLegalSimpleCountingMeasure_iff _ _).mp hs.simple_edges).1
  · exact isLegalSimpleCountingMeasure_mapHomeomorph _ _ _ hs.simple_inputs
  · constructor
    · change ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map (legalMarkedEdgeDilation q c hc)).fst =
        legalInputColorMeasure q (localFiniteMapHomeomorph (legalColoredInputDilation q c hc) s.2) 0
      rw [(marginals_map_legalMarkedEdgeDilation q c hc _).1, hs.source_marginal,
        legalInputColorMeasure_dilation]
    · change ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map (legalMarkedEdgeDilation q c hc)).snd =
        legalInputColorMeasure q (localFiniteMapHomeomorph (legalColoredInputDilation q c hc) s.2) 1
      rw [(marginals_map_legalMarkedEdgeDilation q c hc _).2, hs.target_marginal,
        legalInputColorMeasure_dilation]

/-- The exact unused input complement is the second original copy, for any
actual retained full matching. This identity precedes port selection. -/
theorem IsFullOriginalInputMatching.reserve_input_exact_marginals
    {q : ℕ} {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (r : LegalMarkedOptimalInputScene q) :
    legalInputColorMeasure q (legalMarkedReserveInputScene q (s, r)).2 0 =
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst + legalInputColorMeasure q r.2 0 ∧
      legalInputColorMeasure q (legalMarkedReserveInputScene q (s, r)).2 1 =
        (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd + legalInputColorMeasure q r.2 1 := by
  constructor
  · change legalInputColorMeasure q (legalLocalFiniteMeasureSum (s.2, r.2)) 0 = _
    rw [legalInputColorMeasure_localFiniteMeasureSum, hs.source_marginal]
  · change legalInputColorMeasure q (legalLocalFiniteMeasureSum (s.2, r.2)) 1 = _
    rw [legalInputColorMeasure_localFiniteMeasureSum, hs.target_marginal]

/-- The retained original plan is an actual simple one-to-one integer core
inside the superposed input. Its whole marginal deficits are exactly the
unchanged independent reserve colors, even after unequal physical dilations. -/
theorem LegalWeightedStationaryPoissonMatching.ae_original_dilated_reserve_core
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    ∀ᵐ p ∂((M.law : Measure (LegalMarkedOptimalInputScene q)).prod
        (N.law : Measure (LegalMarkedOptimalInputScene q))),
      let s := legalMarkedInputSceneDilation q c hc p.1
      let r := legalMarkedInputSceneDilation q d hd p.2
      IsFullOriginalInputMatching q s ∧ IsFullOriginalInputMatching q r ∧
        legalInputColorMeasure q (legalMarkedReserveInputScene q (s, r)).2 0 =
          (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).fst + legalInputColorMeasure q r.2 0 ∧
        legalInputColorMeasure q (legalMarkedReserveInputScene q (s, r)).2 1 =
          (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).snd + legalInputColorMeasure q r.2 1 := by
  filter_upwards [ae_fst_of_ae M.full_matching, ae_snd_of_ae N.full_matching] with p hp hq
  have hs := hp.dilation c hc
  have hr := hq.dilation d hd
  exact ⟨hs, hr, hs.reserve_input_exact_marginals _⟩

end OTSelector.Reconstruction
