import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryWindowLaw

/-!
# Simplicity of arbitrary actual original Poisson-input scenes

Exact original compact Laplace inputs give the original finite marked Poisson
law on every compact restriction. Positive spatial dimension supplies simple
unit atoms. A countable compact exhaustion recovers simplicity of the whole
same-scene input whenever its existing integer carrier is retained.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalOriginalInputSimplicityColorMetric : MetricSpace (Fin 2) :=
  TopologicalSpace.metrizableSpaceMetric (Fin 2)
local instance markedStationaryValueLegalOriginalInputSimplicityInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalOriginalInputSimplicityPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- The actual complete original input is simple for any scene law with the
prescribed compact Poisson field and an actual integer input carrier. Neither
matching fullness nor finite-optimum provenance is assumed. -/
theorem ae_originalInput_simple_of_laplace_of_counting
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hLaplace : ∀ S : ℝ, 0 < S →
      ∀ (F : C_c(LegalColoredInputPoint q, ℝ)) (hF : ∀ x, 0 ≤ F x),
      (∀ (x : LegalMarkedPhysicalPoint q) (c : Fin 2),
        x.1 ∉ haarRootCube (Fin q) S → F (x, c) = 0) →
      (∫ s, legalMarkedInputSceneLaplace q F hF s
        ∂(Q : Measure (LegalMarkedOptimalInputScene q))) =
        ∫ b, legalInputBlockLaplace (fun x ↦ F (x, 0)) (fun x ↦ F (x, 1)) b
          ∂legalInputPoissonWindowLaw q (haarRootCube (Fin q) S) α β)
    (hc : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      IsLegalCountingMeasure (0 : LegalColoredInputPoint q) s.2) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q) s.2 := by
  let K := CompactExhaustion.choice (LegalColoredInputPoint q)
  have hsimple := measurableSet_isLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)
  have hn (n : ℕ) : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      IsLegalSimpleCountingMeasure (0 : LegalColoredInputPoint q)
        (legalInputRestrictionLocal (K n) s.2) := by
    obtain ⟨S, hS, hlaw⟩ := map_inputRestrictionLocal_eq_originalPoisson_of_laplace Q hLaplace (K.isCompact n)
    have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦ legalInputRestrictionLocal (K n) s.2) :=
      (measurable_legalInputRestrictionLocal (K.isCompact n).measurableSet).comp measurable_snd
    apply (ae_map_iff hm.aemeasurable hsimple).mp
    rw [hlaw]
    exact (ae_map_iff ((measurable_legalInputRestrictionLocal (K.isCompact n).measurableSet).comp
      (measurable_legalInputTwoBlockLocal q)).aemeasurable hsimple).mpr
        (ae_isLegalSimpleCountingMeasure_originalPoisson_restriction q hq hS α β (K n))
  filter_upwards [ae_all_iff.mpr hn, hc] with s hs hcount
  apply (isLegalSimpleCountingMeasure_iff (0 : LegalColoredInputPoint q) s.2).mpr
  refine ⟨hcount, fun x ↦ ?_⟩
  obtain ⟨n, hxn⟩ := K.exists_mem x
  have hatom := ((isLegalSimpleCountingMeasure_iff _ _).mp (hs n)).2 x
  change ((s.2 : Measure (LegalColoredInputPoint q)).restrict (K n)) {x} ≤ 1 at hatom
  simpa only [Measure.restrict_apply (measurableSet_singleton x),
    singleton_inter_of_mem hxn] using hatom

end OTSelector.Reconstruction
