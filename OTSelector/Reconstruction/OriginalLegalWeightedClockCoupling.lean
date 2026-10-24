import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryTightCut

/-! A genuine original full stationary matching supplies its own strict clock coupling. -/
open Set Function MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction

/-- The actual Palm of the original matching supplies a probability coupling
of its unchanged clocks. No separate Hall flow or original coupling is needed
when a genuine candidate matching is already available. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalForwardClockCoupling
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      Vlasov.IsCoupling π α β ∧ ∀ᵐ p ∂π, p.1 < p.2 := by
  let := Q.palm_probability
  let π := (legalMarkedJointPalm q Q.law).map Prod.fst
  have hprob : IsProbabilityMeasure π :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  refine ⟨π,hprob,⟨?_,?_⟩,?_⟩
  · change ((legalMarkedJointPalm q Q.law).map Prod.fst).map Prod.fst = α
    rw [Measure.map_map measurable_fst measurable_fst]
    exact Q.source_clock
  · change ((legalMarkedJointPalm q Q.law).map Prod.fst).map Prod.snd = β
    rw [Measure.map_map measurable_snd measurable_fst]
    exact Q.target_clock
  · apply (ae_map_iff measurable_fst.aemeasurable
      (measurableSet_lt measurable_fst measurable_snd)).mpr
    exact Q.ae_palm_forward

end OTSelector.Reconstruction
