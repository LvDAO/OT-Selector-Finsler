import OTSelector.Reconstruction.OriginalReserveMappedWindowJoining

/-! The reserve-only joining can be multiplied by the unchanged independent original main scene. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- A single experiment retains both the independent original whole scenes and
exactly the main-scene/cube-sampler marginal used by marks-only reserve deletion.
The whole reserve identity witness does not enter that sampler marginal's auxiliary data. -/
theorem LegalWeightedStationaryPoissonMatching.exists_originalReserve_fullMappedWindow_mainExperiment_joining
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (N : LegalWeightedStationaryPoissonMatching q α β kin g)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    {F : (Fin q → ℝ) → (Fin q → ℝ)} (hF : Measurable F)
    (hpoint : (cubeMeasure (Fin q) 1).map F =
      normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K))
    {A : Set ℝ} (hA : IsCompact A) (hα : α.support ⊆ A) (hβ : β.support ⊆ A) :
    ∃ L : ProbabilityMeasure (LegalMarkedOptimalInputScene q ×
        (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)),
      (L : Measure (LegalMarkedOptimalInputScene q ×
        (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ))).map (fun p ↦ (p.1, p.2.1)) =
        (Q : Measure (LegalMarkedOptimalInputScene q)).prod (N.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (L : Measure (LegalMarkedOptimalInputScene q ×
        (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ))).map (fun p ↦ (p.1, p.2.2)) =
        (Q : Measure (LegalMarkedOptimalInputScene q)).prod (twoMarkedCloudLaw q ℝ ℝ α β (volume K).toNNReal) ∧
      ∀ᵐ p ∂(L : Measure (LegalMarkedOptimalInputScene q ×
        (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ))),
        (p.2.1.2 : Measure (LegalColoredInputPoint q)).restrict
          ((Prod.fst ∘ Prod.fst) ⁻¹' K) =
            legalInputTwoBlockMeasure q (originalMappedReserveCloudArrays q F p.2.2) := by
  obtain ⟨J, hleft, hright, heq⟩ := N.exists_originalReserve_fullMappedWindow_joining
    hK hKpos hF hpoint hA hα hβ
  let L : ProbabilityMeasure (LegalMarkedOptimalInputScene q ×
      (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)) :=
    ⟨(Q : Measure (LegalMarkedOptimalInputScene q)).prod (J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ)), inferInstance⟩
  refine ⟨L, ?_, ?_, ?_⟩
  · change ((Q : Measure (LegalMarkedOptimalInputScene q)).prod (J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ))).map (Prod.map id Prod.fst) = _
    rw [← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id, hleft]
  · change ((Q : Measure (LegalMarkedOptimalInputScene q)).prod (J : Measure (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ))).map (Prod.map id Prod.snd) = _
    rw [← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id, hright]
  · exact ae_snd_of_ae heq

end OTSelector.Reconstruction
