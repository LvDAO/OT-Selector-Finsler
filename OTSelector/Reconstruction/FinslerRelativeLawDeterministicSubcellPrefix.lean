import OTSelector.Reconstruction.FinslerRelativeLawDeterministicLabelRestriction

/-! Exact original finite prefixes survive deterministic microscopic label truncation. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Prescribed microscopic label truncation changes only the global residual.
On every remaining subcell the unchanged original observation law still gives
its exact normalized point law and original binomial count. The same original
population cost data and original physical iid marginals are retained. -/
theorem PopulationTypedCostData.original_deterministic_subcell_prefix_model_law
    {X Z S U T : Type*} [MetricSpace X] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace S] [MeasurableSpace U] [Fintype T]
    [MeasurableSpace (Option (Bool × T))]
    [MeasurableSingletonClass (Option (Bool × T))]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hπ : Vlasov.IsCoupling (χ + ξ) μ ν)
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (a : X → Z) (ha : Measurable a) (u : X → ℝ) {A : Set X}
    (horder : ∀ x ∈ A, ∀ y ∈ A, (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνA : ∀ᵐ y ∂ν, y ∈ A)
    (hcal : ∀ᵐ p ∂χ + ξ, u p.2 - u p.1 = dist p.1 p.2)
    {G L : Set Z} (hG : MeasurableSet G) (hL : MeasurableSet L) (hsub : L ⊆ G)
    (readS : X → S) (readT : X → U) (hmS : Measurable readS) (hmT : Measurable readT)
    (τS : Measure S) (τT : Measure U) [IsFiniteMeasure τS] [IsFiniteMeasure τT]
    (hτS : 0 < τS.real univ) (hτT : 0 < τT.real univ)
    (hsource : ((χ.map Prod.fst).restrict (a ⁻¹' L)).map readS = τS)
    (htarget : ((χ.map Prod.snd).restrict (a ⁻¹' L)).map readT = τT) (N : ℕ) :
    let ξG := restrictOriginalRetainedResidual χ ξ a G
    let hξG : ξG ≤ χ + ξ := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let R := D.refineSubplan ξG hξG
    let _instS : IsProbabilityMeasure (normalizedFiniteLaw τS) := normalizedFiniteLaw_probability τS hτS
    let _instT : IsProbabilityMeasure (normalizedFiniteLaw τT) := normalizedFiniteLaw_probability τT hτT
    (R.markedLaw N).map (Prod.map
      (fun x ↦ mapBlockData (fun p ↦ readS p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) x))
      (fun y ↦ mapBlockData (fun p ↦ readT p.1) (finiteOriginalRestrictedData (retainedMarkedCellEvent (a ⁻¹' L)) y))) =
      (blockDataLaw (normalizedFiniteLaw τS) (binomWeight N (τS univ).toNNReal)).prod
      (blockDataLaw (normalizedFiniteLaw τT) (binomWeight N (τT univ).toNNReal)) := by
  have hlabel : ∀ᵐ p ∂χ, a p.1 = a p.2 :=
    (original_calibrated_coupling_labels μ ν (χ + ξ) χ hπ (Measure.le_add_right le_rfl)
      a u horder hμA hνA hcal).mono fun p hp ↦ hp.1
  have hs : ((((χ + ξ) - restrictOriginalRetainedResidual χ ξ a G).map Prod.fst).restrict
      (a ⁻¹' L)).map readS = τS := by
    rw [original_retained_label_restriction_complement χ ξ a ha hG,
      original_retained_label_restriction_source χ a ha hG hsub]
    exact hsource
  have ht : ((((χ + ξ) - restrictOriginalRetainedResidual χ ξ a G).map Prod.snd).restrict
      (a ⁻¹' L)).map readT = τT := by
    rw [original_retained_label_restriction_complement χ ξ a ha hG,
      original_retained_label_restriction_target χ a ha hlabel hG hsub]
    exact htarget
  exact D.original_retained_prefix_normalized_model_law hπ
    (restrictOriginalRetainedResidual χ ξ a G) (restrictOriginalRetainedResidual_le χ ξ a ha hG)
    N (ha hL) (ha hL) readS readT hmS hmT τS τT hτS hτT hs ht

end OTSelector.Reconstruction
