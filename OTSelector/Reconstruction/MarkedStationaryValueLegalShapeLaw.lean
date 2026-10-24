import OTSelector.Probability.MarkedShapeLaw
import OTSelector.Reconstruction.MarkedStationaryValueLegalShapeExpectation

/-! Legal pressure comparison directly on the unchanged normalized shape laws. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Exact shape-prefix pressure comparison, formulated directly on the original
normalized spatial restriction laws used by the retained class construction. -/
theorem FiniteScalarBins.integrable_shapeBlockValue_compare_legalPressure
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, source a < target b → |g a b| ≤ G) (t : ℝ) :
    Integrable (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      blockLegalTilted q source target r kin g t d.1 d.2)
      ((shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S)) ∧
    |(∫ d, blockLegalTilted q source target r kin g t d.1 d.2
        ∂(shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S)) -
      legalMarkedPressure q source target α β r kin g t| ≤
      (2 * (r : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + |t| * G)) := by
  let _instA : Nonempty A := nonempty_of_isProbabilityMeasure α
  let _instB : Nonempty B := nonempty_of_isProbabilityMeasure β
  have hb := D.integral_shapeLegalMarkedTilted_sub_le_of_forward hgap q hs ht α β r hS
    hsource hsep hC hG hk hkb hg hgb t
  let F : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) → ℝ :=
    fun d ↦ blockLegalTilted q source target r kin g t d.1 d.2
  have hF : Measurable F := measurable_blockLegalTilted q hs ht r hk hg t
  have hi := hb.1
  unfold shapeLegalMarkedTilted at hi
  have htransfer := shapeCloud_integrable_integral q α β r hS F hF hi
  refine ⟨htransfer.1, ?_⟩
  change |(∫ d, F d ∂(shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S)) - _| ≤ _
  rw [htransfer.2]
  exact hb.2

end OTSelector.Reconstruction
