import OTSelector.Reconstruction.MarkedStationaryValueLegalShapeLaw

/-! One original shape tolerance controls a whole bounded tilt interval, after
fixing the microscopic scale and before choosing any measurable shape. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Normalized finite shape-law pressure, using its unchanged original
conditional spatial laws, has an error uniform over a bounded tilt interval. -/
theorem FiniteScalarBins.normalized_shapeBlockValue_sub_le_on_tilt
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (hr : 0 < (r : ℝ))
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, source a < target b → |g a b| ≤ G)
    {T : ℝ} (hT : 0 ≤ T) {S : Set (Fin q → ℝ)} (hS : MeasurableSet S)
    {t : ℝ} (htilt : |t| ≤ T) :
    Integrable (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
      blockLegalTilted q source target r kin g t d.1 d.2)
      ((shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S)) ∧
    |(∫ d, blockLegalTilted q source target r kin g t d.1 d.2
        ∂(shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S)) / (r : ℝ) -
      legalMarkedPressure q source target α β r kin g t / (r : ℝ)| ≤
      (2 * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + T * G)) := by
  obtain ⟨hInt, hbound⟩ := D.integrable_shapeBlockValue_compare_legalPressure hgap q hs ht
    α β r hS hsource hsep hC hG hk hkb hg hgb t
  refine ⟨hInt, ?_⟩
  rw [← sub_div, abs_div, abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  refine hbound.trans ?_
  have htiltG : |t| * G ≤ T * G := mul_le_mul_of_nonneg_right htilt hG
  calc
    _ ≤ (2 * (r : ℝ) * ((cubeMeasure (Fin q) 1) Sᶜ).toReal) *
        (2 * ((D.count : ℝ) + 1) *
          ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + T * G)) := by
      gcongr
    _ = _ := by ring

/-- The same hole tolerance works for every measurable shape and every tilt in
[-T,T]. No geometric regularity or nonempty interior of the shape is assumed. -/
theorem FiniteScalarBins.exists_uniform_shapeBlockValue_tolerance_on_tilt
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    (q : ℕ) {source : A → ℝ} {target : B → ℝ}
    (hs : Measurable source) (ht : Measurable target)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (r : ℝ≥0) (hr : 0 < (r : ℝ))
    (hsource : ∀ᵐ a ∂α, source a ∈ I)
    (hsep : ∀ᵐ p ∂α.prod β, gap ≤ |target p.2 - source p.1|)
    {C G : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : A × B ↦ kin p.1 p.2)))
    (hkb : ∀ a b, source a < target b → ∀ v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    {g : A → B → ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀ a b, source a < target b → |g a b| ≤ G)
    {T : ℝ} (hT : 0 ≤ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Set (Fin q → ℝ), MeasurableSet S →
      ((cubeMeasure (Fin q) 1) Sᶜ).toReal ≤ δ → ∀ t : ℝ, |t| ≤ T →
      Integrable (fun d : BlockData ((Fin q → ℝ) × A) × BlockData ((Fin q → ℝ) × B) ↦
        blockLegalTilted q source target r kin g t d.1 d.2)
        ((shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S)) ∧
      |(∫ d, blockLegalTilted q source target r kin g t d.1 d.2
          ∂(shapeBlockLaw q α r S).prod (shapeBlockLaw q β r S)) / (r : ℝ) -
        legalMarkedPressure q source target α β r kin g t / (r : ℝ)| < ε := by
  let K := 2 * ((D.count : ℝ) + 1) *
    ((r : ℝ) ^ (2 / (q : ℝ)) * (C * q) + T * G)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let δ := ε / (2 * K + 1)
  have hden : 0 < 2 * K + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  refine ⟨δ, hδ, fun S hS hholes t htilt ↦ ?_⟩
  obtain ⟨hInt, hbound⟩ := D.normalized_shapeBlockValue_sub_le_on_tilt hgap q hs ht
    α β r hr hsource hsep hC hG hk hkb hg hgb hT hS htilt
  refine ⟨hInt, hbound.trans_lt ?_⟩
  have htol : 2 * δ * K < ε := by
    have heq : δ * (2 * K + 1) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hholes (by norm_num : (0 : ℝ) ≤ 2)) hK).trans_lt htol

end OTSelector.Reconstruction
