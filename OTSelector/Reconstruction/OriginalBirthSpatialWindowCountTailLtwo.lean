import OTSelector.Reconstruction.BirthSpatialClockWindowIntensity
import OTSelector.Reconstruction.OriginalCountTailOnEventCompletePathAELtwo

/-! Literal product-window original input counts control bounded-phase birth
traffic tails at either endpoint. The physical Haar/density cancellation is
internal, and the matching mark law is never replaced by a Poisson law. -/
open Set Matrix MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The exact original source count in the same deterministic birth spatial
window and original clock band gives the actual small-event traffic tail. -/
theorem exists_original_source_birthSpatialWindow_countTail_completePath_ltwo_ae_on
    {q : ℕ} {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    (hq : 0 < q) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β],
    ∀ {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ},
    ∀ (M : LegalWeightedStationaryPoissonMatching q α β kin g),
    ∀ {t s Kmass : ℝ}, 0 < t → t ≤ 1 → 0 < s → s ≤ t → 0 ≤ Kmass →
    ∀ {A : Set ℝ}, MeasurableSet A →
      α A ≤ ENNReal.ofReal (Kmass * t ^ G.rank * s) →
    ∀ (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ), Measurable d →
    ∀ {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞},
      Measurable h → Measurable f →
    ∀ {Small : Set (LegalMarkedOptimalInputScene q)}, MeasurableSet Small →
    ∀ (V : LegalMarkedOptimalInputScene q → Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))),
      (∀ z, MeasurableSet (V z)) → ∀ {B₀ K : ℝ}, 0 ≤ B₀ →
    let W := birthTrafficSpatialWindow G t s R ×ˢ A
    let N := fun z : LegalMarkedOptimalInputScene q ↦
      ((z.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})).toReal
    let T := Small.indicator (fun z : LegalMarkedOptimalInputScene q ↦
      (legalMarkedCompletePathTraffic q d h f z).toReal)
    (∀ᵐ z ∂(M.law : Measure (LegalMarkedOptimalInputScene q)), z ∈ Small → K < N z →
      (∀ᵐ a ∂physicalScenePairKernel z.1, a ∉ V z →
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0) ∧
      (∀ᵐ a ∂(physicalScenePairKernel z.1).restrict (V z),
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ ENNReal.ofReal B₀) ∧
      physicalScenePairKernel z.1 (V z) ≤
        (z.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})) →
    MemLp ({z | K < N z}.indicator T) 2 (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ z, ({y | K < N y}.indicator T z) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        8 * B₀ ^ 2 * Real.exp ((C * Kmass) * (Real.exp 1 - 1)) * Real.exp (-K / 2) ∧
      eLpNorm ({z | K < N z}.indicator T) 2
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt 8 * B₀ *
          Real.exp ((C * Kmass) * (Real.exp 1 - 1) / 2) * Real.exp (-K / 4)) := by
  obtain ⟨C, hC, hi⟩ := exists_birthSpatialClockWindow_intensity_bound hG hq R
  refine ⟨C, hC, fun {α β} _ _ {kin g} M {t s Kmass} ht ht1 hs hst hKm
    {A} hA hmass d hd {h f} hh hf {Small} hSmall V hV {B₀ K} hB₀ ↦ ?_⟩
  dsimp only
  intro hdata
  have hW := (isCompact_birthTrafficSpatialWindow G t s R).measurableSet.prod hA
  have hb := hi α ht ht1 hs hKm hA hmass
  have hWmass : ((volume : Measure (Fin q → ℝ)).prod α)
      (birthTrafficSpatialWindow G t s R ×ˢ A) ≤ ENNReal.ofReal (C * Kmass) := by
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    have hratio : s / t ≤ 1 := (div_le_one ht).mpr hst
    nlinarith [mul_nonneg hC.le hKm]
  exact M.original_source_countTail_completePath_ltwo_ae_on d hd hh hf hW (by positivity)
    hWmass hSmall V hV hB₀ hdata

/-- The exact original target count in the same deterministic birth spatial
window and original clock band gives the actual small-event traffic tail. -/
theorem exists_original_target_birthSpatialWindow_countTail_completePath_ltwo_ae_on
    {q : ℕ} {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    (hq : 0 < q) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β],
    ∀ {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ},
    ∀ (M : LegalWeightedStationaryPoissonMatching q α β kin g),
    ∀ {t s Kmass : ℝ}, 0 < t → t ≤ 1 → 0 < s → s ≤ t → 0 ≤ Kmass →
    ∀ {A : Set ℝ}, MeasurableSet A →
      β A ≤ ENNReal.ofReal (Kmass * t ^ G.rank * s) →
    ∀ (d : PhysicalPairPalmMark (Fin q) × ℝ → Fin q → ℝ), Measurable d →
    ∀ {h : (Fin q → ℝ) → ℝ≥0∞} {f : PhysicalPairPalmMark (Fin q) × ℝ → ℝ≥0∞},
      Measurable h → Measurable f →
    ∀ {Small : Set (LegalMarkedOptimalInputScene q)}, MeasurableSet Small →
    ∀ (V : LegalMarkedOptimalInputScene q → Set ((Fin q → ℝ) × PhysicalPairPalmMark (Fin q))),
      (∀ z, MeasurableSet (V z)) → ∀ {B₀ K : ℝ}, 0 ≤ B₀ →
    let W := birthTrafficSpatialWindow G t s R ×ˢ A
    let N := fun z : LegalMarkedOptimalInputScene q ↦
      ((z.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})).toReal
    let T := Small.indicator (fun z : LegalMarkedOptimalInputScene q ↦
      (legalMarkedCompletePathTraffic q d h f z).toReal)
    (∀ᵐ z ∂(M.law : Measure (LegalMarkedOptimalInputScene q)), z ∈ Small → K < N z →
      (∀ᵐ a ∂physicalScenePairKernel z.1, a ∉ V z →
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) = 0) ∧
      (∀ᵐ a ∂(physicalScenePairKernel z.1).restrict (V z),
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ ENNReal.ofReal B₀) ∧
      physicalScenePairKernel z.1 (V z) ≤
        (z.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})) →
    MemLp ({z | K < N z}.indicator T) 2 (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ z, ({y | K < N y}.indicator T z) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        8 * B₀ ^ 2 * Real.exp ((C * Kmass) * (Real.exp 1 - 1)) * Real.exp (-K / 2) ∧
      eLpNorm ({z | K < N z}.indicator T) 2
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt 8 * B₀ *
          Real.exp ((C * Kmass) * (Real.exp 1 - 1) / 2) * Real.exp (-K / 4)) := by
  obtain ⟨C, hC, hi⟩ := exists_birthSpatialClockWindow_intensity_bound hG hq R
  refine ⟨C, hC, fun {α β} _ _ {kin g} M {t s Kmass} ht ht1 hs hst hKm
    {A} hA hmass d hd {h f} hh hf {Small} hSmall V hV {B₀ K} hB₀ ↦ ?_⟩
  dsimp only
  intro hdata
  have hW := (isCompact_birthTrafficSpatialWindow G t s R).measurableSet.prod hA
  have hb := hi β ht ht1 hs hKm hA hmass
  have hWmass : ((volume : Measure (Fin q → ℝ)).prod β)
      (birthTrafficSpatialWindow G t s R ×ˢ A) ≤ ENNReal.ofReal (C * Kmass) := by
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    have hratio : s / t ≤ 1 := (div_le_one ht).mpr hst
    nlinarith [mul_nonneg hC.le hKm]
  exact M.original_target_countTail_completePath_ltwo_ae_on d hd hh hf hW (by positivity)
    hWmass hSmall V hV hB₀ hdata

end OTSelector.Reconstruction
