import OTSelector.Reconstruction.OriginalInputCountTailTrafficLtwo
import OTSelector.Reconstruction.BirthBandOriginalPhaseIntensity

/-! Original birth-frame count tails have a uniform exponential L2 estimate.
The actual Haar Jacobian and same-residue density shell cancel before applying
the unchanged two-color Poisson input exponential moment. -/
open Set Matrix MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A bounded-phase source traffic tail is exponentially small under its own
full original input count; the intensity is uniformly bounded when `s ≤ t`. -/
theorem exists_original_source_birthBand_countTail_traffic_ltwo
    {q : ℕ} {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    (hq : 0 < q) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β],
      ∀ {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ},
      ∀ (M : LegalWeightedStationaryPoissonMatching q α β kin g),
      ∀ {t s D A : ℝ}, 0 < t → t ≤ 1 → 0 < s → s ≤ t → 0 ≤ D → 0 ≤ A →
      ∀ {U : ℝ → Matrix (Fin q) (Fin q) ℝ}, Measurable U → (∀ a, (U a).PosSemidef) →
      ∀ {c : ℝ → (Fin q → ℝ)}, Measurable c → ∀ {B : Set ℝ}, MeasurableSet B →
      (∀ a ∈ B, (1 + U a).det ≤ D) → α B ≤ ENNReal.ofReal (A * t ^ G.rank * s) →
      ∀ {T : LegalMarkedOptimalInputScene q → ℝ},
      AEStronglyMeasurable T (M.law : Measure (LegalMarkedOptimalInputScene q)) →
      ∀ {B₀ K : ℝ}, 0 ≤ B₀ →
      let V := markedPhaseSourceCell (birthTrafficSpatialFrame G t s) U c B R
      let N := fun z : LegalMarkedOptimalInputScene q ↦
        ((z.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {0})).toReal
      (∀ᵐ z ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
        K < N z → |T z| ≤ B₀ * N z) →
      MemLp ({z | K < N z}.indicator T) 2
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ z, ({w | K < N w}.indicator T z) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
          8 * B₀ ^ 2 * Real.exp ((C * D * A) * (Real.exp 1 - 1)) * Real.exp (-K / 2) ∧
      eLpNorm ({z | K < N z}.indicator T) 2
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt 8 * B₀ *
          Real.exp ((C * D * A) * (Real.exp 1 - 1) / 2) * Real.exp (-K / 4)) := by
  obtain ⟨C, hC, hi⟩ := exists_birthBand_original_phaseCell_intensity_bound hG
    (by simpa using hq) R
  refine ⟨C, hC, fun {α β} _ _ {kin g} M {t s D A} ht ht1 hs hst hD hA
    {U} hUm hU {c} hc {B} hB hdet hmass {T} hT {B₀ K} hB₀ ↦ ?_⟩
  dsimp only
  intro hbound
  have hV := measurableSet_markedPhaseSourceCell (birthTrafficSpatialFrame G t s) hUm hc hB R
  have hv := hi α ht ht1 hs hD hA hUm hU hc hB hdet hmass
  have hmass' : ((volume : Measure (Fin q → ℝ)).prod α)
      (markedPhaseSourceCell (birthTrafficSpatialFrame G t s) U c B R) ≤
        ENNReal.ofReal (C * D * A) := by
    apply hv.trans
    apply ENNReal.ofReal_le_ofReal
    have hratio : s / t ≤ 1 := (div_le_one ht).mpr hst
    nlinarith [mul_nonneg (mul_nonneg hC.le hD) hA]
  exact M.original_source_countTail_traffic_ltwo hV (by positivity) hmass' hT hB₀ hbound

/-- A bounded-phase target traffic tail is exponentially small under its own
full original input count; the intensity is uniformly bounded when `s ≤ t`. -/
theorem exists_original_target_birthBand_countTail_traffic_ltwo
    {q : ℕ} {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    (hq : 0 < q) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β],
      ∀ {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ},
      ∀ (M : LegalWeightedStationaryPoissonMatching q α β kin g),
      ∀ {t s D A : ℝ}, 0 < t → t ≤ 1 → 0 < s → s ≤ t → 0 ≤ D → 0 ≤ A →
      ∀ {U : ℝ → Matrix (Fin q) (Fin q) ℝ}, Measurable U → (∀ a, (U a).PosSemidef) →
      ∀ {c : ℝ → (Fin q → ℝ)}, Measurable c → ∀ {B : Set ℝ}, MeasurableSet B →
      (∀ a ∈ B, (1 + U a).det ≤ D) → β B ≤ ENNReal.ofReal (A * t ^ G.rank * s) →
      ∀ {T : LegalMarkedOptimalInputScene q → ℝ},
      AEStronglyMeasurable T (M.law : Measure (LegalMarkedOptimalInputScene q)) →
      ∀ {B₀ K : ℝ}, 0 ≤ B₀ →
      let V := markedPhaseSourceCell (birthTrafficSpatialFrame G t s) U c B R
      let N := fun z : LegalMarkedOptimalInputScene q ↦
        ((z.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {1})).toReal
      (∀ᵐ z ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
        K < N z → |T z| ≤ B₀ * N z) →
      MemLp ({z | K < N z}.indicator T) 2
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ z, ({w | K < N w}.indicator T z) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
          8 * B₀ ^ 2 * Real.exp ((C * D * A) * (Real.exp 1 - 1)) * Real.exp (-K / 2) ∧
      eLpNorm ({z | K < N z}.indicator T) 2
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt 8 * B₀ *
          Real.exp ((C * D * A) * (Real.exp 1 - 1) / 2) * Real.exp (-K / 4)) := by
  obtain ⟨C, hC, hi⟩ := exists_birthBand_original_phaseCell_intensity_bound hG
    (by simpa using hq) R
  refine ⟨C, hC, fun {α β} _ _ {kin g} M {t s D A} ht ht1 hs hst hD hA
    {U} hUm hU {c} hc {B} hB hdet hmass {T} hT {B₀ K} hB₀ ↦ ?_⟩
  dsimp only
  intro hbound
  have hV := measurableSet_markedPhaseSourceCell (birthTrafficSpatialFrame G t s) hUm hc hB R
  have hv := hi β ht ht1 hs hD hA hUm hU hc hB hdet hmass
  have hmass' : ((volume : Measure (Fin q → ℝ)).prod β)
      (markedPhaseSourceCell (birthTrafficSpatialFrame G t s) U c B R) ≤
        ENNReal.ofReal (C * D * A) := by
    apply hv.trans
    apply ENNReal.ofReal_le_ofReal
    have hratio : s / t ≤ 1 := (div_le_one ht).mpr hst
    nlinarith [mul_nonneg (mul_nonneg hC.le hD) hA]
  exact M.original_target_countTail_traffic_ltwo hV (by positivity) hmass' hT hB₀ hbound

end OTSelector.Reconstruction
