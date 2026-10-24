import OTSelector.Reconstruction.BirthBandOriginalPhaseIntensity
import OTSelector.Reconstruction.OriginalInputFiniteCountMean

/-! Literal original source and target birth-band counts in the canonical physical
frame. Their mean is O(s/t), and their full original Poisson exponential bound
uses that same intensity. The matched or subsequently selected edges are not
assigned a new Poisson law. -/
open Set Function Matrix MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The unchanged original source input has finite birth-band counts with
mean and exponential estimates at the physical scale `s/t`. -/
theorem exists_original_source_birthBand_count_estimates
    {q : ℕ} {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    (hq : 0 < q) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β],
      ∀ {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ},
      ∀ (M : LegalWeightedStationaryPoissonMatching q α β kin g),
      ∀ {t s D K : ℝ}, 0 < t → t ≤ 1 → 0 < s → 0 ≤ D → 0 ≤ K →
      ∀ {U : ℝ → Matrix (Fin q) (Fin q) ℝ}, Measurable U → (∀ a, (U a).PosSemidef) →
      ∀ {c : ℝ → (Fin q → ℝ)}, Measurable c → ∀ {B : Set ℝ}, MeasurableSet B →
      (∀ a ∈ B, (1 + U a).det ≤ D) → α B ≤ ENNReal.ofReal (K * t ^ G.rank * s) →
      let V := markedPhaseSourceCell (birthTrafficSpatialFrame G t s) U c B R
      let N := fun z : LegalMarkedOptimalInputScene q ↦
        ((z.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {0})).toReal
      (∀ᵐ z ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
        (z.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {0}) < ∞) ∧
      Integrable N (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ z, N z ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤ C * D * K * (s / t) ∧
      ∀ u : ℝ, 0 ≤ u →
        Integrable (fun z ↦ Real.exp (u * N z))
          (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
        (∫ z, Real.exp (u * N z) ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
          Real.exp ((C * D * K * (s / t)) * (Real.exp u - 1)) := by
  obtain ⟨C, hC, hbound⟩ := exists_birthBand_original_phaseCell_intensity_bound hG
    (by simpa using hq) R
  refine ⟨C, hC, fun {α β} _ _ {kin g} M {t s D K} ht ht1 hs hD hK {U} hUm hU
    {c} hc {B} hB hdet hmass ↦ ?_⟩
  dsimp only
  have hV := measurableSet_markedPhaseSourceCell (birthTrafficSpatialFrame G t s) hUm hc hB R
  have hb := hbound α ht ht1 hs hD hK hUm hU hc hB hdet hmass
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hnonneg : 0 ≤ C * D * K * (s / t) := by positivity
  have hreal : (((volume : Measure (Fin q → ℝ)).prod α)
      (markedPhaseSourceCell (birthTrafficSpatialFrame G t s) U c B R)).toReal ≤
      C * D * K * (s / t) := by
    simpa only [ENNReal.toReal_ofReal hnonneg] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  obtain ⟨hi, hmean⟩ := M.original_source_count_integrable_and_integral hV hfin
  refine ⟨(M.original_source_exp_moment_of_finite_intensity hV hfin
    (t := 0) (by norm_num)).1, hi, hmean.le.trans hreal, ?_⟩
  intro u hu
  obtain ⟨_, hI, hExp⟩ := M.original_source_exp_moment_of_finite_intensity hV hfin hu
  refine ⟨hI, hExp.trans (Real.exp_le_exp.mpr ?_)⟩
  exact mul_le_mul_of_nonneg_right hreal (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hu))

/-- The unchanged original target input has finite birth-band counts with
mean and exponential estimates at the physical scale `s/t`. -/
theorem exists_original_target_birthBand_count_estimates
    {q : ℕ} {G : Matrix (Fin q) (Fin q) ℝ} (hG : G.PosSemidef)
    (hq : 0 < q) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β],
      ∀ {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ},
      ∀ (M : LegalWeightedStationaryPoissonMatching q α β kin g),
      ∀ {t s D K : ℝ}, 0 < t → t ≤ 1 → 0 < s → 0 ≤ D → 0 ≤ K →
      ∀ {U : ℝ → Matrix (Fin q) (Fin q) ℝ}, Measurable U → (∀ a, (U a).PosSemidef) →
      ∀ {c : ℝ → (Fin q → ℝ)}, Measurable c → ∀ {B : Set ℝ}, MeasurableSet B →
      (∀ a ∈ B, (1 + U a).det ≤ D) → β B ≤ ENNReal.ofReal (K * t ^ G.rank * s) →
      let V := markedPhaseSourceCell (birthTrafficSpatialFrame G t s) U c B R
      let N := fun z : LegalMarkedOptimalInputScene q ↦
        ((z.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {1})).toReal
      (∀ᵐ z ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
        (z.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {1}) < ∞) ∧
      Integrable N (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ z, N z ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤ C * D * K * (s / t) ∧
      ∀ u : ℝ, 0 ≤ u →
        Integrable (fun z ↦ Real.exp (u * N z))
          (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
        (∫ z, Real.exp (u * N z) ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
          Real.exp ((C * D * K * (s / t)) * (Real.exp u - 1)) := by
  obtain ⟨C, hC, hbound⟩ := exists_birthBand_original_phaseCell_intensity_bound hG
    (by simpa using hq) R
  refine ⟨C, hC, fun {α β} _ _ {kin g} M {t s D K} ht ht1 hs hD hK {U} hUm hU
    {c} hc {B} hB hdet hmass ↦ ?_⟩
  dsimp only
  have hV := measurableSet_markedPhaseSourceCell (birthTrafficSpatialFrame G t s) hUm hc hB R
  have hb := hbound β ht ht1 hs hD hK hUm hU hc hB hdet hmass
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hnonneg : 0 ≤ C * D * K * (s / t) := by positivity
  have hreal : (((volume : Measure (Fin q → ℝ)).prod β)
      (markedPhaseSourceCell (birthTrafficSpatialFrame G t s) U c B R)).toReal ≤
      C * D * K * (s / t) := by
    simpa only [ENNReal.toReal_ofReal hnonneg] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  obtain ⟨hi, hmean⟩ := M.original_target_count_integrable_and_integral hV hfin
  refine ⟨(M.original_target_exp_moment_of_finite_intensity hV hfin
    (t := 0) (by norm_num)).1, hi, hmean.le.trans hreal, ?_⟩
  intro u hu
  obtain ⟨_, hI, hExp⟩ := M.original_target_exp_moment_of_finite_intensity hV hfin hu
  refine ⟨hI, hExp.trans (Real.exp_le_exp.mpr ?_)⟩
  exact mul_le_mul_of_nonneg_right hreal (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hu))

end OTSelector.Reconstruction
