import OTSelector.Probability.ExponentialTailSecondMoment
import OTSelector.Reconstruction.OriginalStationaryFiniteIntensityCounts

/-! Exponentially small L2 count tails for the unchanged original colored input.
No probability law is assigned to a selected matching edge or adaptive port. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Original source input counts control every measurable traffic readout that
is bounded by a fixed multiple of that same count on its count-tail event. -/
theorem LegalWeightedStationaryPoissonMatching.original_source_countTail_traffic_ltwo
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {W : Set (LegalMarkedPhysicalPoint q)} (hW : MeasurableSet W)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hmass : ((volume : Measure (Fin q → ℝ)).prod α) W ≤ ENNReal.ofReal Λ)
    {T : LegalMarkedOptimalInputScene q → ℝ}
    (hT : AEStronglyMeasurable T (M.law : Measure (LegalMarkedOptimalInputScene q)))
    {B K : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      K < ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})).toReal →
      |T s| ≤ B * ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})).toReal) :
    let N := fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})).toReal
    MemLp ({s | K < N s}.indicator T) 2 (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ({z | K < N z}.indicator T s) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        8 * B ^ 2 * Real.exp (Λ * (Real.exp 1 - 1)) * Real.exp (-K / 2) ∧
      eLpNorm ({s | K < N s}.indicator T) 2
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt 8 * B *
          Real.exp (Λ * (Real.exp 1 - 1) / 2) * Real.exp (-K / 4)) := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hreal : (((volume : Measure (Fin q → ℝ)).prod α) W).toReal ≤ Λ := by
    simpa only [ENNReal.toReal_ofReal hΛ] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  obtain ⟨_, hExp, hExpBound⟩ :=
    M.original_source_exp_moment_of_finite_intensity hW hfin (t := 1) (by norm_num)
  simp only [one_mul] at hExp hExpBound
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})).toReal) :=
    ((Measure.measurable_coe (hW.prod (measurableSet_singleton (0 : Fin 2)))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal
  have hexp : (∫ s, Real.exp
      (((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {0})).toReal)
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      Real.exp (Λ * (Real.exp 1 - 1)) := by
    apply hExpBound.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hreal
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)))
  exact countTail_traffic_memLp_two_and_exponential_norm
    (M.law : Measure (LegalMarkedOptimalInputScene q)) hm
    (fun _ ↦ ENNReal.toReal_nonneg) hExp hexp hT hB hbound

/-- Original target input counts control every measurable traffic readout that
is bounded by a fixed multiple of that same count on its count-tail event. -/
theorem LegalWeightedStationaryPoissonMatching.original_target_countTail_traffic_ltwo
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {W : Set (LegalMarkedPhysicalPoint q)} (hW : MeasurableSet W)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hmass : ((volume : Measure (Fin q → ℝ)).prod β) W ≤ ENNReal.ofReal Λ)
    {T : LegalMarkedOptimalInputScene q → ℝ}
    (hT : AEStronglyMeasurable T (M.law : Measure (LegalMarkedOptimalInputScene q)))
    {B K : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      K < ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})).toReal →
      |T s| ≤ B * ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})).toReal) :
    let N := fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})).toReal
    MemLp ({s | K < N s}.indicator T) 2 (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, ({z | K < N z}.indicator T s) ^ 2
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
        8 * B ^ 2 * Real.exp (Λ * (Real.exp 1 - 1)) * Real.exp (-K / 2) ∧
      eLpNorm ({s | K < N s}.indicator T) 2
        (M.law : Measure (LegalMarkedOptimalInputScene q)) ≤
        ENNReal.ofReal (Real.sqrt 8 * B *
          Real.exp (Λ * (Real.exp 1 - 1) / 2) * Real.exp (-K / 4)) := by
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hreal : (((volume : Measure (Fin q → ℝ)).prod β) W).toReal ≤ Λ := by
    simpa only [ENNReal.toReal_ofReal hΛ] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  obtain ⟨_, hExp, hExpBound⟩ :=
    M.original_target_exp_moment_of_finite_intensity hW hfin (t := 1) (by norm_num)
  simp only [one_mul] at hExp hExpBound
  have hm : Measurable (fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})).toReal) :=
    ((Measure.measurable_coe (hW.prod (measurableSet_singleton (1 : Fin 2)))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal
  have hexp : (∫ s, Real.exp
      (((s.2 : Measure (LegalColoredInputPoint q)) (W ×ˢ {1})).toReal)
      ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
      Real.exp (Λ * (Real.exp 1 - 1)) := by
    apply hExpBound.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hreal
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)))
  exact countTail_traffic_memLp_two_and_exponential_norm
    (M.law : Measure (LegalMarkedOptimalInputScene q)) hm
    (fun _ ↦ ENNReal.toReal_nonneg) hExp hexp hT hB hbound

end OTSelector.Reconstruction
