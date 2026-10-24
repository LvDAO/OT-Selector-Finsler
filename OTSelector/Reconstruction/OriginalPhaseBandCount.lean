import OTSelector.Reconstruction.OriginalInputFiniteCountMean
import OTSelector.Reconstruction.MarkedPhaseBandIntensity

/-! True original Poisson counts in deterministic marked phase bands. The same
original full input supplies the count, its mean, and its exponential bound. -/
open Set Function Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Original source phase-band counts have their actual physical intensity
mean bound and full Poisson exponential bound, without selected-cloud laws. -/
theorem LegalWeightedStationaryPoissonMatching.original_source_phaseBand_count_estimates
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {L : Matrix (Fin q) (Fin q) ℝ} (hL : IsUnit L.det)
    {U : ℝ → Matrix (Fin q) (Fin q) ℝ} (hUm : Measurable U)
    (hU : ∀ a, (U a).PosSemidef) {c : ℝ → (Fin q → ℝ)} (hc : Measurable c)
    {B : Set ℝ} (hB : MeasurableSet B) (R : ℝ) {D m : ℝ}
    (hdet : ∀ a ∈ B, (1 + U a).det ≤ D) (hmass : α B ≤ ENNReal.ofReal m) :
    let V := markedPhaseSourceCell L U c B R
    let H := (ENNReal.ofReal |L.det| *
      volume (Metric.closedBall (0 : Fin q → ℝ) (phaseSourceCellRadius (Fin q) R))) *
      ENNReal.ofReal D * ENNReal.ofReal m
    let N := fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {0})).toReal
    (∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {0}) < ∞) ∧
      Integrable N (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, N s ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤ H.toReal ∧
      ∀ t : ℝ, 0 ≤ t →
        Integrable (fun s ↦ Real.exp (t * N s))
          (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
        (∫ s, Real.exp (t * N s) ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
          Real.exp (H.toReal * (Real.exp t - 1)) := by
  dsimp only
  have hV := measurableSet_markedPhaseSourceCell L hUm hc hB R
  have hbound := prod_volume_markedPhaseSourceCell_le_of_band_det_bound hL hUm hU hc hB
    α R hdet hmass
  have hHfin := phaseBandIntensity_bound_ne_top L R D m
  have hfin := ne_top_of_le_ne_top hHfin hbound
  have hreal := ENNReal.toReal_mono hHfin hbound
  obtain ⟨hi, hmean⟩ := M.original_source_count_integrable_and_integral hV hfin
  refine ⟨(M.original_source_exp_moment_of_finite_intensity hV hfin (t := 0) (by norm_num)).1,
    hi, hmean.le.trans hreal, ?_⟩
  intro t ht
  obtain ⟨_, hIexp, hexp⟩ := M.original_source_exp_moment_of_finite_intensity hV hfin ht
  refine ⟨hIexp, hexp.trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right hreal (sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht))

/-- Original target phase-band counts have their actual physical intensity
mean bound and full Poisson exponential bound, without selected-cloud laws. -/
theorem LegalWeightedStationaryPoissonMatching.original_target_phaseBand_count_estimates
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {L : Matrix (Fin q) (Fin q) ℝ} (hL : IsUnit L.det)
    {U : ℝ → Matrix (Fin q) (Fin q) ℝ} (hUm : Measurable U)
    (hU : ∀ a, (U a).PosSemidef) {c : ℝ → (Fin q → ℝ)} (hc : Measurable c)
    {B : Set ℝ} (hB : MeasurableSet B) (R : ℝ) {D m : ℝ}
    (hdet : ∀ a ∈ B, (1 + U a).det ≤ D) (hmass : β B ≤ ENNReal.ofReal m) :
    let V := markedPhaseSourceCell L U c B R
    let H := (ENNReal.ofReal |L.det| *
      volume (Metric.closedBall (0 : Fin q → ℝ) (phaseSourceCellRadius (Fin q) R))) *
      ENNReal.ofReal D * ENNReal.ofReal m
    let N := fun s : LegalMarkedOptimalInputScene q ↦
      ((s.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {1})).toReal
    (∀ᵐ s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)),
      (s.2 : Measure (LegalColoredInputPoint q)) (V ×ˢ {1}) < ∞) ∧
      Integrable N (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
      (∫ s, N s ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤ H.toReal ∧
      ∀ t : ℝ, 0 ≤ t →
        Integrable (fun s ↦ Real.exp (t * N s))
          (M.law : Measure (LegalMarkedOptimalInputScene q)) ∧
        (∫ s, Real.exp (t * N s) ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) ≤
          Real.exp (H.toReal * (Real.exp t - 1)) := by
  dsimp only
  have hV := measurableSet_markedPhaseSourceCell L hUm hc hB R
  have hbound := prod_volume_markedPhaseSourceCell_le_of_band_det_bound hL hUm hU hc hB
    β R hdet hmass
  have hHfin := phaseBandIntensity_bound_ne_top L R D m
  have hfin := ne_top_of_le_ne_top hHfin hbound
  have hreal := ENNReal.toReal_mono hHfin hbound
  obtain ⟨hi, hmean⟩ := M.original_target_count_integrable_and_integral hV hfin
  refine ⟨(M.original_target_exp_moment_of_finite_intensity hV hfin (t := 0) (by norm_num)).1,
    hi, hmean.le.trans hreal, ?_⟩
  intro t ht
  obtain ⟨_, hIexp, hexp⟩ := M.original_target_exp_moment_of_finite_intensity hV hfin ht
  refine ⟨hIexp, hexp.trans ?_⟩
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right hreal (sub_nonneg.mpr (Real.one_le_exp_iff.mpr ht))

end OTSelector.Reconstruction
