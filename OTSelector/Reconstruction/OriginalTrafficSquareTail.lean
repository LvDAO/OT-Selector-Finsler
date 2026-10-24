import OTSelector.Reconstruction.OriginalLongPathAbsoluteTraffic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # The actual original long-path square has vanishing nonnegative mean -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

/-- Finite genuine real square means identify the literal nonnegative square
mean of the same almost-surely finite traffic. -/
theorem lintegral_ennreal_sq_eq_ofReal_integral_toReal_sq
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ≥0∞}
    (hfinite : ∀ᵐ x ∂μ, f x ≠ (⊤ : ℝ≥0∞))
    (hI : Integrable (fun x ↦ (f x).toReal ^ 2) μ) :
    (∫⁻ x, f x ^ 2 ∂μ) = ENNReal.ofReal (∫ x, (f x).toReal ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun _ ↦ sq_nonneg _)]
  apply lintegral_congr_ae
  filter_upwards [hfinite] with x hx
  rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The literal original full square is finite, and the same literal long-path
square mean vanishes; finite weighted energy supplies all pointwise finiteness. -/
theorem original_longPathTraffic_sq_finite_and_tendsto_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hηm : Measurable η) (hηi : Integrable η volume)
    (hfullI : Integrable (fun scene ↦
      (originalSeedCompletePathAbsoluteTraffic S w η scene).toReal ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) :
    ((∫⁻ scene, originalSeedCompletePathAbsoluteTraffic S w η scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≠ (⊤ : ℝ≥0∞)) ∧
    (∀ R : ℝ, (∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w η R scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≠ (⊤ : ℝ≥0∞)) ∧
    Tendsto (fun R : ℝ ↦ ∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w η R scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
      atTop (𝓝 0) := by
  have hfullfin : (∫⁻ scene, originalSeedCompletePathAbsoluteTraffic S w η scene ^ 2
      ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≠ (⊤ : ℝ≥0∞) := by
    rw [lintegral_ennreal_sq_eq_ofReal_integral_toReal_sq _
      ((D.ae_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hηm hηi).mono
        fun _ h ↦ h.ne) hfullI]
    exact ENNReal.ofReal_ne_top
  have hdom (R : ℝ) : ∀ scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker),
      originalSeedLongPathAbsoluteTraffic S w η R scene ^ 2 ≤
        originalSeedCompletePathAbsoluteTraffic S w η scene ^ 2 :=
    fun scene ↦ pow_le_pow_left' (originalSeedLongPathAbsoluteTraffic_le_full S w η R scene) 2
  refine ⟨hfullfin, fun R ↦ ne_top_of_le_ne_top hfullfin (lintegral_mono (hdom R)), ?_⟩
  have hlim : ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      Tendsto (fun R ↦ originalSeedLongPathAbsoluteTraffic S w η R scene ^ 2)
        atTop (𝓝 (0 : ℝ≥0∞)) := by
    filter_upwards [D.ae_tendsto_original_longPathAbsoluteTraffic_zero hF hw hbounds Q hηm hηi]
      with scene hscene
    simpa [Function.comp_def] using ((ENNReal.continuous_pow 2).tendsto 0).comp hscene
  simpa using tendsto_lintegral_filter_of_dominated_convergence
    (fun scene ↦ originalSeedCompletePathAbsoluteTraffic S w η scene ^ 2)
    (Eventually.of_forall fun R ↦ (measurable_originalSeedLongPathAbsoluteTraffic S hF hw hηm R).pow_const 2)
    (Eventually.of_forall fun R ↦ Eventually.of_forall (hdom R)) hfullfin hlim

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
