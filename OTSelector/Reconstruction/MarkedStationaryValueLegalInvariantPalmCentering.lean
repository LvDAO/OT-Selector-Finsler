import OTSelector.Reconstruction.MarkedStationaryValueLegalInvariantMinimum

/-!
# Actual invariant-conditional centering from original conditioned Palms

Every invariant event uses its own actual original conditioned scene Palm.
A literal scene readout converts those Palm means to invariant event integrals,
which determine the conditional expectation on the invariant sigma algebra.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Centering in every actual invariant-conditioned Palm gives conditional
centering of the same original scene observable. No conditional Palm is
identified with a Palm-event conditioning. -/
theorem LegalWeightedStationaryPoissonMatching.condExp_scenePalmReadout_eq_zero
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    {f : PhysicalPairPalmMark (Fin q) → V} (hf : Integrable f (legalMarkedJointPalm q M.law))
    (hzero : ∀ (A : Set (LegalMarkedOptimalInputScene q)) (hA : MeasurableSet A)
      (hpos : (M.law : Measure (LegalMarkedOptimalInputScene q)) A ≠ 0)
      (hinv : ∀ v : Fin q → ℝ, legalMarkedInputSceneReroot q v ⁻¹' A =ᵐ[(M.law : Measure _)] A),
      ∫ m, f m ∂legalMarkedJointPalm q
        (M.invariantConditionedMatching hq A hA hpos hinv).law = 0) :
    (M.law : Measure (LegalMarkedOptimalInputScene q))[
      legalMarkedScenePalmReadout q f | M.invariantSigma] =ᵐ[(M.law : Measure _)] fun _ ↦ 0 := by
  apply condExp_eq_zero_of_all_setIntegral_eq_zero _ (aeInvariantEventSigma_le _ _)
    (integrable_legalMarkedScenePalmReadout M.law hf)
  intro A hA
  by_cases hpos : (M.law : Measure (LegalMarkedOptimalInputScene q)) A = 0
  · exact setIntegral_measure_zero _ hpos
  · let R := M.invariantConditionedMatching hq A hA.1 hpos hA.2
    have hc : ((M.law : Measure (LegalMarkedOptimalInputScene q)) A)⁻¹ ≠ ∞ :=
      ENNReal.inv_ne_top.mpr hpos
    have hIf : Integrable f (legalMarkedJointPalm q R.law) :=
      (hf.smul_measure hc).mono_measure (M.conditionedPalm_le A hpos)
    have hmean : (∫ s, legalMarkedScenePalmReadout q f s
        ∂(M.law : Measure (LegalMarkedOptimalInputScene q))[|A]) = 0 := by
      have he := integral_legalMarkedScenePalmReadout R.law hIf
      rw [hzero A hA.1 hpos hA.2] at he
      exact he
    have hr : ((M.law : Measure (LegalMarkedOptimalInputScene q)) A).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hpos, measure_ne_top _ _⟩
    have he : (((M.law : Measure (LegalMarkedOptimalInputScene q)) A).toReal)⁻¹ •
        (∫ s in A, legalMarkedScenePalmReadout q f s
          ∂(M.law : Measure (LegalMarkedOptimalInputScene q))) = 0 := by
      simpa only [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv] using hmean
    exact (smul_eq_zero.mp he).resolve_left (inv_ne_zero hr)

end OTSelector.Reconstruction
