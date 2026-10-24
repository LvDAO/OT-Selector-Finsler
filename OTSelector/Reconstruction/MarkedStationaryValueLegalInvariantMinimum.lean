import OTSelector.Reconstruction.MarkedStationaryValueLegalInvariantConditioning
import OTSelector.Reconstruction.MarkedStationaryValueLegalScenePalmReadout
import OTSelector.Probability.ConditionalMinimumMean
import OTSelector.Probability.InvariantEventSigma

/-!
# Actual minimizing original matchings remain minimizing on invariant events

The original scene weighted readout has its true weighted value as mean.
Literal invariant conditioning stays in the same original matching class,
so conditional means attain that same global minimum.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- All original rerooting-invariant events of the actual original scene law. -/
@[instance_reducible]
def LegalWeightedStationaryPoissonMatching.invariantSigma
    {q : ℕ} {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) :
    MeasurableSpace (LegalMarkedOptimalInputScene q) :=
  aeInvariantEventSigma (M.law : Measure (LegalMarkedOptimalInputScene q))
    (legalMarkedInputSceneReroot q)

/-- Actual original invariant conditioning retains the attained weighted
minimum; the conditioned Palm is its own scene's Palm throughout. -/
theorem LegalWeightedStationaryPoissonMatching.invariantConditionedMatching_value_eq
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching q α β kin g, M.value t ≤ R.value t)
    (A : Set (LegalMarkedOptimalInputScene q)) (hA : MeasurableSet A)
    (hpos : (M.law : Measure (LegalMarkedOptimalInputScene q)) A ≠ 0)
    (hinv : ∀ v : Fin q → ℝ, legalMarkedInputSceneReroot q v ⁻¹' A =ᵐ[(M.law : Measure _)] A) :
    (M.invariantConditionedMatching hq A hA hpos hinv).value t = M.value t := by
  let f := legalMarkedScenePalmReadout q
    (fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
  have hI : Integrable f (M.law : Measure (LegalMarkedOptimalInputScene q)) :=
    integrable_legalMarkedScenePalmReadout M.law
      (M.kinetic_integrable.add (M.probe_integrable.const_mul t))
  have hmean : ∫ s, f s ∂(M.law : Measure (LegalMarkedOptimalInputScene q)) = M.value t :=
    (M.value_eq_integral_scenePalmReadout t).symm
  have hlow : ∀ B, MeasurableSet[M.invariantSigma] B →
      (M.law : Measure (LegalMarkedOptimalInputScene q)) B ≠ 0 →
      M.value t ≤ ∫ s, f s ∂(M.law : Measure (LegalMarkedOptimalInputScene q))[|B] := by
    intro B hB hBpos
    have h := hmin (M.invariantConditionedMatching hq B hB.1 hBpos hB.2)
    rw [(M.invariantConditionedMatching hq B hB.1 hBpos hB.2).value_eq_integral_scenePalmReadout t,
      M.invariantConditionedMatching_law] at h
    exact h
  have hval := integral_cond_eq_minimum_of_conditional_lower_bound
    (M.law : Measure (LegalMarkedOptimalInputScene q))
    (aeInvariantEventSigma_le _ _) hI hmean hlow (show MeasurableSet[M.invariantSigma] A from ⟨hA, hinv⟩) hpos
  rw [LegalWeightedStationaryPoissonMatching.value_eq_integral_scenePalmReadout,
    M.invariantConditionedMatching_law]
  exact hval

/-- The literal invariant-conditioned original matching is itself globally
minimizing for the same kinetic cost and paired-clock tilt. -/
theorem LegalWeightedStationaryPoissonMatching.invariantConditionedMatching_minimal
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching q α β kin g, M.value t ≤ R.value t)
    (A : Set (LegalMarkedOptimalInputScene q)) (hA : MeasurableSet A)
    (hpos : (M.law : Measure (LegalMarkedOptimalInputScene q)) A ≠ 0)
    (hinv : ∀ v : Fin q → ℝ, legalMarkedInputSceneReroot q v ⁻¹' A =ᵐ[(M.law : Measure _)] A) :
    ∀ R : LegalWeightedStationaryPoissonMatching q α β kin g,
      (M.invariantConditionedMatching hq A hA hpos hinv).value t ≤ R.value t := by
  rw [M.invariantConditionedMatching_value_eq hq t hmin A hA hpos hinv]
  exact hmin

/-- The original minimizing scene cost has constant conditional mean on the
actual sigma algebra of all invariant original scene events. -/
theorem LegalWeightedStationaryPoissonMatching.condExp_scenePalmReadout_eq_minimum
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g) (t : ℝ)
    (hmin : ∀ R : LegalWeightedStationaryPoissonMatching q α β kin g, M.value t ≤ R.value t) :
    (M.law : Measure (LegalMarkedOptimalInputScene q))[
      legalMarkedScenePalmReadout q (fun m ↦ kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2)
        | M.invariantSigma] =ᵐ[(M.law : Measure _)] fun _ ↦ M.value t := by
  apply condExp_eq_minimum_of_conditional_lower_bound _ (aeInvariantEventSigma_le _ _)
    (integrable_legalMarkedScenePalmReadout M.law
      (M.kinetic_integrable.add (M.probe_integrable.const_mul t)))
    (M.value_eq_integral_scenePalmReadout t).symm
  intro A hA hpos
  have h := hmin (M.invariantConditionedMatching hq A hA.1 hpos hA.2)
  rw [(M.invariantConditionedMatching hq A hA.1 hpos hA.2).value_eq_integral_scenePalmReadout t,
    M.invariantConditionedMatching_law] at h
  exact h

end OTSelector.Reconstruction
