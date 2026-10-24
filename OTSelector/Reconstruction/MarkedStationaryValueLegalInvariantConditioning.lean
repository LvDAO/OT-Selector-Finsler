import OTSelector.Reconstruction.MarkedStationaryValueLegalConditionedMatching
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalPoissonInputErgodicity

/-!
# Actual invariant conditioning preserves the original weighted matching class

The complete original Poisson input is ergodic under a nonzero translation.
An invariant scene event therefore retains exactly that same whole input law.
All weighted matching fields then follow for the literal conditioned scene.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported ProbabilityTheory
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalInvariantConditioningInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInvariantConditioningPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- An actual invariant scene event preserves the complete original input
law. The required ergodicity is proved from this same original Poisson input. -/
theorem LegalWeightedStationaryPoissonMatching.conditioned_inputLaw_eq
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (A : Set (LegalMarkedOptimalInputScene q)) (hA : MeasurableSet A)
    (hpos : (M.law : Measure (LegalMarkedOptimalInputScene q)) A ≠ 0)
    (hinv : ∀ v : Fin q → ℝ, legalMarkedInputSceneReroot q v ⁻¹' A =ᵐ[(M.law : Measure _)] A) :
    (M.conditionedLaw A hpos : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd =
      (M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd := by
  let v : Fin q → ℝ := fun _ ↦ 1
  have hv : v ≠ 0 := by
    intro hz
    have := congrFun hz ⟨0, hq⟩
    norm_num [v] at this
  have : IsProbabilityMeasure ((M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact map_cond_eq_of_ergodic_factor_of_ae_invariant
    (M.law : Measure (LegalMarkedOptimalInputScene q))
    ((M.law : Measure (LegalMarkedOptimalInputScene q)).map Prod.snd)
    (legalMarkedInputSceneReroot q v) (legalOriginalInputTranslation q v) Prod.snd
    (M.stationary v) measurable_snd rfl (fun _ ↦ rfl) (M.originalInput_ergodic hv)
    A hA (hinv v) hpos

/-- Every positive invariant scene event yields a genuine matching for the
same original cost and original Poisson clocks, with no factor-law premise. -/
def LegalWeightedStationaryPoissonMatching.invariantConditionedMatching
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (A : Set (LegalMarkedOptimalInputScene q)) (hA : MeasurableSet A)
    (hpos : (M.law : Measure (LegalMarkedOptimalInputScene q)) A ≠ 0)
    (hinv : ∀ v : Fin q → ℝ, legalMarkedInputSceneReroot q v ⁻¹' A =ᵐ[(M.law : Measure _)] A) :
    LegalWeightedStationaryPoissonMatching q α β kin g :=
  M.conditionedMatching A hA hpos hinv (M.conditioned_inputLaw_eq hq A hA hpos hinv)

@[simp]
theorem LegalWeightedStationaryPoissonMatching.invariantConditionedMatching_law
    {q : ℕ} (hq : 0 < q) {α β : Measure ℝ}
    [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (A : Set (LegalMarkedOptimalInputScene q)) (hA : MeasurableSet A)
    (hpos : (M.law : Measure (LegalMarkedOptimalInputScene q)) A ≠ 0)
    (hinv : ∀ v : Fin q → ℝ, legalMarkedInputSceneReroot q v ⁻¹' A =ᵐ[(M.law : Measure _)] A) :
    (M.invariantConditionedMatching hq A hA hpos hinv).law = M.conditionedLaw A hpos := rfl

end OTSelector.Reconstruction
