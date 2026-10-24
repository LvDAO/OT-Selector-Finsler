import OTSelector.Reconstruction.FinslerPhysicalSceneRootedRetainedCyclePairWitness
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonproperExhaustion
import OTSelector.Transport.CyclicMonotonicity.ClockTwoCycleExhaustion

/-! Countable actual full-plan pair witnesses give one common legal no-cycle event. -/
open Set MeasureTheory ProbabilityTheory TopologicalSpace OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι S : Type*} [Fintype ι] [MeasurableSpace S]
local notation "Point" => ((ι → ℝ) × ℝ)
local notation "Edge" => (Point × Point)

/-- The literal marked-scene witness uses the unchanged original clock and cost. -/
theorem physicalSceneStrictCyclePairEvent_fiber_eq_clockImprovement
    (c : S → Point → Point → ℝ) (K : Set Edge) (gap margin : ℝ) (s : S) :
    Prod.mk s ⁻¹' physicalSceneStrictCyclePairEvent c (physicalSceneClockGapRegion gap) K margin =
      clockTwoCycleImprovement Prod.snd (c s) K gap margin := by
  ext p
  simp only [mem_preimage, physicalSceneStrictCyclePairEvent, physicalSceneClockGapRegion,
    clockTwoCycleImprovement, clockTwoCycleLegal, clockTwoCycleGain, mem_ofPred_eq, and_assoc]

/-- Every compact witness may be proved on its own probability-one event on
one fixed full scene law. Countable exhaustion then gives one common event
with the original cost inequality for almost every strictly legal edge pair. -/
theorem ae_physicalScene_twoCycle_cost_le_of_cyclePairMass_zero
    (R : Measure S) (plan : S → LocalFiniteMeasure Edge) (c : S → Point → Point → ℝ)
    (K : ℕ → Set Edge) (hmono : Monotone K) (hcover : ∀ e, ∃ n, e ∈ K n)
    (hnull : ∀ n k m : ℕ, ∀ᵐ s ∂R,
      physicalSceneCyclePairMass plan
        (physicalSceneStrictCyclePairEvent c
          (physicalSceneClockGapRegion (1 / ((k : ℝ) + 1))) (K n) (1 / ((m : ℝ) + 1))) s = 0) :
    ∀ᵐ s ∂R, ∀ᵐ p ∂(plan s : Measure Edge).prod (plan s : Measure Edge),
      (p.1.1.2 < p.1.2.2 ∧ p.2.1.2 < p.2.2.2 ∧
        p.1.1.2 < p.2.2.2 ∧ p.2.1.2 < p.1.2.2) →
      c s p.1.1 p.1.2 + c s p.2.1 p.2.2 ≤ c s p.1.1 p.2.2 + c s p.2.1 p.1.2 := by
  apply ae_ae_twoCycle_cost_le_of_clock_improvement_null R
    (fun s ↦ (plan s : Measure Edge)) Prod.snd c K hmono hcover
  intro n k m
  filter_upwards [hnull n k m] with s hs
  change (plan s : Measure Edge).prod (plan s : Measure Edge)
    (Prod.mk s ⁻¹' physicalSceneStrictCyclePairEvent c
      (physicalSceneClockGapRegion (1 / ((k : ℝ) + 1))) (K n) (1 / ((m : ℝ) + 1))) = 0 at hs
  rwa [physicalSceneStrictCyclePairEvent_fiber_eq_clockImprovement] at hs

/-- The canonical compact norm-ball exhaustion is produced internally. -/
theorem ae_physicalScene_twoCycle_cost_le_of_compact_cyclePairMass_zero
    (R : Measure S) (plan : S → LocalFiniteMeasure Edge) (c : S → Point → Point → ℝ)
    (hnull : ∀ (K : Set Edge), IsCompact K → ∀ k m : ℕ, ∀ᵐ s ∂R,
      physicalSceneCyclePairMass plan
        (physicalSceneStrictCyclePairEvent c
          (physicalSceneClockGapRegion (1 / ((k : ℝ) + 1))) K (1 / ((m : ℝ) + 1))) s = 0) :
    ∀ᵐ s ∂R, ∀ᵐ p ∂(plan s : Measure Edge).prod (plan s : Measure Edge),
      (p.1.1.2 < p.1.2.2 ∧ p.2.1.2 < p.2.2.2 ∧
        p.1.1.2 < p.2.2.2 ∧ p.2.1.2 < p.1.2.2) →
      c s p.1.1 p.1.2 + c s p.2.1 p.2.2 ≤ c s p.1.1 p.2.2 + c s p.2.1 p.1.2 := by
  let K := physicalSceneNormBallExhaustion Edge 0
  exact ae_physicalScene_twoCycle_cost_le_of_cyclePairMass_zero R plan c K
    K.subset K.exists_mem (fun n ↦ hnull (K n) (K.isCompact n))
end OTSelector.Reconstruction
