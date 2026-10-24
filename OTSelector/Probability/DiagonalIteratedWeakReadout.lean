import OTSelector.Topology.CurriedAccuracyApproximation

/-!
Conditions: Two actual iterated weak-limit stages, continuous plan-valued maps, a bounded continuous probe and equality of the plans a.e. under the final law.

Objects: Integrable bounded probe gaps, their real/nonnegative expectation limits and vanishing gaps under the curried two-parameter filter.

Proof detail: Make the absolute difference of the two bounded probe integrals a bounded continuous readout. Pass it through each weak stage, use final a.e. plan equality for zero expectation, and package the limits with the curried filter.

References: D. H. Fremlin: Sections 437J(d),(f),(g), 437K–437L, PDF p. 61 onward; Rick Durrett: Section 1.4, Exercise 1.4.1, p. 24.
Relation: A local bounded-test iterated-limit consequence. The inner sample threshold depends on the fixed outer index; no uniform product-filter or same-rate diagonal limit is claimed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneDiagonalWeakReadout.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneDiagonalWeakReadout`; the selected original proof blocks follow. -/
section

/-!
# Diagonal original weak laws give vanishing bounded probe gaps

The bounded continuous probe gap passes through each of the two given weak
stages. Equality of the two original plans almost surely at the final law
makes its expectation zero. The curried filter keeps the inner sample
threshold dependent on the fixed outer index.
-/

open Set Function Filter MeasureTheory
open scoped Topology BoundedContinuousFunction ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]

/-- The literal absolute signed probe gap of two original probability plans. -/
def physicalSceneProbabilityPlanProbeGap (f : Z →ᵇ ℝ)
    (s : ProbabilityMeasure Z × ProbabilityMeasure Z) : ℝ :=
  |(∫ p, f p ∂(s.1 : Measure Z)) - ∫ p, f p ∂(s.2 : Measure Z)|

/-- Continuous probability-plan projections turn a bounded continuous probe
into a bounded continuous scalar gap without any extra source hypothesis. -/
def boundedContinuousProbabilityPlanProbeGap
    {S : Type*} [TopologicalSpace S]
    (π₀ π₁ : S → ProbabilityMeasure Z) (hπ₀ : Continuous π₀) (hπ₁ : Continuous π₁)
    (f : Z →ᵇ ℝ) : S →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun s ↦ |(∫ p, f p ∂(π₀ s : Measure Z)) - ∫ p, f p ∂(π₁ s : Measure Z)|)
    ((((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp hπ₀).sub
      ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).comp hπ₁)).abs)
    (2 * ‖f‖) (fun s ↦ by
      rw [Real.norm_eq_abs, abs_abs]
      calc
        |(∫ p, f p ∂(π₀ s : Measure Z)) - ∫ p, f p ∂(π₁ s : Measure Z)| ≤
            |∫ p, f p ∂(π₀ s : Measure Z)| + |∫ p, f p ∂(π₁ s : Measure Z)| :=
          abs_sub _ _
        _ ≤ ‖f‖ + ‖f‖ := add_le_add
          (f.norm_integral_le_norm (μ := (π₀ s : Measure Z)))
          (f.norm_integral_le_norm (μ := (π₁ s : Measure Z)))
        _ = 2 * ‖f‖ := (two_mul _).symm)

/-- The literal paired-plan gap is continuous in the ordinary weak topology. -/
theorem continuous_physicalSceneProbabilityPlanProbeGap (f : Z →ᵇ ℝ) :
    Continuous (physicalSceneProbabilityPlanProbeGap f) :=
  (boundedContinuousProbabilityPlanProbeGap Prod.fst Prod.snd
    continuous_fst continuous_snd f).continuous

/-- The literal original paired-plan gap is integrable against every finite
law with measurable opens. -/
theorem integrable_physicalSceneProbabilityPlanProbeGap
    [OpensMeasurableSpace (ProbabilityMeasure Z × ProbabilityMeasure Z)]
    (f : Z →ᵇ ℝ) (R : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))
    [IsFiniteMeasure R] : Integrable (physicalSceneProbabilityPlanProbeGap f) R :=
  (boundedContinuousProbabilityPlanProbeGap Prod.fst Prod.snd
    continuous_fst continuous_snd f).integrable (μ := R)

/-- For arbitrary continuous original plan projections, both real and
extended nonnegative gap expectations pass a weak-law limit. -/
theorem probabilityPlan_probe_gap_expectation_tendsto_of_weak
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    (P : ℕ → ProbabilityMeasure S) (Q : ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (π₀ π₁ : S → ProbabilityMeasure Z) (hπ₀ : Continuous π₀) (hπ₁ : Continuous π₁)
    (f : Z →ᵇ ℝ) :
    let obs := fun s ↦ |(∫ p, f p ∂(π₀ s : Measure Z)) - ∫ p, f p ∂(π₁ s : Measure Z)|
    (∀ n, Integrable obs (P n : Measure S)) ∧ Integrable obs (Q : Measure S) ∧
    Tendsto (fun n ↦ ∫ s, obs s ∂(P n : Measure S)) atTop
      (𝓝 (∫ s, obs s ∂(Q : Measure S))) ∧
    Tendsto (fun n ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(P n : Measure S)) atTop
      (𝓝 (∫⁻ s, ENNReal.ofReal (obs s) ∂(Q : Measure S))) := by
  intro obs
  let G := boundedContinuousProbabilityPlanProbeGap π₀ π₁ hπ₀ hπ₁ f
  have hInt (n : ℕ) : Integrable obs (P n : Measure S) :=
    G.integrable (μ := (P n : Measure S))
  have hIntQ : Integrable obs (Q : Measure S) := G.integrable (μ := (Q : Measure S))
  have hreal : Tendsto (fun n ↦ ∫ s, obs s ∂(P n : Measure S)) atTop
      (𝓝 (∫ s, obs s ∂(Q : Measure S))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) G
  refine ⟨hInt, hIntQ, hreal, ?_⟩
  have henn := (ENNReal.continuous_ofReal.tendsto (∫ s, obs s ∂(Q : Measure S))).comp hreal
  rw [ofReal_integral_eq_lintegral_ofReal hIntQ (ae_of_all _ fun _ ↦ abs_nonneg _)] at henn
  exact henn.congr' (Eventually.of_forall fun n ↦
    ofReal_integral_eq_lintegral_ofReal (hInt n) (ae_of_all _ fun _ ↦ abs_nonneg _))

/-- The two given weak stages and almost-sure diagonal agreement yield all
actual bounded probe expectation limits, with the sample-before-outer curry
limit equal to zero for real and extended nonnegative expectations. -/
theorem diagonal_probabilityPlan_probe_gap_expectation_limits_of_iterated_weak
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    (P : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (P ℓ) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (π₀ π₁ : S → ProbabilityMeasure Z) (hπ₀ : Continuous π₀) (hπ₁ : Continuous π₁)
    (hdiag : ∀ᵐ s ∂(R : Measure S), π₀ s = π₁ s) (f : Z →ᵇ ℝ) :
    let obs := fun s ↦ |(∫ p, f p ∂(π₀ s : Measure Z)) - ∫ p, f p ∂(π₁ s : Measure Z)|
    (∫ s, obs s ∂(R : Measure S)) = 0 ∧
    (∫⁻ s, ENNReal.ofReal (obs s) ∂(R : Measure S)) = 0 ∧
    (∀ ℓ n, Integrable obs (P ℓ n : Measure S)) ∧
    (∀ ℓ, Integrable obs (Q ℓ : Measure S)) ∧ Integrable obs (R : Measure S) ∧
    (∀ ℓ, Tendsto (fun n ↦ ∫ s, obs s ∂(P ℓ n : Measure S)) atTop
      (𝓝 (∫ s, obs s ∂(Q ℓ : Measure S)))) ∧
    Tendsto (fun ℓ ↦ ∫ s, obs s ∂(Q (ψ ℓ) : Measure S)) atTop (𝓝 0) ∧
    Tendsto (fun p : ℕ × ℕ ↦ ∫ s, obs s ∂(P (ψ p.1) p.2 : Measure S))
      ((atTop : Filter ℕ).curry atTop) (𝓝 0) ∧
    (∀ ℓ, Tendsto (fun n ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(P ℓ n : Measure S)) atTop
      (𝓝 (∫⁻ s, ENNReal.ofReal (obs s) ∂(Q ℓ : Measure S)))) ∧
    Tendsto (fun ℓ ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(Q (ψ ℓ) : Measure S)) atTop (𝓝 0) ∧
    Tendsto (fun p : ℕ × ℕ ↦ ∫⁻ s, ENNReal.ofReal (obs s)
      ∂(P (ψ p.1) p.2 : Measure S)) ((atTop : Filter ℕ).curry atTop) (𝓝 0) := by
  intro obs
  have hI (ℓ : ℕ) := probabilityPlan_probe_gap_expectation_tendsto_of_weak
    (P ℓ) (Q ℓ) (hinner ℓ) π₀ π₁ hπ₀ hπ₁ f
  have hO := probabilityPlan_probe_gap_expectation_tendsto_of_weak
    (fun ℓ ↦ Q (ψ ℓ)) R houter π₀ π₁ hπ₀ hπ₁ f
  have hRzero : obs =ᵐ[(R : Measure S)] fun _ ↦ 0 := by
    filter_upwards [hdiag] with s hs
    dsimp only [obs]
    rw [hs, sub_self, abs_zero]
  have hRreal : (∫ s, obs s ∂(R : Measure S)) = 0 := integral_eq_zero_of_ae hRzero
  have hRenn : (∫⁻ s, ENNReal.ofReal (obs s) ∂(R : Measure S)) = 0 := by
    calc
      _ = ∫⁻ _s, (0 : ℝ≥0∞) ∂(R : Measure S) :=
        lintegral_congr_ae (hRzero.mono fun s hs ↦ by rw [hs, ENNReal.ofReal_zero])
      _ = 0 := lintegral_zero
  have hrealOuter : Tendsto (fun ℓ ↦ ∫ s, obs s ∂(Q (ψ ℓ) : Measure S)) atTop (𝓝 0) := by
    rw [← hRreal]
    exact hO.2.2.1
  have hennOuter : Tendsto
      (fun ℓ ↦ ∫⁻ s, ENNReal.ofReal (obs s) ∂(Q (ψ ℓ) : Measure S)) atTop (𝓝 0) := by
    rw [← hRenn]
    exact hO.2.2.2
  refine ⟨hRreal, hRenn, fun ℓ ↦ (hI ℓ).1, fun ℓ ↦ (hI ℓ).2.1, hO.2.1,
    fun ℓ ↦ (hI ℓ).2.2.1, hrealOuter, ?_, fun ℓ ↦ (hI ℓ).2.2.2, hennOuter, ?_⟩
  · exact tendsto_curry_zero_of_inner_outer_readout_limits
      (fun ℓ n ↦ ∫ s, obs s ∂(P ℓ n : Measure S))
      (fun ℓ ↦ ∫ s, obs s ∂(Q ℓ : Measure S)) ψ (fun ℓ ↦ (hI ℓ).2.2.1) hrealOuter
  · exact tendsto_lintegral_ofReal_curry_zero_of_iterated_readout_limits
      (fun ℓ n ↦ (P ℓ n : Measure S)) (fun ℓ ↦ (Q ℓ : Measure S))
      (fun _ n ↦ n) ψ obs (fun _ ↦ abs_nonneg _)
      (fun ℓ ↦ ⟨Eventually.of_forall (hI ℓ).1, (hI ℓ).2.2.1⟩) hrealOuter

/-- Pair-space specialization, with the literal original probability-plan
probe gap and no changes to either of the two weak-limit indices. -/
theorem physicalSceneProbabilityPlanProbeGap_limits_of_iterated_weak
    [OpensMeasurableSpace (ProbabilityMeasure Z × ProbabilityMeasure Z)]
    (P : ℕ → ℕ → ProbabilityMeasure (ProbabilityMeasure Z × ProbabilityMeasure Z))
    (Q : ℕ → ProbabilityMeasure (ProbabilityMeasure Z × ProbabilityMeasure Z))
    (R : ProbabilityMeasure (ProbabilityMeasure Z × ProbabilityMeasure Z)) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (P ℓ) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (hdiag : ∀ᵐ s ∂(R : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z)), s.1 = s.2)
    (f : Z →ᵇ ℝ) :
    let obs := physicalSceneProbabilityPlanProbeGap f
    (∫ s, obs s ∂(R : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))) = 0 ∧
    (∫⁻ s, ENNReal.ofReal (obs s)
      ∂(R : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))) = 0 ∧
    (∀ ℓ n, Integrable obs (P ℓ n : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))) ∧
    (∀ ℓ, Integrable obs (Q ℓ : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))) ∧
    Integrable obs (R : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z)) ∧
    (∀ ℓ, Tendsto (fun n ↦ ∫ s, obs s
      ∂(P ℓ n : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))) atTop
      (𝓝 (∫ s, obs s ∂(Q ℓ : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))))) ∧
    Tendsto (fun ℓ ↦ ∫ s, obs s
      ∂(Q (ψ ℓ) : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))) atTop (𝓝 0) ∧
    Tendsto (fun p : ℕ × ℕ ↦ ∫ s, obs s
      ∂(P (ψ p.1) p.2 : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z)))
      ((atTop : Filter ℕ).curry atTop) (𝓝 0) ∧
    (∀ ℓ, Tendsto (fun n ↦ ∫⁻ s, ENNReal.ofReal (obs s)
      ∂(P ℓ n : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))) atTop
      (𝓝 (∫⁻ s, ENNReal.ofReal (obs s)
        ∂(Q ℓ : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))))) ∧
    Tendsto (fun ℓ ↦ ∫⁻ s, ENNReal.ofReal (obs s)
      ∂(Q (ψ ℓ) : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z))) atTop (𝓝 0) ∧
    Tendsto (fun p : ℕ × ℕ ↦ ∫⁻ s, ENNReal.ofReal (obs s)
      ∂(P (ψ p.1) p.2 : Measure (ProbabilityMeasure Z × ProbabilityMeasure Z)))
      ((atTop : Filter ℕ).curry atTop) (𝓝 0) :=
  diagonal_probabilityPlan_probe_gap_expectation_limits_of_iterated_weak
    P Q R ψ hinner houter Prod.fst Prod.snd continuous_fst continuous_snd hdiag f

end OTSelector.Reconstruction

end
end
