import OTSelector.Reconstruction.FinslerOriginalPlanFreeTileLLN

/-!
# Mask-coupling law for the plan-free tile mean

The frozen tile entry couples the mask `edgeEvent(X,Y,c)` to the pair configuration.
This module proves the strongest unconditional form available without a full
decoupling theory, and isolates the exact conditioning input.

**What is proved.**

1. `maskedFrozenCost_eq_indicator_mul`: the masked frozen cost is exactly the
   indicator of the mask times the frozen entry,
   `maskedFrozenCost Q d i j = (Q.indicator (fun p => d p.1 p.2)) (i,j)`.
   This is the deterministic mask decomposition; the coupling is entirely in the
   joint law of `Q(s)` and `d(s)`.

2. `integral_maskedPairSum_eq_card_sq_mul_entry`: **uniform masked-entry identity**.
   If the masked entries have equal expectations over all index pairs (the
   *masked-entry exchangeability* input, which for iid samples follows from
   permutation invariance of the mask condition), then the integrated pair sum is
   the number of pairs times the single-entry expectation:

     `∫ s, ∑ i ∑ j, E s i j ∂μ = (m:ℝ)^2 * ∫ s, E s i 0 j 0.`

   Equivalently the *normalized plan-free tile average* equals the expected masked
   entry at any fixed pair — this is the mask-coupling law at the level of
   exchangeability, and it does not require the mask amplitude to be independent of
   the pairs.

3. `planFreeTileMean_eq_fixedPair`: the normalized plan-free tile mean
   `(1/m^2) ∫ ∑∑ E` is the fixed-pair masked expectation.

4. `PlanFreeTileMeanIdentification` (def) and
   `planFreeTileLLN_of_fixedPairIdentification`: the remaining input is stated with
   all quantifiers explicit: the fixed-pair masked expectation converges to the
   population tile value under the `(n+1)^{2/q}` scale normalization; combined with
   2 it yields `PlanFreeTileLLN`.

**Remaining sub-gap (exact).**  Two pieces are not proved here: (i) the
exchangeability hypothesis itself for the frozen mask (permutation invariance of
`edgeEvent` + integrability, an instance of the repo exchangeability pattern); and
(ii) the identification of the *fixed-pair* masked expectation with the population
tile value `tilePopValue` under the `(n+1)^{2/q}` normalization (this needs the
conditional law of a single edge given its membership in the mask, i.e. a
conditioning/decoupling step).

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

/-- **The deterministic mask decomposition.**  The masked frozen cost is the mask
indicator times the frozen entry. -/
theorem maskedFrozenCost_eq_indicator_mul {n : ℕ} (Q : Set (Fin n × Fin n))
    (d : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    maskedFrozenCost Q d i j = (Q.indicator (fun p : Fin n × Fin n ↦ d p.1 p.2)) (i, j) :=
  rfl

/-- **Uniform masked-entry identity (mask-coupling law at exchangeability level).**
If all masked entries of a matrix-valued random variable have equal expectations,
then the integrated pair sum is the number of pairs times the single-entry
expectation: the normalized plan-free average equals the fixed-pair masked
expectation.  No independence between the mask amplitude and the pairs is needed —
only the exchangeability of the masked entries. -/
theorem integral_maskedPairSum_eq_card_sq_mul_entry
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m) (E : Ω → Matrix (Fin m) (Fin m) ℝ)
    (hint : ∀ i j, Integrable (fun s ↦ E s i j) μ)
    (hEq : ∀ (i j i' j' : Fin m),
      ∫ s, E s i j ∂μ = ∫ s, E s i' j' ∂μ) :
    ∫ s, (∑ i, ∑ j, E s i j) ∂μ =
      ((m : ℝ) * (m : ℝ)) * ∫ s, E s ⟨0, hm⟩ ⟨0, hm⟩ ∂μ := by
  have hstep : ∀ i : Fin m, ∫ s, (∑ j : Fin m, E s i j) ∂μ =
      (m : ℝ) * ∫ s, E s ⟨0, hm⟩ ⟨0, hm⟩ ∂μ := by
    intro i
    rw [integral_finsetSum Finset.univ (fun j _ ↦ hint i j)]
    rw [Finset.sum_congr rfl
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) ↦ hEq i j ⟨0, hm⟩ ⟨0, hm⟩)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [integral_finsetSum Finset.univ
    (fun i _ ↦ integrable_finsetSum Finset.univ (fun j _ ↦ hint i j))]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) ↦ hstep i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The normalized plan-free tile average is the fixed-pair masked expectation.**

This is the mask-coupling law in the form needed by the plan-free lane: the
`(n+1)^{2/q}`-scaled plan-free tile mean, after the uniform pair normalization, is
exactly the expected masked frozen entry at one fixed pair. -/
theorem planFreeTileMean_eq_fixedPair
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m) (E : Ω → Matrix (Fin m) (Fin m) ℝ)
    (hint : ∀ i j, Integrable (fun s ↦ E s i j) μ)
    (hEq : ∀ (i j i' j' : Fin m),
      ∫ s, E s i j ∂μ = ∫ s, E s i' j' ∂μ) :
    (1 / (m : ℝ)) * ((1 / (m : ℝ)) * ∫ s, (∑ i, ∑ j, E s i j) ∂μ) =
      ∫ s, E s ⟨0, hm⟩ ⟨0, hm⟩ ∂μ := by
  rw [integral_maskedPairSum_eq_card_sq_mul_entry μ hm E hint hEq]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  field_simp

/-- **The remaining input of the plan-free lane.**  The fixed-pair masked frozen
expectation converges to the population tile value: this is the identification of
the *single-edge* conditional law (conditioning on mask membership) with the
population tile integrand, under the `(n+1)^{2/q}` scale normalization. -/
def PlanFreeTileMeanIdentification (fixedPair : ℕ → ℝ) (popVal : ℕ → ℝ) : Prop :=
  Tendsto (fun n ↦ fixedPair n - popVal n) atTop (𝓝 0)

/-- **The fixed-pair identification yields the plan-free LLN.**  Combining the
uniform masked-entry identity with the fixed-pair identification gives the plan-free
per-tile LLN. -/
theorem planFreeTileLLN_of_fixedPairIdentification
    (mean fixedPair popVal : ℕ → ℝ)
    (hmean : ∀ n, mean n = fixedPair n)
    (hid : PlanFreeTileMeanIdentification fixedPair popVal) :
    PlanFreeTileLLN (fun n ↦ mean n - popVal n) := by
  show Tendsto (fun n ↦ mean n - popVal n) atTop (𝓝 0)
  refine hid.congr' ?_
  filter_upwards with n
  rw [hmean n]

end OTSelector.Reconstruction
