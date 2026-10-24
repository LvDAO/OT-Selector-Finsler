import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Independent Random Region

Conditions: Two measurable independent random variables X,Y on a finite base measure; an integrable real function on the product marginal law.

Objects: The joint pushforward, its product marginal law, and the iterated integral after restriction to any jointly measurable region.

Proof detail: Identify the joint law with the product by independence, transport the integral through the measurable pushforward, then apply Fubini to the indicator-restricted integrable function.

Relation to primary sources: This generalizes the cited real-valued probability statements to measurable carriers and a supplied finite-measure independence identity. A region may depend on revealed coordinates, but it must be jointly measurable.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF), Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
-/
/-!
# Pair laws and Fubini transport for independent random variables

This file isolates the measure-theoretic transport used by the finite-sample and deferred
decision arguments.  If two measurable random variables are independent, their joint pushforward
law is the product of their marginal pushforward laws.  Consequently, an integrable function of
the pair can be integrated on the original sample space or on that product law.  The final theorem
specializes this identity to the indicator of an arbitrary measurable region, which is the form
needed for random remaining regions.

All statements below are direct consequences of mathlib's independence, pushforward, and Fubini
theorems.  No conditional-law or project-local assumption is introduced.
-/

open MeasureTheory ProbabilityTheory Set

namespace OTSelector.Probability

variable {Ω A B : Type*}
variable [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]

/-! ## Joint law -/

/-- The joint law of two independent measurable random variables is the product of their laws. -/
theorem indepFun_pair_map_eq_prod_map_map
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → A} {Y : Ω → B}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ) :
    Measure.map (fun ω ↦ (X ω, Y ω)) μ =
      (Measure.map X μ).prod (Measure.map Y μ) := by
  exact hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable

/-! ## Integral transport -/

/-- Transport an integrable function of an independent pair to its product marginal law. -/
theorem integral_indepFun_pair_eq_integral_prod
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → A} {Y : Ω → B}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ)
    {F : A × B → ℝ}
    (hF : Integrable F ((Measure.map X μ).prod (Measure.map Y μ))) :
    (∫ ω, F (X ω, Y ω) ∂μ) =
      ∫ p, F p ∂((Measure.map X μ).prod (Measure.map Y μ)) := by
  have hpair : Measurable (fun ω ↦ (X ω, Y ω)) := hX.prodMk hY
  have hmap : Measure.map (fun ω ↦ (X ω, Y ω)) μ =
      (Measure.map X μ).prod (Measure.map Y μ) :=
    indepFun_pair_map_eq_prod_map_map hX hY hXY
  have hFmap : Integrable F (Measure.map (fun ω ↦ (X ω, Y ω)) μ) := by
    rw [hmap]
    exact hF
  exact (integral_map hpair.aemeasurable hFmap.aestronglyMeasurable).symm.trans
    (by rw [hmap])

/-! ## Measurable random regions -/

/--
For an integrable `f` and a measurable region `C` in the pair space, integrate the regional
restriction either on the original space or by Fubini over the two independent marginal laws.

The set `C` may encode a region selected from revealed data; the only requirement at this level is
joint measurability in the pair variables.
-/
theorem integral_indepFun_randomRegion_eq_iterated
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : Ω → A} {Y : Ω → B}
    (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y μ)
    {f : A × B → ℝ} {C : Set (A × B)}
    (hC : MeasurableSet C)
    (hf : Integrable f ((Measure.map X μ).prod (Measure.map Y μ))) :
    (∫ ω, C.indicator f (X ω, Y ω) ∂μ) =
      ∫ x, ∫ y, C.indicator f (x, y) ∂(Measure.map Y μ) ∂(Measure.map X μ) := by
  let F : A × B → ℝ := C.indicator f
  have hF : Integrable F ((Measure.map X μ).prod (Measure.map Y μ)) := hf.indicator hC
  have htransport := integral_indepFun_pair_eq_integral_prod hX hY hXY hF
  calc
    (∫ ω, C.indicator f (X ω, Y ω) ∂μ) =
        ∫ p, F p ∂((Measure.map X μ).prod (Measure.map Y μ)) := by
      simpa [F] using htransport
    _ = ∫ x, ∫ y, F (x, y) ∂(Measure.map Y μ) ∂(Measure.map X μ) :=
      integral_prod F hF
    _ = ∫ x, ∫ y, C.indicator f (x, y) ∂(Measure.map Y μ) ∂(Measure.map X μ) := by
      rfl

end OTSelector.Probability
