import OTSelector.MeasureTheory.FixedMarginalWeightedWeak
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.FixedMarginalRestrictedWeak.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.FixedMarginalRestrictedWeak`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.FixedMarginalRestrictedWeak

## Lemma skeleton

* **Conditions:** Weakly convergent joint probabilities with the same fixed first marginal and an arbitrary measurable first-coordinate set.
* **Objects:** Weak convergence of restrictions to the corresponding measurable cylinder.
* **Proof detail:** Approximate its first-coordinate indicator in L1 of the fixed marginal by continuous bounded functions; the approximation error is uniform in every joint law, so weak convergence applies to each approximant.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=110): Section 418J (second-countable target Lusin theorem), with compact inner regularity in Section 416.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61): Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.

Source relation (composition): Fixed-marginal indicator weighting removes any boundary-null hypothesis on the measurable macro set.
-/

/-! Measurable macro cores retain their original mass under joint weak limits.
Their boundary may have positive measure; the fixed first marginal supplies the
required indicator-weight convergence. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Probability
variable {W S : Type*} [TopologicalSpace W] [PolishSpace W]
  [MeasurableSpace W] [BorelSpace W]
  [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]

/-- Restricting every joint law to an arbitrary measurable first-coordinate
core preserves weak convergence as finite measures, with no renormalization. -/
theorem fixed_first_marginal_restrict_tendsto_of_weak
    (η : ProbabilityMeasure W)
    (Rn : ℕ → ProbabilityMeasure (W × S)) (R : ProbabilityMeasure (W × S))
    (hweak : Tendsto Rn atTop (𝓝 R))
    (hmarg : ∀ n, (Rn n).map measurable_fst.aemeasurable = η)
    (A : Set W) (hA : MeasurableSet A) :
    Tendsto (fun n ↦ (Rn n).toFiniteMeasure.restrict (A ×ˢ univ)) atTop
      (𝓝 (R.toFiniteMeasure.restrict (A ×ˢ univ))) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro Φ
  let h : W → ℝ := A.indicator (fun _ ↦ 1)
  have hh : Integrable h (η : Measure W) := (integrable_const 1).indicator hA
  have ht := (fixed_first_marginal_weighted_integral_tendsto_of_weak
    η Rn R hweak hmarg h hh Φ).2
  have heq (μ : Measure (W × S)) :
      (∫ p, h p.1 * Φ p ∂μ) = ∫ p, Φ p ∂μ.restrict (A ×ˢ univ) := by
    have hf : (fun p : W × S ↦ h p.1 * Φ p) =
        (A ×ˢ univ).indicator (fun p ↦ Φ p) := by
      funext p
      by_cases hp : p.1 ∈ A <;> simp [h,hp]
    rw [hf,integral_indicator (hA.prod MeasurableSet.univ)]
  change Tendsto (fun n ↦ ∫ p, Φ p ∂(Rn n : Measure (W × S)).restrict (A ×ˢ univ))
    atTop (𝓝 (∫ p, Φ p ∂(R : Measure (W × S)).restrict (A ×ˢ univ)))
  simpa only [heq] using ht

end OTSelector.Probability

end
end
