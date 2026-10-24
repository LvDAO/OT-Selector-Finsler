import OTSelector.MeasureTheory.ApproximateDominationAbsoluteContinuity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.ProjectedDominationDiscard.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.ProjectedDominationDiscard`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ProjectedDominationDiscard

## Lemma skeleton

* **Conditions:** Auxiliary laws at each accuracy push to the exact same full source law; retained source domination and discard tail estimates vanish at stated scales.
* **Objects:** Projected good-event failure bound and almost-everywhere absolute continuity of the original source.
* **Proof detail:** Push the discard-tail event estimate through the projection, combine retained/reference domination on low-discard events and apply the infinitely-good-event absolute-continuity argument.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=59): Section 2B, Theorems 2.59–2.60, p. 44 (increasing and decreasing sets).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.

Source relation (composition): Tail-only approximate domination transfer; no discard expectation or summability is assumed.
-/

/-! Approximate references for retained plans imply absolute continuity of
the same full source marginal. Auxiliary laws may vary with accuracy, provided
their original projections are exactly the same full law. Only tail bounds on
discarded mass are used; its expectation need not be available. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Probability

/-- A good carrier on the full law fails no more often than the original
discard threshold on any auxiliary law with that exact projection. -/
theorem measure_compl_le_of_projected_discard_tail
    {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (R : Measure S) (P : Measure A) (projection : A → S)
    (hprojection : Measurable projection) (hmap : P.map projection = R)
    (G : Set S) (hG : MeasurableSet G) (discard : A → ℝ≥0∞)
    (threshold failure : ℝ≥0∞)
    (hgood : ∀ᵐ a ∂P, discard a ≤ threshold → projection a ∈ G)
    (htail : P {a | threshold < discard a} ≤ failure) : R Gᶜ ≤ failure := by
  rw [← hmap, Measure.map_apply hprojection hG.compl]
  apply le_trans _ htail
  apply measure_mono_ae
  filter_upwards [hgood] with a ha hbad
  exact lt_of_not_ge (fun hle ↦ hbad (ha hle))

/-- Retained references, full/retained/discard inequalities and the original
discard tails are composed before letting accuracy tend to zero. All auxiliary
laws project to the SAME full law; no extra weak limit or expected-discard
assumption is introduced. The good carriers control every set simultaneously. -/
theorem ae_absolutelyContinuous_of_projected_domination_discard_bounds
    {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    {A : ℕ → Type*} [∀ n, MeasurableSpace (A n)]
    (R : Measure S) (P : ∀ n, Measure (A n))
    (projection : ∀ n, A n → S)
    (hprojection : ∀ n, Measurable (projection n))
    (hmap : ∀ n, (P n).map (projection n) = R)
    (source : S → Measure X) (reference : Measure X)
    (approximant : ℕ → Measure X) (hac : ∀ n, approximant n ≪ reference)
    (retained : ∀ n, A n → Measure X) (discard : ∀ n, A n → ℝ≥0∞)
    (error threshold loss : ℕ → ℝ≥0∞)
    (herror : Tendsto error atTop (𝓝 0))
    (hthreshold : Tendsto threshold atTop (𝓝 0))
    (hloss : Tendsto (fun n ↦ loss n / threshold n) atTop (𝓝 0))
    (hfull : ∀ n, ∀ᵐ a ∂P n, ∀ B : Set X,
      source (projection n a) B ≤ retained n a B + discard n a)
    (hretained : ∀ n, ∀ᵐ a ∂P n, ∀ B : Set X,
      retained n a B ≤ approximant n B + error n)
    (htail : ∀ n, P n {a | threshold n < discard n a} ≤ loss n / threshold n)
    (G : ℕ → Set S) (hGmeasurable : ∀ n, MeasurableSet (G n))
    (hG : ∀ n s, s ∈ G n ↔ ∀ B : Set X,
      source s B ≤ approximant n B + (error n + threshold n)) :
    ∀ᵐ s ∂R, source s ≪ reference := by
  have hfailure (n : ℕ) : R (G n)ᶜ ≤ loss n / threshold n := by
    apply measure_compl_le_of_projected_discard_tail R (P n) (projection n)
      (hprojection n) (hmap n) (G n) (hGmeasurable n) (discard n)
      (threshold n) (loss n / threshold n) _ (htail n)
    filter_upwards [hfull n, hretained n] with a hfa hra hsmall
    apply (hG n (projection n a)).mpr
    intro B
    calc
      source (projection n a) B ≤ retained n a B + discard n a := hfa B
      _ ≤ (approximant n B + error n) + threshold n := add_le_add (hra B) hsmall
      _ = approximant n B + (error n + threshold n) := add_assoc _ _ _
  have hsum : Tendsto (fun n ↦ error n + threshold n) atTop (𝓝 0) := by
    simpa only [zero_add] using herror.add hthreshold
  have hfailureLimit : Tendsto (fun n ↦ R (G n)ᶜ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hloss
      (fun _ ↦ bot_le) hfailure
  exact ae_absolutelyContinuous_of_domination_failures_tendsto_zero
    R source reference approximant hac (fun n ↦ error n + threshold n) hsum G
    (fun n s hs ↦ (hG n s).mp hs) hfailureLimit

end OTSelector.Probability

end
end
