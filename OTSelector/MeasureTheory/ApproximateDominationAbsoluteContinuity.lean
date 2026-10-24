import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
## Lemma skeleton

* **Conditions:** Good-event failure masses tend to zero; on each good event a source measure is setwise dominated by an absolutely continuous approximant plus an error tending to zero, simultaneously for all sets.
* **Objects:** Almost-everywhere infinitely frequent good events and absolute continuity of the actual source measure.
* **Proof detail:** An eventually-bad tail has mass bounded by every later failure mass, hence zero; remove the countable union of such tails. On the resulting one event, use infinitely many good indices for every reference-null set.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 2B, Theorems 2.59–2.60, p. 44 (increasing and decreasing sets).
  https://measure.axler.net/MIRA.pdf#page=59
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** Derived measure-continuity/null-tail argument. No summability, independence, measurability of the absolute-continuity predicate or measurable good events is required in the header.
-/

/-! Setwise domination with vanishing error implies absolute continuity on
one almost-everywhere event. The good events need only have failure probability
tending to zero; no summability or measurability of the absolute-continuity
predicate is needed. The absolutely continuous reference may change at every
accuracy. -/

open Set Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Probability

/-- Vanishing failure probabilities give arbitrarily accurate good events
almost everywhere, without a summability assumption. -/
theorem ae_frequently_mem_of_compl_measure_tendsto_zero
    {S : Type*} [MeasurableSpace S] (R : Measure S) (G : ℕ → Set S)
    (hfailure : Tendsto (fun n ↦ R (G n)ᶜ) atTop (𝓝 0)) :
    ∀ᵐ s ∂R, ∃ᶠ n in atTop, s ∈ G n := by
  let E : ℕ → Set S := fun m ↦ {s | ∀ n, m ≤ n → s ∉ G n}
  have hzero (m : ℕ) : R (E m) = 0 := by
    apply le_antisymm _ bot_le
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hfailure
    filter_upwards [eventually_ge_atTop m] with n hn
    exact measure_mono (fun s hs ↦ hs n hn)
  have hnot : ∀ᵐ s ∂R, ∀ m, s ∉ E m := by
    rw [ae_all_iff]
    intro m
    apply ae_iff.mpr
    simpa only [not_not, Set.setOf_mem_eq] using hzero m
  filter_upwards [hnot] with s hs
  apply frequently_atTop.mpr
  intro m
  have hm : ¬ ∀ n, m ≤ n → s ∉ G n := hs m
  push Not at hm
  exact hm

/-- All sets are controlled on the same good event. This order of quantifiers
allows the conclusion to handle every reference-null set simultaneously. -/
theorem ae_absolutelyContinuous_of_domination_failures_tendsto_zero
    {S X : Type*} [MeasurableSpace S] [MeasurableSpace X]
    (R : Measure S) (source : S → Measure X) (reference : Measure X)
    (approximant : ℕ → Measure X)
    (hac : ∀ n, approximant n ≪ reference)
    (error : ℕ → ℝ≥0∞) (herror : Tendsto error atTop (𝓝 0))
    (G : ℕ → Set S)
    (hgood : ∀ n, ∀ s ∈ G n, ∀ B : Set X,
      source s B ≤ approximant n B + error n)
    (hfailure : Tendsto (fun n ↦ R (G n)ᶜ) atTop (𝓝 0)) :
    ∀ᵐ s ∂R, source s ≪ reference := by
  filter_upwards [ae_frequently_mem_of_compl_measure_tendsto_zero R G hfailure] with s hs
  intro B hB
  apply le_antisymm _ bot_le
  apply le_of_tendsto_of_tendsto_of_frequently tendsto_const_nhds herror
  exact hs.mono fun n hn ↦ by simpa only [hac n hB, zero_add] using hgood n s hn B

end OTSelector.Probability
