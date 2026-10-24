import LeanLevy.RandomMeasure.PoissonRandomMeasure

/-!
# Probability.PoissonRandomMeasure

## Lemma skeleton

* **Conditions:** The vendored Poisson point-family construction with sigma-finite intensity; two disjoint measurable sets each have finite intensity.

* **Objects:** Independence of the two actual random-measure counts.

* **Proof detail:** Apply the construction’s disjoint-count independence theorem and rewrite the two coordinate evaluations as counts.

## Mathematical sources

- [Günter Last; Mathew Penrose, Lectures on the Poisson Process](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=31): Section 3.1, Definition 3.1(i)–(ii), p. 19.

Source relation (adapter): Direct two-set instance of complete independence in the Poisson-process definition; the public file only re-exports the existing construction.
-/

/-!
# Spatial Poisson random measures

This module re-exports the vendored LeanLevy construction of a spatial Poisson
random measure with an arbitrary σ-finite intensity.  The construction provides
independent Poisson counts on disjoint measurable sets, Campbell's formula, and
thinning.  These are the stochastic inputs of the finite-volume pressure layer;
the vendored sources are MIT licensed (see `vendor/leanlevy/LICENSE`).
-/

open MeasureTheory ProbabilityTheory

namespace OTSelector.Probability

/-- Poisson random measures have independent counts on disjoint finite-mass
measurable sets. -/
theorem poissonRandomMeasure_indepFun_disjoint
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : IsPoissonPointFamily K X m μ)
    {A B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hfinA : m A < ⊤) (hfinB : m B < ⊤) (hdisj : Disjoint A B) :
    IndepFun (fun ω ↦ poissonRandomMeasure K X ω A)
      (fun ω ↦ poissonRandomMeasure K X ω B) μ :=
  indepFun_poissonRandomMeasure_apply h hA hB hfinA hfinB hdisj

end OTSelector.Probability
