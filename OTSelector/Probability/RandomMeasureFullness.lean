import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Random Measure Fullness

Conditions: A.e. domination of random measures and equal expected local masses on a countable cover with finite expected dominating masses.

Objects: A.e. equality of the complete random measures from their local mean identity.

Proof detail: Apply the actual dominated random-measure equality theorem to the supplied countable cover.

Relation to primary sources: A reusable wrapper around the locally proved zero-defect/countable-cover theorem; fullness is an equality conclusion, not an assumption.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.4, Exercise 1.4.1, p. 24. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=32
-/
/-! Equal local mean masses and original domination recover whole random measures. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- Random measures dominated by the original input agree almost surely if
their expected masses agree on a countable cover with finite input
means. Neither random measure is required to be globally finite. -/
theorem ae_randomMeasure_eq_of_le_of_local_mean_eq
    {Ω X I : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [Countable I]
    (P : Measure Ω) (μ ν : Ω → Measure X)
    (K : I → Set X) (hcover : ⋃ i, K i = univ)
    (hdom : ∀ᵐ ω ∂P, μ ω ≤ ν ω)
    (hν : ∀ i, AEMeasurable (fun ω ↦ ν ω (K i)) P)
    (hfinite : ∀ i, (∫⁻ ω, ν ω (K i) ∂P) < ∞)
    (hmean : ∀ i, (∫⁻ ω, μ ω (K i) ∂P) = ∫⁻ ω, ν ω (K i) ∂P) :
    ∀ᵐ ω ∂P, μ ω = ν ω := by
  have hcounts (i : I) : ∀ᵐ ω ∂P, μ ω (K i) = ν ω (K i) := by
    apply ae_eq_of_ae_le_of_lintegral_le
      (hdom.mono fun ω hω ↦ hω (K i))
    · exact (lt_of_le_of_lt (lintegral_mono_ae
        (hdom.mono fun ω hω ↦ hω (K i))) (hfinite i)).ne
    · exact hν i
    · exact (hmean i).symm.le
  have hνfinite (i : I) : ∀ᵐ ω ∂P, ν ω (K i) < ∞ :=
    ae_lt_top' (hν i) (hfinite i).ne
  filter_upwards [hdom, ae_all_iff.mpr hcounts, ae_all_iff.mpr hνfinite]
    with ω hdom hcounts hνfinite
  apply Measure.ext_of_iUnion_eq_univ hcover
  intro i
  let _ : IsFiniteMeasure ((μ ω).restrict (K i)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      lt_of_le_of_lt (hdom (K i)) (hνfinite i)⟩
  apply Measure.eq_of_le_of_measure_univ_eq
  · exact Measure.restrict_mono_measure hdom (K i)
  · simpa only [Measure.restrict_apply_univ] using hcounts i

end OTSelector.Probability
