import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Moments.Variance

/-!
## Lemma skeleton

* **Conditions:** Probability measures on arbitrary measurable spaces and a measurable bounded real product observable. The separate oscillation estimate assumes a uniform pairwise difference bound.
* **Objects:** The oscillation variance bound, integrability of fiber variances, and variance = mean fiber variance + variance of fiber means.
* **Proof detail:** Use boundedness to establish all L2 and slice-integrability inputs. Expand each variance as second moment minus squared mean and use Fubini; the oscillation bound follows after centering.

## Mathematical sources

* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 1.6.3, p. 33, equations (1.6.2)–(1.6.4).
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=41
* Rick Durrett, *Probability: Theory and Examples, 5th edition (11 January 2019)*, Section 4.1, Exercises 4.1.6–4.1.7, p. 216.
  https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=224
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 5B, Theorem 5.32 (Fubini), pp. 132–133.
  https://measure.axler.net/MIRA.pdf#page=147

**Relationship to the sources:** Bounded product-space version of the law of total variance, proved directly by Fubini. The C^2 oscillation bound is valid without a sharp-constant claim.
-/

/-!
# Variance decomposition for bounded product observables

Fubini and the ordinary second-moment formula decompose the variance under a
product probability. Boundedness supplies every integrability input. This is the
recursive step for coordinatewise concentration of the actual empirical pressure.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Probability

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A uniform oscillation bound controls variance under any probability law. -/
theorem variance_le_sq_of_oscillation (μ : Measure X) [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : Measurable f) {C : ℝ}
    (hosc : ∀ x y, |f x - f y| ≤ C) : variance f μ ≤ C ^ 2 := by
  let x₀ : X := Classical.choice (nonempty_of_isProbabilityMeasure μ)
  have hbound : ∀ᵐ x ∂μ, f x ∈ Set.Icc (f x₀ - C) (f x₀ + C) := by
    apply Filter.Eventually.of_forall
    intro x
    have h := abs_le.mp (hosc x x₀)
    constructor <;> linarith
  have h := variance_le_sq_of_bounded hbound hf.aemeasurable
  convert h using 1
  ring

/-- The variance of a bounded observable is the mean of its conditional
variances plus the variance of its conditional means, for the actual product law. -/
theorem variance_prod_of_bounded (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : X × Y → ℝ} (hf : Measurable f) {M : ℝ}
    (hbound : ∀ z, |f z| ≤ M) :
    Integrable (fun x ↦ variance (fun y ↦ f (x, y)) ν) μ ∧
      variance f (μ.prod ν) =
        (∫ x, variance (fun y ↦ f (x, y)) ν ∂μ) +
          variance (fun x ↦ ∫ y, f (x, y) ∂ν) μ := by
  let g : X → ℝ := fun x ↦ ∫ y, f (x, y) ∂ν
  have hf2 : MemLp f 2 (μ.prod ν) :=
    MemLp.of_bound hf.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using hbound z)
  have hslice (x : X) : MemLp (fun y ↦ f (x, y)) 2 ν :=
    MemLp.of_bound (hf.comp measurable_prodMk_left).aestronglyMeasurable M
      (Filter.Eventually.of_forall fun y ↦ by simpa only [Real.norm_eq_abs] using hbound (x, y))
  have hg : Measurable g := hf.stronglyMeasurable.integral_prod_right'.measurable
  have hgbound (x : X) : |g x| ≤ M := by
    simpa [g, Real.norm_eq_abs] using
      norm_integral_le_of_norm_le_const (μ := ν) (Filter.Eventually.of_forall fun y ↦
        (show ‖f (x, y)‖ ≤ M by simpa only [Real.norm_eq_abs] using hbound (x, y)))
  have hg2 : MemLp g 2 μ := MemLp.of_bound hg.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x ↦ by simpa only [Real.norm_eq_abs] using hgbound x)
  have hvariance : (fun x ↦ variance (fun y ↦ f (x, y)) ν) =
      (fun x ↦ (∫ y, f (x, y) ^ 2 ∂ν) - g x ^ 2) := by
    funext x
    exact variance_eq_sub (hslice x)
  have hvarint : Integrable (fun x ↦ variance (fun y ↦ f (x, y)) ν) μ := by
    rw [hvariance]
    exact hf2.integrable_sq.integral_prod_left.sub hg2.integrable_sq
  refine ⟨hvarint, ?_⟩
  rw [hvariance, integral_sub hf2.integrable_sq.integral_prod_left hg2.integrable_sq,
    variance_eq_sub hf2, variance_eq_sub hg2]
  simp only [Pi.pow_apply]
  rw [integral_prod _ hf2.integrable_sq, integral_prod _ (hf2.integrable (by norm_num))]
  ring

end OTSelector.Probability
