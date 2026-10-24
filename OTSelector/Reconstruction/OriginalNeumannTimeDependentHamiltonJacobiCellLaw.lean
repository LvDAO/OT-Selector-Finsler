import OTSelector.Transport.Neumann.CellLaw
import OTSelector.MeasureTheory.FiniteDensityCellReadout
import OTSelector.Transport.Neumann.EndpointCoupling

/-!
Conditions: An integrable nonnegative density and a measurable map into a finite measurable index set.

Objects: The exact pushed-forward density law as the finite measure of actual density-cell weights.

Proof detail: Evaluate both measures on singletons using map-withDensity and sum the finite singleton partition.

Sources: D. H. Fremlin, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40 (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27); D. H. Fremlin, Section 235G, integration along an inverse-measure-preserving map (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf).
Relation: Finite density-cell measure adapter; weights remain those of the original input density.
-/

/-! The actual nonnegative density law has exactly the original finite cell weights. -/
open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

variable {X : Type*} [MeasurableSpace X]

/-- The actual density law has precisely the original integral as its total mass. -/
theorem originalDensityWithDensity_univ (μ : Measure X) (f : X → ℝ)
    (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) univ =
      ENNReal.ofReal (∫ x, f x ∂μ) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hf hf0]

/-- An integrable nonnegative original density gives a finite actual measure. -/
theorem originalDensityWithDensity_isFiniteMeasure (μ : Measure X) (f : X → ℝ)
    (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) :
    IsFiniteMeasure (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) := by
  constructor
  rw [originalDensityWithDensity_univ μ f hf hf0]
  exact ENNReal.ofReal_lt_top

/-- Unit original density mass gives an actual probability measure. -/
theorem originalDensityWithDensity_isProbabilityMeasure (μ : Measure X) (f : X → ℝ)
    (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hmass : ∫ x, f x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))) := by
  constructor
  rw [originalDensityWithDensity_univ μ f hf hf0, hmass, ENNReal.ofReal_one]



end OTSelector.Reconstruction
