import OTSelector.MeasureTheory.FiniteDensityCellReadout
import OTSelector.Transport.Neumann.EndpointCoupling
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiCellLaw.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiCellLaw`; the selected original proof blocks follow. -/
section

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







/-- Quantizing the genuine original density law produces exactly the finite
weighted measure of its literal cell integrals, including zero-mass cells. -/
theorem originalDensityCellWeight_map_withDensity
    {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (T : X → I) (hT : Measurable T) :
    (μ.withDensity (fun x ↦ ENNReal.ofReal (f x))).map T =
      finiteWeightedMeasure (originalDensityCellWeight μ f T) := by
  classical
  apply Measure.ext_of_singleton
  intro i
  rw [Measure.map_apply hT (measurableSet_singleton i),
    withDensity_apply _ (hT (measurableSet_singleton i)),
    ← ofReal_integral_eq_lintegral_ofReal hf.restrict (ae_restrict_of_ae hf0)]
  simp [finiteWeightedMeasure, originalDensityCellWeight, Pi.single_apply]

end OTSelector.Reconstruction

end
end
