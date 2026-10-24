import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Prod

/-!
## Lemma skeleton

* **Conditions:** Finite Borel measures with full-mass compact carriers on the two factors; the cost is continuous on their product.
* **Objects:** Integrability of the paired cost under the original product measure.
* **Proof detail:** The cost is bounded on the compact product, whose complement is null; apply the finite-measure bounded-integrand criterion.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99

**Relationship to the sources:** Elementary compact-carrier corollary of the bounded-integral estimate; no global bound on the ambient noncompact space is assumed.
-/

/-!
# Continuous paired costs under compactly supported original laws

The two original finite measures may live on noncompact spaces. Their full-mass
compact carriers suffice for integrability of every continuous paired cost,
with no globally bounded extension and no change of sampling law.
-/

open MeasureTheory Set

namespace OTSelector.Probability

variable {S T : Type*} [TopologicalSpace S] [TopologicalSpace T]
  [MeasurableSpace S] [MeasurableSpace T] [BorelSpace S] [BorelSpace T]
  [T2Space S] [T2Space T] [SecondCountableTopologyEither S T]

/-- Compact full-mass carriers give integrability of the original continuous paired cost. -/
theorem integrable_continuous_of_compact_carriers
    (μ : Measure S) [IsFiniteMeasure μ] (ν : Measure T) [IsFiniteMeasure ν]
    {A : Set S} {B : Set T} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    {c : S × T → ℝ} (hc : Continuous c) : Integrable c (μ.prod ν) := by
  have h : IntegrableOn c (A ×ˢ B) (μ.prod ν) :=
    hc.continuousOn.integrableOn_compact (hA.prod hB)
  rw [IntegrableOn, ← Measure.prod_restrict,
    Measure.restrict_eq_self_of_ae_mem hμ, Measure.restrict_eq_self_of_ae_mem hν] at h
  exact h

end OTSelector.Probability
