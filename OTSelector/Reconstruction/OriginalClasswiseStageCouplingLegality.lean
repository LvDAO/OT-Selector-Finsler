import OTSelector.Transport.Coupling.FiniteStageLegality
import OTSelector.Transport.Coupling.FiniteOrderedStages
import OTSelector.Transport.Coupling.MixtureLabelTransfer

/-!
Conditions: Finite labeled stage couplings have the actual successive marginals and finite quadratic costs; the strict-order consequence has disjoint source/target colors at each stage.

Objects: A pseudometric ignoring labels, strict ordered classwise coupling and forbidden-label matrix zeros.

Proof detail: Lift smoothing while retaining labels, glue the actual successive couplings, compare nondecreasing labels and eliminate equality using the zero-color condition; forbidden classes have zero carried mass.

Sources: Gabriel Peyré, Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185); D. H. Fremlin, 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary (https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25); D. H. Fremlin, Section 235G, integration along an inverse-measure-preserving map (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf).
Relation: Derived finite-stage gluing/label-support construction. The factor N in quadratic cost is the local path Cauchy–Schwarz bound, not an optimal constant.
-/

/-! Strict class order and actual RN unsmoothing retain the same genuine
quadratic coupling, original labels, physical cost and allowed class pairs. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 300000





/-- The same labelled coupling has exactly its original physical quadratic
cost under the induced pseudometric; no product-metric label penalty occurs. -/
theorem classPhysical_quadratic_integral_eq
    {C E : Type*} [MeasurableSpace C] [MeasurableSpace E] [PseudoMetricSpace E]
    (Γ : Measure ((C × E) × (C × E))) :
    letI := classPhysicalPseudoMetricSpace C E
    (∫ p, dist p.1 p.2 ^ 2 ∂Γ) = ∫ p, dist p.1.2 p.2.2 ^ 2 ∂Γ := rfl








end OTSelector.Reconstruction
