import LeanPool.Vlasov.OT.Coupling
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import OTSelector.Geometry.Finsler.LengthIsometry
import OTSelector.Transport.Coupling.CostEquivalence

/-!
## Lemma skeleton

* **Conditions:** A tangent-length-preserving C1 manifold diffeomorphism and Borel measurable marginal spaces.
* **Objects:** Every pushed-forward length-cost coupling and the full set of optimal couplings, including infinite costs and ties.
* **Proof detail:** Use the proved geometric extended-distance identity as the pointwise cost identity in the generic measurable-equivalence coupling theorem.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, pp. 313–314, length distance, Definition 4.1 and Lemma 4.2, equations (4–1)–(4–4).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Gabriel Peyré; Marco Cuturi, *Computational Optimal Transport (2019 author version)*, Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.
  https://optimaltransport.github.io/pdf/ComputationalOT.pdf
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 235G, integration along an inverse-measure-preserving map.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** This is a transport specialization combining the geometry lemma and pushforward calculus. BCS/Shen do not claim this OT theorem; no optimizer is selected or assumed unique.
-/

/-!
# Optimal couplings under length isometries

The geometric tangent-length identity has already produced the actual
extended distance identity. Product pushforward then preserves the cost
of every coupling, including infinite costs, and identifies the complete
optimal-coupling set for the pushed-forward Borel marginals.

The two proofs are direct transport applications of the geometric result;
the Finsler length foundation does not import this adapter.
-/

open Set MeasureTheory
open scoped Manifold ENNReal ContDiff Topology

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [∀ x : M, ENorm (TangentSpace I x)] [normN : ∀ y : N, ENorm (TangentSpace J y)]

section Measures

variable [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

/-- The derived length-distance identity preserves every joint measure's extended cost,
including infinite costs, under the product pushforward. -/
theorem couplingCost_map_lengthDistance (e : Diffeomorph I J M N 1)
    (hpres : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J e x v‖ₑ = ‖v‖ₑ)
    (π : Measure (M × M)) :
    couplingCost (Manifold.riemannianEDist J)
        (π.map (e.toHomeomorph.toMeasurableEquiv.prodCongr e.toHomeomorph.toMeasurableEquiv)) =
      couplingCost (Manifold.riemannianEDist I) π :=
  couplingCost_map e.toHomeomorph.toMeasurableEquiv e.toHomeomorph.toMeasurableEquiv
    (Manifold.riemannianEDist I) (Manifold.riemannianEDist J)
    (riemannianEDist_diffeomorph e hpres) π

/-- A tangent-norm-preserving C¹ diffeomorphism preserves and reflects genuine length-cost
optimality for Borel marginals. Optimality compares against every feasible coupling. -/
theorem isOptimalCoupling_map_lengthDistance_iff (e : Diffeomorph I J M N 1)
    (hpres : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J e x v‖ₑ = ‖v‖ₑ)
    {μ ν : Measure M} {π : Measure (M × M)} :
    IsOptimalCoupling (Manifold.riemannianEDist J) (μ.map e) (ν.map e)
        (π.map (e.toHomeomorph.toMeasurableEquiv.prodCongr e.toHomeomorph.toMeasurableEquiv)) ↔
      IsOptimalCoupling (Manifold.riemannianEDist I) μ ν π :=
  isOptimalCoupling_map_iff e.toHomeomorph.toMeasurableEquiv e.toHomeomorph.toMeasurableEquiv
    (Manifold.riemannianEDist I) (Manifold.riemannianEDist J)
    (riemannianEDist_diffeomorph e hpres)

end Measures

end OTSelector.Geometry
