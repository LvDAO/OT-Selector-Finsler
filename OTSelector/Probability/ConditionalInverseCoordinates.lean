import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional Inverse Coordinates

Conditions: Finite η; measurable label a with measurable equality, measurable scalar u and reconstruction b; b(a(x),u(x))=x almost everywhere.

Objects: Recovery of both the original label and clock under almost every actual conditional scalar law.

Proof detail: The coordinate recovery equalities define a measurable subset of the joint label-clock space. Push the a.e. inverse identity into that joint law, then disintegrate it and apply the iterated-a.e. rule.

Relation to primary sources: This is a local coordinate consistency consequence of the actual joint law, not a new disintegration axiom. No pointwise inverse off the original full-measure set is required.

References:
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452E, p. 20: consistency and strong consistency; 452G(a)–(c), p. 21: probability kernels and concentration on fibers. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=20
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
-/
/-!
# Original coordinates under conditional clock laws

The same almost-everywhere inverse of the original label-clock map recovers both
coordinates at almost every time of almost every conditional law. The measurable
coordinate equality passes directly through the original joint distribution.
-/

open Set MeasureTheory ProbabilityTheory Filter

namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z] [MeasurableEq Z]

/-- The supplied almost-everywhere inverse has the original label and clock at
almost every time of almost every original conditional clock law. -/
theorem ae_condDistrib_coordinates_of_ae_leftInverse
    (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} {b : Z × ℝ → M}
    (ha : Measurable a) (hu : Measurable u) (hb : Measurable b)
    (hbinv : ∀ᵐ x ∂η, b (a x, u x) = x) :
    ∀ᵐ z ∂η.map a, ∀ᵐ t ∂condDistrib u a η z,
      a (b (z, t)) = z ∧ u (b (z, t)) = t := by
  have hmeas : MeasurableSet {q : Z × ℝ |
      a (b q) = q.1 ∧ u (b q) = q.2} :=
    (measurableSet_eq_fun (ha.comp hb) measurable_fst).inter
      (measurableSet_eq_fun (hu.comp hb) measurable_snd)
  have hjoint : ∀ᵐ q ∂η.map (fun x ↦ (a x, u x)),
      a (b q) = q.1 ∧ u (b q) = q.2 := by
    apply (ae_map_iff (ha.prodMk hu).aemeasurable hmeas).mpr
    exact hbinv.mono fun _ hx ↦ ⟨congrArg a hx, congrArg u hx⟩
  rw [← compProd_map_condDistrib (μ := η) (X := a) hu.aemeasurable] at hjoint
  exact Measure.ae_ae_of_ae_compProd hjoint

end OTSelector.Reconstruction
