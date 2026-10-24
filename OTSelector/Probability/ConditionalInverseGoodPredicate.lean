import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional Inverse Good Predicate

Conditions: Finite original measure, measurable label a and scalar u, a measurable reconstruction b, an almost-everywhere identity b(a(x),u(x))=x, and an arbitrary almost-everywhere good predicate.

Objects: Almost every actual conditional scalar law is concentrated on reconstructed good points and has at least one good time; two equal label marginals give a shared full label set.

Proof detail: The reconstruction pushes the actual joint label-clock law back to the original measure. Pull the full predicate through this pushforward, disintegrate, and use that each conditional scalar law is a probability law to obtain existence.

Relation to primary sources: These are local almost-everywhere transport lemmas. Good is not assumed measurable. Existence of a good time is pointwise at almost every label, with no measurable choice and no claim that the good times for two laws coincide.

References:
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
-/
/-!
# Good times under the original conditional clock laws

An almost-everywhere inverse of the original label-clock map transfers any
full-measure predicate to the existing conditional laws. Their probability
property gives good times on almost every label, simultaneously for two laws
with the same label distribution. No measurability of the predicate is required.
-/

open Set MeasureTheory ProbabilityTheory Filter

namespace OTSelector.Reconstruction

variable {M Z : Type*} [MeasurableSpace M] [MeasurableSpace Z]

/-- An almost-everywhere inverse transfers any full-measure property to almost
all original conditional clock laws, each of which has a good time. -/
theorem ae_condDistrib_good_of_ae_leftInverse
    (η : Measure M) [IsFiniteMeasure η]
    {a : M → Z} {u : M → ℝ} {b : Z × ℝ → M}
    (ha : Measurable a) (hu : Measurable u) (hb : Measurable b)
    (hbinv : ∀ᵐ x ∂η, b (a x, u x) = x)
    {Good : M → Prop} (hGood : ∀ᵐ x ∂η, Good x) :
    ∀ᵐ z ∂η.map a,
      (∀ᵐ t ∂condDistrib u a η z, Good (b (z, t))) ∧
        ∃ t : ℝ, Good (b (z, t)) := by
  have hrec : (η.map (fun x ↦ (a x, u x))).map b = η := by
    rw [Measure.map_map hb (ha.prodMk hu)]
    calc
      η.map (b ∘ fun x ↦ (a x, u x)) = η.map id := Measure.map_congr hbinv
      _ = η := Measure.map_id
  have hjoint : ∀ᵐ q ∂η.map (fun x ↦ (a x, u x)), Good (b q) :=
    ae_of_ae_map hb.aemeasurable (by rwa [hrec])
  rw [← compProd_map_condDistrib (μ := η) (X := a) hu.aemeasurable] at hjoint
  exact (Measure.ae_ae_of_ae_compProd hjoint).mono fun _ hz ↦ ⟨hz, hz.exists⟩

/-- Both original laws retain their separate good properties on one full set of
common labels. The two good times may differ and no selection measurability is asserted. -/
theorem ae_commonLabel_condDistrib_good_of_ae_leftInverse
    (μ ν : Measure M) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a : M → Z} {u : M → ℝ} {b : Z × ℝ → M}
    (ha : Measurable a) (hu : Measurable u) (hb : Measurable b)
    {lambda : Measure Z} (hμlabel : μ.map a = lambda) (hνlabel : ν.map a = lambda)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x)
    (hνinv : ∀ᵐ x ∂ν, b (a x, u x) = x)
    {Goodμ Goodν : M → Prop}
    (hμgood : ∀ᵐ x ∂μ, Goodμ x) (hνgood : ∀ᵐ x ∂ν, Goodν x) :
    ∀ᵐ z ∂lambda,
      ((∀ᵐ s ∂condDistrib u a μ z, Goodμ (b (z, s))) ∧
        ∃ s : ℝ, Goodμ (b (z, s))) ∧
      ((∀ᵐ t ∂condDistrib u a ν z, Goodν (b (z, t))) ∧
        ∃ t : ℝ, Goodν (b (z, t))) := by
  have hμ := ae_condDistrib_good_of_ae_leftInverse μ ha hu hb hμinv hμgood
  have hν := ae_condDistrib_good_of_ae_leftInverse ν ha hu hb hνinv hνgood
  rw [hμlabel] at hμ
  rw [hνlabel] at hν
  exact hμ.and hν

end OTSelector.Reconstruction
