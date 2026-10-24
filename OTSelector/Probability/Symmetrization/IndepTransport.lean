import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
/-
Adapted from StatLean/Stat-Lean commit e1ef06bf52d2a8896439c5b59d982d9aad28a254,
`StatLean/ConcentrationInequalities/ForMathlib/IndepTransport.lean`.
Original source licensed under Apache-2.0.
-/


/-!
# Probability.Symmetrization.IndepTransport

## Lemma skeleton

* **Conditions:** A finite independent family of measurable maps on a probability space, with the specified pushforward-integrand measurability; optionally an independent passenger product factor.

* **Objects:** Equal integrals on the abstract sample space and the explicit product of marginal laws.

* **Proof detail:** Identify the joint pushforward law with the product of the marginals, apply change of variables, and regroup the extra product coordinate when present.

## Mathematical sources

- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56): Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf): Sections 254G–254I and 254N–254O, infinite products, coordinate maps and subproducts.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.

Source relation (adapter): Law-transport wrappers. Independence is an actual premise, and no integrability requirement is invented for the totalized integral-map identity.
-/

/-!
# Integral transport between independence hypotheses and canonical products

Theorem-agnostic wrappers translating abstract-sample-space independence
hypotheses into integrals over explicit canonical product measures. For an
independent family $X_i : \Omega \to \beta_i$,
$$ \int_\Omega G\bigl((X_i(\omega))_i\bigr)\, d\mu
   \;=\; \int G \, d\Bigl(\bigotimes_i (X_i)_\# \mu\Bigr), $$
with a variant carrying a passenger product factor, and the
introduce/eliminate-auxiliary-randomness identity for a pair of independent
maps: if $A \perp B$ and $B$ has law $\rho$, then
$$ \int_\Omega G(A(\omega), B(\omega))\, d\mu
   \;=\; \int_{\Omega \times \gamma} G(A(\omega'), z)\, d(\mu \otimes \rho). $$
These are the three moves every symmetrization assembly file and every
downstream consumer (VC, chaining) uses to move between "signs on `Ω`" and
"signs as a product coordinate".

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §6.3 (joint law of an independent family;
footnote 7 on enlarging the probability space with independent signs). Pure
plumbing — no numbered theorem.

**Proof formalization notes.** All three lemmas are wraps of pin-verified
Mathlib bricks: `ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map`,
`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`,
`MeasureTheory.MeasurePreserving.prod`, and `MeasureTheory.integral_map`.
Measurability of the integrand is taken as `AEStronglyMeasurable` with respect
to the *pushforward* measure — the natural hypothesis for `integral_map`.
Mathlib-only imports; candidate upstream. The passenger-coordinate theorem is
`integral_prod_eq_integral_pi_prod`; both transports are direct wraps.

**Bibliographic comments.** The identification of an independent family with
the product of its marginal laws is Kolmogorov's construction (*Grundbegriffe
der Wahrscheinlichkeitsrechnung*, 1933); the "enlarge the space by an
independent auxiliary sequence" device is standard in Banach-space probability
(Ledoux–Talagrand, *Probability in Banach Spaces*, 1991, Ch. 6).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace OTSelector.Probability.Symmetrization

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Transport an integral of a function of an independent family to the
product of the marginal laws (HDP §6.3: the joint law of an independent
family is the product of the marginals). -/
theorem integral_eq_integral_pi_map {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {X : (i : ι) → Ω → β i}
    -- LEAN-ONLY: a.e.-measurability of the family; matches
    -- `iIndepFun_iff_map_fun_eq_pi_map`'s hypothesis shape
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (h_indep : iIndepFun X μ)
    {G : ((i : ι) → β i) → ℝ}
    -- LEAN-ONLY: integrand measurability w.r.t. the pushforward; the natural
    -- `integral_map` side condition
    (hG : AEStronglyMeasurable G (Measure.pi fun i => μ.map (X i))) :
    ∫ ω, G (fun i => X i ω) ∂μ = ∫ y, G y ∂(Measure.pi fun i => μ.map (X i)) := by
  have hφ : AEMeasurable (fun ω i => X i ω) μ := aemeasurable_pi_lambda _ h_meas
  have hmap : μ.map (fun ω i => X i ω) = Measure.pi (fun i => μ.map (X i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map h_meas).mp h_indep
  rw [← hmap] at hG ⊢
  exact (integral_map hφ hG).symm

/-- Transport with a passenger product factor: an integral over `μ.prod ρ` of
a function of the independent family in the first coordinate equals the
integral over the canonical product `(⊗ᵢ (Xᵢ)#μ).prod ρ`. -/
theorem integral_prod_eq_integral_pi_prod {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {X : (i : ι) → Ω → β i}
    -- LEAN-ONLY: measurability of the family
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun X μ)
    {γ : Type*} {mγ : MeasurableSpace γ} {ρ : Measure γ} [IsProbabilityMeasure ρ]
    {G : (((i : ι) → β i) × γ) → ℝ}
    -- LEAN-ONLY: integrand measurability w.r.t. the pushforward product
    (hG : AEStronglyMeasurable G ((Measure.pi fun i => μ.map (X i)).prod ρ)) :
    ∫ p, G (fun i => X i p.1, p.2) ∂(μ.prod ρ)
      = ∫ q, G q ∂((Measure.pi fun i => μ.map (X i)).prod ρ) := by
  have hφ : Measurable (fun ω i => X i ω) := measurable_pi_lambda _ h_meas
  have hmapφ : μ.map (fun ω i => X i ω) = Measure.pi (fun i => μ.map (X i)) :=
    (iIndepFun_iff_map_fun_eq_pi_map (fun i => (h_meas i).aemeasurable)).mp h_indep
  have hψ : Measurable (fun p : Ω × γ => (fun i => X i p.1, p.2)) :=
    (measurable_pi_lambda _ (fun i => (h_meas i).comp measurable_fst)).prodMk measurable_snd
  have hmapψ : (μ.prod ρ).map (fun p : Ω × γ => (fun i => X i p.1, p.2))
      = (Measure.pi fun i => μ.map (X i)).prod ρ := by
    rw [show (fun p : Ω × γ => (fun i => X i p.1, p.2))
          = Prod.map (fun ω i => X i ω) id from rfl,
        ← Measure.map_prod_map μ ρ hφ measurable_id, Measure.map_id, hmapφ]
  rw [← hmapψ, integral_map hψ.aemeasurable (by rw [hmapψ]; exact hG)]

end OTSelector.Probability.Symmetrization
