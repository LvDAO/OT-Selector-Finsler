import Mathlib.MeasureTheory.Measure.Support
import OTSelector.Transport.CyclicMonotonicity.CountableTargetRigidity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteCountableTargetRigidity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteCountableTargetRigidity`; the selected original proof blocks follow. -/
section

/-!
# Probability.CavitySemidiscreteCountableTargetRigidity

**Conditions:** A common countable target cloud is measurably embedded, both original plans have the same source marginal, and their carried relation is almost surely single-valued or satisfies the explicit two-cycle/atomlessness conditions.

**Objects:** Ambient plans, their pulled-back target-labelled plans and exact equality, including infinite mass.

**Proof detail:** Pull both plans back along the measured target embedding, apply countable-target single-valued rigidity, then push forward and recover each original plan exactly; averaged-support variants obtain a common carried relation.

**Sources:** [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=254), Appendix A.1, Theorem A.5, p. 242; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30), Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (generalization): The source combines measurable embedding transport and measure uniqueness with the locally proved atomless two-cycle rigidity. No general uniqueness of all optimal transport plans is attributed to the references.
-/

/-!
# Rigidity for ambient plans on a common countable target cloud

The actual source-target plans are pulled back along the measured target-label
embedding. The pullbacks recover the original plans exactly, so countable-target
rigidity gives equality in the original ambient space, including infinite mass.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S Y J : Type*} [MeasurableSpace S] [MeasurableSpace Y]
  [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]

/-- Pulling back the original countable target cloud reduces ambient equality to
an almost-everywhere single-valued carried relation, with no finite-mass premise. -/
theorem ambient_plan_eq_of_countable_target_ae_single_valued
    (μ : Measure S) (π₀ π₁ : Measure (S × Y))
    (y : J → Y) (hy : MeasurableEmbedding y)
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (htarget₀ : ∀ᵐ z ∂π₀, z.2 ∈ Set.range y)
    (htarget₁ : ∀ᵐ z ∂π₁, z.2 ∈ Set.range y)
    (Γ : Set (S × Y)) (hΓ : MeasurableSet Γ)
    (hcarried₀ : ∀ᵐ z ∂π₀, z ∈ Γ) (hcarried₁ : ∀ᵐ z ∂π₁, z ∈ Γ)
    (hsingle : ∀ᵐ s ∂μ, ∀ i j, (s, y i) ∈ Γ → (s, y j) ∈ Γ → i = j) :
    π₀ = π₁ := by
  let e : S × J → S × Y := Prod.map id y
  have he : MeasurableEmbedding e := MeasurableEmbedding.id.prodMap hy
  have hrange : Set.range e = {z : S × Y | z.2 ∈ Set.range y} := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.2, rfl⟩
    · rintro ⟨j, hj⟩
      exact ⟨(z.1, j), Prod.ext rfl hj⟩
  have hrecover (π : Measure (S × Y)) (ht : ∀ᵐ z ∂π, z.2 ∈ Set.range y) :
      (π.comap e).map e = π := by
    rw [he.map_comap, Measure.restrict_eq_self_of_ae_mem]
    simpa only [hrange, mem_ofPred_eq] using ht
  have hrec₀ := hrecover π₀ htarget₀
  have hrec₁ := hrecover π₁ htarget₁
  have hsource (π : Measure (S × Y)) (hrec : (π.comap e).map e = π) :
      (π.comap e).map Prod.fst = π.map Prod.fst := by
    calc
      _ = ((π.comap e).map e).map Prod.fst :=
        (Measure.map_map measurable_fst he.measurable).symm
      _ = _ := congrArg (fun ρ : Measure (S × Y) ↦ ρ.map Prod.fst) hrec
  have heq := OTSelector.Reconstruction.measure_eq_of_common_ae_single_valued_relation
    (Γ := e ⁻¹' Γ) (hΓ.preimage he.measurable) hsingle
    ((hsource π₀ hrec₀).trans hsource₀) ((hsource π₁ hrec₁).trans hsource₁)
    (ae_of_ae_map he.measurable.aemeasurable (hrec₀.symm ▸ hcarried₀))
    (ae_of_ae_map he.measurable.aemeasurable (hrec₁.symm ▸ hcarried₁))
  rw [← hrec₀, ← hrec₁, heq]

/-- The original ambient plans agree when they have the same source marginal, are
carried by one monotone relation, and use the same countable embedded target cloud. -/
theorem ambient_plan_eq_of_countable_target_twoCycle
    (μ : Measure S) (π₀ π₁ : Measure (S × Y))
    (y : J → Y) (hy : MeasurableEmbedding y)
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (htarget₀ : ∀ᵐ z ∂π₀, z.2 ∈ Set.range y)
    (htarget₁ : ∀ᵐ z ∂π₁, z.2 ∈ Set.range y)
    (c : S → Y → ℝ) (Γ : Set (S × Y)) (hΓ : MeasurableSet Γ)
    (hcycle : OTSelector.Reconstruction.IsTwoCycleMonotone c Γ)
    (hcarried₀ : ∀ᵐ z ∂π₀, z ∈ Γ) (hcarried₁ : ∀ᵐ z ∂π₁, z ∈ Γ)
    (hc : ∀ j, Measurable (fun s ↦ c s (y j)))
    (hatom : ∀ i j, i ≠ j →
      NullSingletonClass (μ.map (fun s ↦ c s (y i) - c s (y j)))) :
    π₀ = π₁ := by
  apply ambient_plan_eq_of_countable_target_ae_single_valued μ π₀ π₁ y hy
    hsource₀ hsource₁ htarget₀ htarget₁ Γ hΓ hcarried₀ hcarried₁
  exact OTSelector.Reconstruction.IsTwoCycleMonotone.ae_single_valued
    (c := fun s j ↦ c s (y j)) (Γ := (Prod.map id y) ⁻¹' Γ)
    (fun x i x' j hi hj ↦ hcycle x (y i) x' (y j) hi hj) hc hatom

/-- Equality of the original ambient plans follows from two-cycle monotonicity of the
support of their actual average and their common countably supported target marginal. -/
theorem ambient_plan_eq_of_countable_target_average_support
    [TopologicalSpace S] [TopologicalSpace Y]
    [OpensMeasurableSpace S] [OpensMeasurableSpace Y]
    [SecondCountableTopology S] [SecondCountableTopology Y]
    (μ : Measure S) (ν : Measure Y) (π₀ π₁ : Measure (S × Y))
    (y : J → Y) (hy : MeasurableEmbedding y) (hν : ∀ᵐ z ∂ν, z ∈ Set.range y)
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (htarget₀ : π₀.map Prod.snd = ν) (htarget₁ : π₁.map Prod.snd = ν)
    (c : S → Y → ℝ)
    (hcycle : OTSelector.Reconstruction.IsTwoCycleMonotone c
      (((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)).support))
    (hc : ∀ j, Measurable (fun s ↦ c s (y j)))
    (hatom : ∀ i j, i ≠ j →
      NullSingletonClass (μ.map (fun s ↦ c s (y i) - c s (y j)))) :
    π₀ = π₁ := by
  have hsupp : ∀ᵐ z ∂(2 : ℝ≥0∞)⁻¹ • (π₀ + π₁),
      z ∈ (((2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)).support) := Measure.support_mem_ae
  rw [Measure.ae_ennreal_smul_measure_iff (by simp), ae_add_measure_iff] at hsupp
  exact ambient_plan_eq_of_countable_target_twoCycle μ π₀ π₁ y hy hsource₀ hsource₁
    (ae_of_ae_map measurable_snd.aemeasurable (htarget₀.symm ▸ hν))
    (ae_of_ae_map measurable_snd.aemeasurable (htarget₁.symm ▸ hν))
    c _ Measure.isClosed_support.measurableSet hcycle hsupp.1 hsupp.2 hc hatom

end OTSelector.Probability


end
end
