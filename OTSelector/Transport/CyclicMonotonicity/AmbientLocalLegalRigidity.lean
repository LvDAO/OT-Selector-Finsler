import OTSelector.Transport.CyclicMonotonicity.AmbientCountableTargetRigidity
import OTSelector.Transport.CyclicMonotonicity.CountableLegalTargetRigidity
import OTSelector.Transport.CyclicMonotonicity.CountableLocalLegalRigidity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteLocalLegalTargetRigidity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteLocalLegalTargetRigidity`; the selected original proof blocks follow. -/
section

/-!
Conditions: Two ambient plans share a source law and countable measurable target cloud, and their carried support obeys local two-cycle monotonicity with atomless pairwise cost differences on common legal windows.

Objects: Equality of the unchanged two plans.

Proof detail: Put any simultaneous distinct target choices into a common window, apply two-cycle threshold rigidity and exclude ties by the atomless difference law; countability combines the null sets.

Sources: Gabriel Peyré, Section 5.2, equations (5.6)–(5.8), pp. 94–96 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=98); D. H. Fremlin, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf); D. H. Fremlin, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31 (https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30).
Relation: Countable/local-window generalization of semidiscrete no-tie rigidity, proved in the library. It assumes no new truncated-plan marginal identity.
-/

/-! Local legal windows determine the unchanged ambient plans on their common
countable target cloud. Only two simultaneous target choices need a common
window; no truncated-plan source or target marginal is introduced. -/

open Set MeasureTheory OTSelector.Reconstruction
noncomputable section
namespace OTSelector.Probability

variable {S Y J K : Type*} [MeasurableSpace S] [MeasurableSpace Y]
  [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J] [Countable K]

/-- Ambient equality follows from countably many locally rigid legal relations.
Their costs may differ, and the original target marginals need not be equal. -/
theorem ambient_plan_eq_of_countable_target_local_legal_twoCycle
    (μ : Measure S) (π₀ π₁ : Measure (S × Y))
    (y : J → Y) (hy : MeasurableEmbedding y)
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (htarget₀ : ∀ᵐ p ∂π₀, p.2 ∈ range y) (htarget₁ : ∀ᵐ p ∂π₁, p.2 ∈ range y)
    (Γ : Set (S × Y)) (hΓ : MeasurableSet Γ)
    (hcarried₀ : ∀ᵐ p ∂π₀, p ∈ Γ) (hcarried₁ : ∀ᵐ p ∂π₁, p ∈ Γ)
    (D : K → Set (S × Y)) (hD : ∀ k, MeasurableSet (D k))
    (cost : K → S → Y → ℝ)
    (hcycle : ∀ k, IsTwoCycleMonotoneOn (cost k) (D k) (Γ ∩ D k))
    (hc : ∀ k i j, AEMeasurable (fun x ↦ cost k x (y i) - cost k x (y j))
      (μ.restrict (commonLegalSource (D k) (y i) (y j))))
    (hatom : ∀ k i j, i ≠ j → NullSingletonClass
      ((μ.restrict (commonLegalSource (D k) (y i) (y j))).map
        (fun x ↦ cost k x (y i) - cost k x (y j))))
    (hcover : ∀ᵐ x ∂μ, ∀ i j, i ≠ j → (x, y i) ∈ Γ → (x, y j) ∈ Γ →
      ∃ k, (x, y i) ∈ D k ∧ (x, y j) ∈ D k) : π₀ = π₁ := by
  apply ambient_plan_eq_of_countable_target_ae_single_valued μ π₀ π₁ y hy
    hsource₀ hsource₁ htarget₀ htarget₁ Γ hΓ hcarried₀ hcarried₁
  exact ae_single_valued_of_countable_local_legal_twoCycle μ ((Prod.map id y) ⁻¹' Γ)
    (fun k ↦ (Prod.map id y) ⁻¹' D k)
    (fun k ↦ (hD k).preimage (measurable_id.prodMap hy.measurable))
    (fun k x j ↦ cost k x (y j))
    (fun k x i x' j hi hj hcross hcross' ↦
      hcycle k x (y i) x' (y j) hi hj hcross hcross') hc hatom hcover

end OTSelector.Probability

end
end
