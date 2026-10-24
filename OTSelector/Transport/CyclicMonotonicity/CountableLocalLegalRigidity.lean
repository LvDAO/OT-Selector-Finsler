import OTSelector.Transport.CyclicMonotonicity.CountableLegalTargetRigidity
import OTSelector.Transport.CyclicMonotonicity.CountableTargetRigidity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CountableLocalLegalTwoCycleRigidity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CountableLocalLegalTwoCycleRigidity`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.CountableLocalLegalTwoCycleRigidity

**Conditions:** Countably many legal windows and countable targets; each window has the exact local two-cycle/atomless-difference property, and every potential split is covered by one common window.

**Objects:** Almost-everywhere single-valued full relation and equality of original plans, without truncating either marginal.

**Proof detail:** Apply legal rigidity separately on each window, intersect the countably many full source events, and use the split-cover property to exclude every pair of distinct target values; then apply common-source measure uniqueness.

**Sources:** [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=254), Appendix A.1, Theorem A.5, p. 242; [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf), Section 2.2, Definition 2.1 and equations (2.6)–(2.7), p. 12; Section 2.3, Remark 2.13, equations (2.14)–(2.15), p. 20.

Source relation (generalization): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Countably many local legal windows suffice for rigidity of the full
relation. A possible split needs only to lie in one common window. The two
original plans are never truncated, so their common source marginal is kept.
Costs and legal domains may vary with the window. -/

open Set MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction

variable {S J K : Type*} [MeasurableSpace S] [MeasurableSpace J]
  [Countable J] [Countable K]

/-- Local legal two-cycle rigidity rules out every split of the full relation
when each pair of distinct target choices is covered by one common window. -/
theorem ae_single_valued_of_countable_local_legal_twoCycle
    (μ : Measure S) (Γ : Set (S × J)) (D : K → Set (S × J))
    (hD : ∀ k, MeasurableSet (D k)) (cost : K → S → J → ℝ)
    (hcycle : ∀ k, IsTwoCycleMonotoneOn (cost k) (D k) (Γ ∩ D k))
    (hc : ∀ k i j, AEMeasurable (fun x ↦ cost k x i - cost k x j)
      (μ.restrict (commonLegalSource (D k) i j)))
    (hatom : ∀ k i j, i ≠ j → NullSingletonClass
      ((μ.restrict (commonLegalSource (D k) i j)).map
        (fun x ↦ cost k x i - cost k x j)))
    (hcover : ∀ᵐ x ∂μ, ∀ i j, i ≠ j → (x, i) ∈ Γ → (x, j) ∈ Γ →
      ∃ k, (x, i) ∈ D k ∧ (x, j) ∈ D k) :
    ∀ᵐ x ∂μ, ∀ i j, (x, i) ∈ Γ → (x, j) ∈ Γ → i = j := by
  have hlocal : ∀ᵐ x ∂μ, ∀ k i j,
      (x, i) ∈ Γ ∩ D k → (x, j) ∈ Γ ∩ D k → i = j := by
    apply ae_all_iff.mpr
    intro k
    exact (hcycle k).ae_single_valued (hD k) inter_subset_right (hc k) (hatom k)
  filter_upwards [hlocal, hcover] with x hx hcx i j hi hj
  by_cases hij : i = j
  · exact hij
  obtain ⟨k, hki, hkj⟩ := hcx i j hij hi hj
  exact hx k i j ⟨hi, hki⟩ ⟨hj, hkj⟩

/-- The SAME full plans agree after local-window rigidity. No equality of
truncated source marginals or common target marginal is required. -/
theorem measure_eq_of_countable_local_legal_twoCycle
    [MeasurableSingletonClass J]
    (μ : Measure S) (Γ : Set (S × J)) (hΓ : MeasurableSet Γ)
    (D : K → Set (S × J)) (hD : ∀ k, MeasurableSet (D k))
    (cost : K → S → J → ℝ)
    (hcycle : ∀ k, IsTwoCycleMonotoneOn (cost k) (D k) (Γ ∩ D k))
    (hc : ∀ k i j, AEMeasurable (fun x ↦ cost k x i - cost k x j)
      (μ.restrict (commonLegalSource (D k) i j)))
    (hatom : ∀ k i j, i ≠ j → NullSingletonClass
      ((μ.restrict (commonLegalSource (D k) i j)).map
        (fun x ↦ cost k x i - cost k x j)))
    (hcover : ∀ᵐ x ∂μ, ∀ i j, i ≠ j → (x, i) ∈ Γ → (x, j) ∈ Γ →
      ∃ k, (x, i) ∈ D k ∧ (x, j) ∈ D k)
    (π₀ π₁ : Measure (S × J))
    (hsource₀ : π₀.map Prod.fst = μ) (hsource₁ : π₁.map Prod.fst = μ)
    (hcarried₀ : ∀ᵐ p ∂π₀, p ∈ Γ) (hcarried₁ : ∀ᵐ p ∂π₁, p ∈ Γ) :
    π₀ = π₁ :=
  measure_eq_of_common_ae_single_valued_relation hΓ
    (ae_single_valued_of_countable_local_legal_twoCycle μ Γ D hD cost hcycle hc hatom hcover)
    hsource₀ hsource₁ hcarried₀ hcarried₁

end OTSelector.Reconstruction

end
end
