import OTSelector.Finite.LegalMatchingValue
import OTSelector.Finite.MaxCardValueMeasurable
import OTSelector.Finite.PartialMatching
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MarkedStationaryValueLegalOptimizer.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MarkedStationaryValueLegalOptimizer`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.MarkedStationaryValueLegalOptimizer

**Conditions:** An actual finite legal graph and signed costs depend measurably on the observations.

**Objects:** One exact legal optimizer chosen by a fixed enumeration, with measurable selected-edge events.

**Proof detail:** Enumerate finite matchings, prove attainment of the lexicographic cardinality/cost optimum, and take its least valid index; each optimality event is a finite collection of measurable cost comparisons.

**Sources:** [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106), Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces; [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# A measurable exact optimizer for the actual finite legal graph

One fixed enumeration resolves ties. Both the allowed graph and all signed edge
costs may depend measurably on the original observations. In particular the
selected core's edge events, needed by adaptive repair estimates, are measurable.
-/

open Set MeasureTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ}

/-- Exact signed optimality at the actual legal maximum cardinality. -/
def IsLegalOptimal (allowed : Finset (Fin m × Fin n)) (c : Fin m → Fin n → ℝ)
    (σ : OTSelector.PartialMatching m n) : Prop :=
  IsLegal allowed σ ∧ σ.card = legalMaximumCard allowed ∧ σ.cost c = legalMaximumValue allowed c

private def legalMatchingEnumeration (m n : ℕ) : ℕ → OTSelector.PartialMatching m n := by
  let _ : Encodable (OTSelector.PartialMatching m n) := Encodable.ofCountable _
  exact fun k ↦ (Encodable.decode k).getD empty

private theorem legalMatchingEnumeration_surjective (m n : ℕ) :
    Function.Surjective (legalMatchingEnumeration m n) := by
  let _ : Encodable (OTSelector.PartialMatching m n) := Encodable.ofCountable _
  exact Encodable.surjective_decode_getD _ empty

private theorem exists_legalOptimal_index (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) :
    ∃ k, IsLegalOptimal allowed c (legalMatchingEnumeration m n k) := by
  obtain ⟨σ, hσ⟩ := exists_cost_eq_legalMaximumValue allowed c
  obtain ⟨k, rfl⟩ := legalMatchingEnumeration_surjective m n σ
  exact ⟨k, hσ⟩

/-- First exact legal optimum in a fixed enumeration, including tied samples. -/
def firstLegalOptimalMatching (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) : OTSelector.PartialMatching m n := by
  classical
  exact legalMatchingEnumeration m n (Nat.find (exists_legalOptimal_index allowed c))

theorem firstLegalOptimalMatching_isLegalOptimal (allowed : Finset (Fin m × Fin n))
    (c : Fin m → Fin n → ℝ) : IsLegalOptimal allowed c (firstLegalOptimalMatching allowed c) := by
  classical
  exact Nat.find_spec (exists_legalOptimal_index allowed c)

/-- Actual graph events and edge costs make every exact-optimality event measurable. -/
theorem measurableSet_isLegalOptimal {Ω : Type*} [MeasurableSpace Ω]
    (allowed : Ω → Finset (Fin m × Fin n))
    (hallowed : ∀ S, MeasurableSet {ξ | allowed ξ = S})
    (c : Ω → Fin m → Fin n → ℝ) (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (σ : OTSelector.PartialMatching m n) :
    MeasurableSet {ξ | IsLegalOptimal (allowed ξ) (c ξ) σ} := by
  classical
  have hrepr : {ξ | IsLegalOptimal (allowed ξ) (c ξ) σ} =
      ⋃ S : Finset (Fin m × Fin n),
        {ξ | allowed ξ = S} ∩ {ξ | IsLegalOptimal S (c ξ) σ} := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h ↦ ⟨allowed ξ, rfl, h⟩, fun ⟨S, hS, h⟩ ↦ hS.symm ▸ h⟩
  rw [hrepr]
  apply MeasurableSet.iUnion
  intro S
  apply (hallowed S).inter
  exact (MeasurableSet.const (IsLegal S σ)).inter
    ((MeasurableSet.const (σ.card = legalMaximumCard S)).inter
      (measurableSet_eq_fun (Finset.measurable_sum _ fun e _ ↦ hc e.1 e.2)
        (measurable_legalMaximumValue_fixed S c hc)))

/-- The actual exact optimum is measurable for any measurable structure on
the finite matching space. No uniqueness premise is needed. -/
theorem measurable_firstLegalOptimalMatching {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (OTSelector.PartialMatching m n)]
    (allowed : Ω → Finset (Fin m × Fin n))
    (hallowed : ∀ S, MeasurableSet {ξ | allowed ξ = S})
    (c : Ω → Fin m → Fin n → ℝ) (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j)) :
    Measurable (fun ξ ↦ firstLegalOptimalMatching (allowed ξ) (c ξ)) := by
  classical
  exact (measurable_of_countable (legalMatchingEnumeration m n)).comp
    (measurable_find (fun ξ ↦ exists_legalOptimal_index (allowed ξ) (c ξ))
      (fun k ↦ measurableSet_isLegalOptimal allowed hallowed c hc _))

/-- Every edge-inclusion event of the selected actual optimum is measurable. -/
theorem measurableSet_mem_firstLegalOptimalMatching {Ω : Type*} [MeasurableSpace Ω]
    (allowed : Ω → Finset (Fin m × Fin n))
    (hallowed : ∀ S, MeasurableSet {ξ | allowed ξ = S})
    (c : Ω → Fin m → Fin n → ℝ) (hc : ∀ i j, Measurable (fun ξ ↦ c ξ i j))
    (e : Fin m × Fin n) :
    MeasurableSet {ξ | e ∈ (firstLegalOptimalMatching (allowed ξ) (c ξ)).edges} := by
  let _instLegalOptimizerMeasurable : MeasurableSpace (OTSelector.PartialMatching m n) := ⊤
  have hs : MeasurableSet {σ : OTSelector.PartialMatching m n | e ∈ σ.edges} :=
    MeasurableSet.of_discrete
  exact hs.preimage (measurable_firstLegalOptimalMatching allowed hallowed c hc)

end OTSelector.Reconstruction.PartialMatching

end
end
