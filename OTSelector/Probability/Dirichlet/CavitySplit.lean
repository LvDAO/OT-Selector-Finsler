import Mathlib.Data.Nat.Choose.Multinomial
import OTSelector.Finite.AssignmentCavity
import OTSelector.Finite.CapacityAssignment
import OTSelector.Finite.TargetTreeCanonicalSuccess
import OTSelector.Finite.TargetTreePrices
import OTSelector.Probability.Dirichlet.CavitySuccess
import OTSelector.Transport.Semidiscrete.CavityCells

/-!
Conditions: A finite coordinate set and a fixed retained subset with its specified size; the measure-preserving split assumes a sigma-finite common coordinate law.

Objects: A measurable equivalence between retained/complementary sample coordinates, preservation of the actual finite product law and exact translation of successful subsets into strict complement-count events.

Proof detail: Reindex the finite product by the retained/complement partition and transport the product measure. Expand the retained cost readout and the strict-allocation definition under this same coordinate equivalence.

References: Rick Durrett: Section 1.7, Theorem 1.7.2, p. 38; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: The product split is a standard reindexing construction; the successful-subset equivalence is the project’s deterministic cavity interface and keeps the strict inequalities explicit.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityDirichletSplit.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityDirichletSplit`; the selected original proof blocks follow. -/
section

/-!
# Exact original iid laws for retained subsets

A fixed actual source subset is enumerated as the retained cavity input. Its complement
keeps its original labels. Splitting the original finite iid array gives exactly the
product of these laws; the candidate's cavity matrix is the ordinary retained-input matrix.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {n m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Expose an actual retained subset and its complement in the same original iid array. -/
def cavitySubsetSplit (I : {I : Finset (Fin n) // I.card = m}) :
    (Fin n → S) ≃ᵐ (Fin m → S) × ({k : Fin n // k ∉ I.1} → S) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n ↦ S) (fun k ↦ k ∈ I.1)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.piCongrLeft (fun _ : Fin m ↦ S) (retainedSubsetRowEquiv I).symm)
      (MeasurableEquiv.refl _))

@[simp]
theorem cavitySubsetSplit_fst (I : {I : Finset (Fin n) // I.card = m})
    (x : Fin n → S) (k : Fin m) :
    (cavitySubsetSplit I x).1 k = x (retainedSubsetRowEquiv I k) := by
  change MeasurableEquiv.piCongrLeft (fun _ : Fin m ↦ S) (retainedSubsetRowEquiv I).symm
    (fun l : {l : Fin n // l ∈ I.1} ↦ x l) k = _
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin m ↦ S)
    (retainedSubsetRowEquiv I).symm
    (fun l : {l : Fin n // l ∈ I.1} ↦ x l) (retainedSubsetRowEquiv I k)
  simpa only [Equiv.symm_apply_apply] using h



/-- The subset/complement split preserves the exact original product law. -/
theorem measurePreserving_cavitySubsetSplit (μ : Measure S) [SigmaFinite μ]
    (I : {I : Finset (Fin n) // I.card = m}) :
    MeasurePreserving (cavitySubsetSplit I) (Measure.pi (fun _ : Fin n ↦ μ))
      ((Measure.pi (fun _ : Fin m ↦ μ)).prod
        (Measure.pi (fun _ : {k : Fin n // k ∉ I.1} ↦ μ))) := by
  let : Fintype {k : Fin n // k ∈ I.1} := Subtype.fintype (fun k ↦ k ∈ I.1)
  have h₀ := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n ↦ μ) (fun k ↦ k ∈ I.1)
  have h₁ := (measurePreserving_piCongrLeft (fun _ : Fin m ↦ μ)
    (retainedSubsetRowEquiv I).symm).prod
      (MeasurePreserving.id (Measure.pi (fun _ : {k : Fin n // k ∉ I.1} ↦ μ)))
  exact h₁.comp h₀

omit [MeasurableSpace S] in
/-- The candidate's own matrix is precisely the ordinary matrix of its retained input. -/
theorem retainedSubsetCavityCost_iid_eq (c : Fin (m + 1) → S → ℝ)
    (I : {I : Finset (Fin n) // I.card = m}) (x : Fin n → S) :
    retainedSubsetCavityCost (iidCapacityInputCost c (fun k x ↦ x k) x) 0 I =
      iidCapacityInputCost c (fun k w ↦ w k) (fun k ↦ x (retainedSubsetRowEquiv I k)) := by
  funext k j
  refine Fin.succAboveCases 0 ?_ (fun l ↦ ?_) k
  · simp only [retainedSubsetCavityCost, iidCapacityInputCost, Fin.insertNth_apply_same]
  · simp only [retainedSubsetCavityCost_retained, iidCapacityInputCost_retained]

/-- Strict cell-count event on retained input and its original complementary array. -/
def cavityStrictAllocationCounts {W κ : Type*} [Fintype κ]
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ) (i : Fin (m + 1)) (r : Fin (m + 1) → ℕ) :
    Set (W × (κ → S)) :=
  {z | ∃ a : κ → Fin (m + 1), CapacityFeasible r a ∧
    ∀ k j, j ≠ a k → cavityScore retained row i (z.1, z.2 k) (a k) <
      cavityScore retained row i (z.1, z.2 k) j}

/-- Success is exactly the strict count event after exposing the same retained coordinates. -/
theorem capacitySuccessfulSubset_iff_split_strict_counts
    (c : Fin (m + 1) → S → ℝ) (r : Fin (m + 1) → ℕ)
    (I : {I : Finset (Fin n) // I.card = m}) (x : Fin n → S) :
    CapacitySuccessfulSubset r (by simp) (iidCapacityInputCost c (fun k x ↦ x k) x) 0 I ↔
      cavitySubsetSplit I x ∈ cavityStrictAllocationCounts
        (iidCapacityInputCost c (fun k w ↦ w k)) (fun z j ↦ c j z.2) 0 (fun j ↦ r j - 1) := by
  have hsplit : cavitySubsetSplit I x =
      ((fun k ↦ x (retainedSubsetRowEquiv I k)), fun k : {k : Fin n // k ∉ I.1} ↦ x k) := by
    apply Prod.ext
    · exact funext (cavitySubsetSplit_fst I x)
    · rfl
  rw [hsplit]
  simp only [CapacitySuccessfulSubset, cavityStrictAllocationCounts, mem_ofPred_eq,
    iidCapacityInputCost_retained, capacityVacancyPrice_unit_eq_assignmentCavityValue,
    retainedSubsetCavityCost_iid_eq, cavityScore]

end OTSelector.Probability

end
end
