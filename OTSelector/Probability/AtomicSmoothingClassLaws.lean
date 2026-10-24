import OTSelector.Transport.Coupling.OrderedStageChain

/-!
Conditions: A finite original family of finite smoothing measures and natural-number labels, bounded by N for the finite-prefix identity.

Objects: Actual grouped class laws, their finiteness/zero-unused-label property and equality of their finite labeled prefix with the sum of the original tagged smoothing measures.

Proof detail: Sum the finite family over label fibers, then interchange the finite grouped sums and use the unique original label for each summand.

References: Rick Durrett: Section 1.4, Theorem 1.4.7, p. 23; Section 1.6, positive/negative parts p. 28 and Theorem 1.6.1, p. 29; Terence Tao: Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
Relation: Finite measure/label regrouping, preserving total original tagged mass. It supplies no new probabilistic independence or replacement law.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClassLaws.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairClassLaws`; the selected original proof blocks follow. -/
section

/-! The actual class laws group the original finite smoothing measures without
changing their labels or total tagged law. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 300000
variable {E I : Type*} [MeasurableSpace E] [Fintype I]

/-- The literal sum of smoothing measures of original atoms in one class. -/
def originalAtomSmoothingClassLaw (κ : I → Measure E) (c : I → ℕ) (k : ℕ) : Measure E :=
  ∑ i, if c i = k then κ i else 0

/-- Each class law is finite whenever the original component laws are finite. -/
theorem originalAtomSmoothingClassLaw_isFiniteMeasure
    (κ : I → Measure E) [∀ i, IsFiniteMeasure (κ i)] (c : I → ℕ) (k : ℕ) :
    IsFiniteMeasure (originalAtomSmoothingClassLaw κ c k) := by
  classical
  have : ∀ i, IsFiniteMeasure (if c i = k then κ i else 0) := by
    intro i
    split_ifs <;> infer_instance
  unfold originalAtomSmoothingClassLaw
  infer_instance

/-- A class without original source labels contributes the actual zero law. -/
theorem originalAtomSmoothingClassLaw_eq_zero_of_no_label
    (κ : I → Measure E) (c : I → ℕ) (k : ℕ) (h : ∀ i, c i ≠ k) :
    originalAtomSmoothingClassLaw κ c k = 0 := by
  classical
  simp only [originalAtomSmoothingClassLaw]
  apply Finset.sum_eq_zero
  intro i _
  simp only [h i, ite_false]

/-- Grouping all original smoothing laws by their actual classes recovers the
exact sum of their original tagged laws, including empty arrays and zero classes. -/
theorem originalAtomSmoothingClassLaw_labelledPrefix
    (κ : I → Measure E) (c : I → ℕ) (N : ℕ) (hc : ∀ i, c i < N) :
    finiteStageLabelledPrefix (originalAtomSmoothingClassLaw κ c) N =
      ∑ i, (κ i).map (Prod.mk (c i)) := by
  classical
  have hmap (k : ℕ) : (originalAtomSmoothingClassLaw κ c k).map (Prod.mk k) =
      ∑ i, if c i = k then (κ i).map (Prod.mk k) else 0 := by
    unfold originalAtomSmoothingClassLaw
    rw [Measure.map_finset_sum' measurable_prodMk_left.aemeasurable]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  unfold finiteStageLabelledPrefix
  simp_rw [hmap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single (c i)]
  · simp
  · intro k _ hki
    simp [Ne.symm hki]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (hc i)))

end OTSelector.Reconstruction

end
end
