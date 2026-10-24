import OTSelector.Finite.CapacityAssignment
import OTSelector.Probability.Dirichlet.CavityMoments
import OTSelector.Probability.Dirichlet.CavitySplit
import OTSelector.Transport.Semidiscrete.CavityCells

/-!
Conditions: Measurable retained and new-row costs over an s-finite retained-data measure and a probability source law; equivalence with weak allocation counts assumes unique labels pointwise or the stated a.e. no-ties condition.

Objects: Measurability of strict allocation counts, their pointwise/a.e. equivalence with ordinary counts and the resulting exact multinomial cell-mass integral.

Proof detail: Express strict winner conditions by finitely many measurable inequalities. Remove the finite union of tie events and transfer the previously proved count-event probability across a.e. equality.

References: Rick Durrett: Section 1.7, Theorem 1.7.2, p. 38; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: The strict-to-ordinary replacement requires the explicit no-ties hypothesis. It is a locally derived event identity rather than a generic automatic property of arbitrary cells.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityDirichletStrictCounts.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityDirichletStrictCounts`; the selected original proof blocks follow. -/
section

/-!
# Strict cavity counts and the actual conditional mixed moments

Strict and closed cavity-count events differ only on actual cell ties. The atomless
row-difference hypothesis removes those ties under the original product law, allowing
the canonical successful-subset identity to use the existing multinomial moment formula.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {κ W S : Type*} [Fintype κ] [MeasurableSpace W] [MeasurableSpace S]

/-- The strict finite-count event is jointly measurable. -/
theorem measurableSet_cavityStrictAllocationCounts
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ)
    (hret : ∀ k j, Measurable (fun w ↦ retained w k j))
    (hrow : ∀ j, Measurable (fun z ↦ row z j))
    (i : Fin (m + 1)) (r : Fin (m + 1) → ℕ) :
    MeasurableSet (cavityStrictAllocationCounts (κ := κ) retained row i r) := by
  classical
  simp only [cavityStrictAllocationCounts, ofPred_exists]
  apply MeasurableSet.iUnion
  intro a
  by_cases ha : CapacityFeasible r a
  · simp only [ha, true_and, ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    have hmap : Measurable (fun z : W × (κ → S) ↦ (z.1, z.2 k)) :=
      measurable_fst.prodMk ((measurable_pi_apply k).comp measurable_snd)
    exact measurableSet_lt ((measurable_cavityScore retained row hret hrow i (a k)).comp hmap)
      ((measurable_cavityScore retained row hret hrow i j).comp hmap)
  · simp only [ha, false_and, ofPred_false]
    exact MeasurableSet.empty

omit [MeasurableSpace W] [MeasurableSpace S] in
/-- Unique actual cell membership identifies strict and closed count events pointwise. -/
theorem cavityStrictAllocationCounts_iff_of_unique
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ) (i : Fin (m + 1)) (r : Fin (m + 1) → ℕ)
    (z : W × (κ → S)) (hu : ∀ k, ∃! j, (z.1, z.2 k) ∈ cavityCell retained row i j) :
    z ∈ cavityStrictAllocationCounts retained row i r ↔
      z ∈ cavityAllocationCounts retained row i r := by
  simp only [cavityStrictAllocationCounts, cavityAllocationCounts, mem_iUnion,
    cavityAllocationEvent, mem_ofPred_eq]
  constructor
  · rintro ⟨a, ha, ht⟩
    refine ⟨⟨a, ha⟩, fun k j ↦ ?_⟩
    by_cases hj : j = a k
    · simp only [hj, le_refl]
    · exact (ht k j hj).le
  · rintro ⟨a, ha⟩
    refine ⟨a.1, a.2, fun k j hj ↦ lt_of_le_of_ne (ha k j) ?_⟩
    intro heq
    have hjcell : (z.1, z.2 k) ∈ cavityCell retained row i j := by
      intro l
      rw [← heq]
      exact ha k l
    exact hj ((hu k).unique hjcell (ha k))

/-- Under the actual no-tie hypothesis, strict and closed finite-count events agree
almost everywhere for the original retained/complement product law. -/
theorem ae_cavityStrictAllocationCounts_eq
    (ν : Measure W) [SFinite ν] (μ : Measure S) [IsProbabilityMeasure μ]
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ)
    (hret : ∀ k j, Measurable (fun w ↦ retained w k j))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (m + 1))
    (hno : ∀ᵐ w ∂ν, ∀ j l, j ≠ l →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) l} = 0)
    (r : Fin (m + 1) → ℕ) :
    cavityStrictAllocationCounts (κ := κ) retained row i r =ᵐ[ν.prod (Measure.pi (fun _ : κ ↦ μ))]
      cavityAllocationCounts retained row i r := by
  classical
  have hs := measurableSet_cavityStrictAllocationCounts (κ := κ) retained row hret hrow i r
  have hc : MeasurableSet (cavityAllocationCounts (κ := κ) retained row i r) :=
    MeasurableSet.iUnion fun a ↦ measurableSet_cavityAllocationEvent retained row hret hrow i a.1
  have hm : MeasurableSet {z : W × (κ → S) |
      z ∈ cavityStrictAllocationCounts retained row i r ↔
        z ∈ cavityAllocationCounts retained row i r} := by
    have heq : {z : W × (κ → S) |
        z ∈ cavityStrictAllocationCounts retained row i r ↔
          z ∈ cavityAllocationCounts retained row i r} =
        (cavityStrictAllocationCounts retained row i r ∩ cavityAllocationCounts retained row i r) ∪
        ((cavityStrictAllocationCounts retained row i r)ᶜ ∩
          (cavityAllocationCounts retained row i r)ᶜ) := by
      ext z
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_compl_iff]
      tauto
    rw [heq]
    exact (hs.inter hc).union (hs.compl.inter hc.compl)
  suffices h : ∀ᵐ z ∂ν.prod (Measure.pi (fun _ : κ ↦ μ)),
      z ∈ cavityStrictAllocationCounts retained row i r ↔
        z ∈ cavityAllocationCounts retained row i r by
    exact h.mono fun _ hz ↦ propext hz
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [hno] with w hw
  have hcells : ∀ᵐ x ∂Measure.pi (fun _ : κ ↦ μ),
      ∀ k, ∃! j, (w, x k) ∈ cavityCell retained row i j := by
    apply ae_all_iff.mpr
    intro k
    exact (measurePreserving_eval (fun _ : κ ↦ μ) k).quasiMeasurePreserving.tendsto_ae
      (ae_existsUnique_mem_cavityCell μ retained row i w hw)
  filter_upwards [hcells] with x hx
  exact cavityStrictAllocationCounts_iff_of_unique retained row i r (w, x) hx

/-- The exact strict-count probability is the actual cavity mixed moment with its word
multiplicity, since strictness removes only original-law null ties. -/
theorem measure_cavityStrictAllocationCounts
    (ν : Measure W) [SFinite ν] (μ : Measure S) [IsProbabilityMeasure μ]
    (retained : W → Fin (m + 1) → Fin (m + 1) → ℝ)
    (row : W × S → Fin (m + 1) → ℝ)
    (hret : ∀ k j, Measurable (fun w ↦ retained w k j))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i : Fin (m + 1))
    (hno : ∀ᵐ w ∂ν, ∀ j l, j ≠ l →
      μ {s | cavityScore retained row i (w, s) j = cavityScore retained row i (w, s) l} = 0)
    (r : Fin (m + 1) → ℕ) :
    (ν.prod (Measure.pi (fun _ : κ ↦ μ))) (cavityStrictAllocationCounts retained row i r) =
      (Nat.card {a : κ → Fin (m + 1) // CapacityFeasible r a} : ℝ≥0∞) *
        ∫⁻ w, ∏ j, cavityCellMass μ retained row i j w ^ r j ∂ν := by
  rw [measure_congr (ae_cavityStrictAllocationCounts_eq ν μ retained row hret hrow i hno r)]
  exact measure_cavityAllocationCounts ν μ retained row hret hrow i hno r

end OTSelector.Probability

end
end
