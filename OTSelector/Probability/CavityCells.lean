import OTSelector.Transport.Semidiscrete.CavityCells
import OTSelector.Finite.AssignmentCavity
import OTSelector.Probability.IndependentRandomRegion
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
Conditions: Finite assignment costs with measurable retained rows/new row; no-tie, independence and product-law hypotheses occur only in the corresponding almost-everywhere variants.

Objects: Actual cavity scores/cells/masses, measurability, coverage and unique cell selection almost everywhere.

Proof detail: Use finite assignment cavity minima for scores, measurable comparisons for cells, and Fubini/independence to transfer pairwise atomless score differences to a unique minimizer.

Sources: Gabriel Peyré, Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20) (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31); Gabriel Peyré, Section 5.2, equations (5.6)–(5.8), pp. 94–96 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=98); D. H. Fremlin, Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25 (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19); Rick Durrett, Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56); Project manuscript, Section “Exact iid cavity disintegration”, Theorem thm:iid-cavity-dirichlet and Proposition prop:iid-cavity-mean, equation eq:iid-cavity-mean-plan (main.tex).
Relation: Finite row-deletion and no-tie cell calculations, also used in main.tex thm:iid-cavity-dirichlet. The distribution-free Dirichlet theorem is not inferred from these cells alone.
-/

/-!
# Measurable finite cavity cells under the original insertion law

Exact vacancy prices depend only on the retained input. Their measurable row envelopes define
cells containing every possible optimal partner, with all ties retained. Atomless pairwise
row-cost differences imply that these cells partition the insertion space almost everywhere.
For an independent insertion on the original probability space, cell masses give the allocation
probabilities after restriction to any measurable retained-input event. No new samples or
uniqueness of the full assignment are assumed. The atomless condition remains explicit; no
Dirichlet law or geometric verification of that condition is claimed here.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

namespace OTSelector.Probability

variable {n : ℕ} {W S Ω : Type*}
  [MeasurableSpace W] [MeasurableSpace S] [MeasurableSpace Ω]







omit [MeasurableSpace W] [MeasurableSpace S] in
/-- The inserted row does not enter the actual vacancy price. -/
theorem cavity_price_ignores_insertion
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i j : Fin (n + 1)) (z : W × S) :
    assignmentCavityValue (Function.update (retained z.1) i (row z)) i j =
      assignmentCavityValue (retained z.1) i j :=
  assignmentCavityValue_update_row _ _ _ _









omit [MeasurableSpace W] [MeasurableSpace S] in
/-- Cavity cells cover the full pair space, before any no-tie hypothesis. -/
theorem iUnion_cavityCell
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ⋃ j, cavityCell retained row i j = Set.univ := by
  ext z
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_mem_cavityCell retained row i z

omit [MeasurableSpace W] [MeasurableSpace S] in
/-- Cell membership is equivalent to existence of a full optimal permutation with that partner. -/
theorem mem_cavityCell_iff_exists_optimal_partner
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ) (i j : Fin (n + 1)) (z : W × S) :
    z ∈ cavityCell retained row i j ↔
      ∃ σ : Assignment (n + 1),
        OptimalAssignment (Function.update (retained z.1) i (row z)) σ ∧ σ i = j := by
  rw [exists_optimalAssignment_partner_iff]
  simp [cavityCell, cavityScore, assignmentRowEnvelope]



















/-- Exact conditional cell probabilities, tested against every measurable retained-input event.
This disintegration uses the original independent pair and holds even before ties are excluded. -/
theorem measure_cavityCell_restrict_retained
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure S) [SFinite μ]
    (W₀ : Ω → W) (X : Ω → S) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i j : Fin (n + 1))
    (B : Set W) (hB : MeasurableSet B) :
    P {ω | W₀ ω ∈ B ∧ (W₀ ω, X ω) ∈ cavityCell retained row i j} =
      ∫⁻ w in B, cavityCellMass μ retained row i j w ∂P.map W₀ := by
  let C : Set (W × S) := {z | z.1 ∈ B ∧ z ∈ cavityCell retained row i j}
  have hC : MeasurableSet C :=
    (hB.preimage measurable_fst).inter (measurableSet_cavityCell retained row hret hrow i j)
  change P ((fun ω ↦ (W₀ ω, X ω)) ⁻¹' C) = _
  rw [← Measure.map_apply (hW.prodMk hX) hC,
    hindep.map_prod_eq_prod_map_map hW.aemeasurable hX.aemeasurable, hlaw,
    Measure.prod_apply hC]
  rw [← lintegral_indicator hB]
  apply lintegral_congr
  intro w
  by_cases hw : w ∈ B <;> simp [C, hw, cavityCellMass]

/-- Every full optimal permutation has the cell-mass conditional allocation law once ties vanish.
The chosen optimum can be any function of the original data; no measurable or unique full
optimizer is assumed. The displayed probabilities are well-defined outer event probabilities. -/
theorem measure_optimal_partner_restrict_retained
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure S) [SFinite μ]
    (W₀ : Ω → W) (X : Ω → S) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i j : Fin (n + 1))
    (hno : ∀ᵐ w ∂P.map W₀, ∀ u v, u ≠ v →
      μ {s | cavityScore retained row i (w, s) u = cavityScore retained row i (w, s) v} = 0)
    (σ : Ω → Assignment (n + 1))
    (hσ : ∀ᵐ ω ∂P, OptimalAssignment
      (Function.update (retained (W₀ ω)) i (row (W₀ ω, X ω))) (σ ω))
    (B : Set W) (hB : MeasurableSet B) :
    P {ω | W₀ ω ∈ B ∧ σ ω i = j} =
      ∫⁻ w in B, cavityCellMass μ retained row i j w ∂P.map W₀ := by
  rw [← measure_cavityCell_restrict_retained P μ W₀ X hW hX hindep hlaw
    retained row hret hrow i j B hB]
  apply measure_congr
  filter_upwards [hσ, ae_existsUnique_mem_cavityCell_of_indepFun P μ W₀ X hW hX hindep hlaw
    retained row hret hrow i hno] with ω hσω huniq
  have hmem : (W₀ ω, X ω) ∈ cavityCell retained row i (σ ω i) :=
    (mem_cavityCell_iff_exists_optimal_partner retained row i (σ ω i) (W₀ ω, X ω)).mpr
      ⟨σ ω, hσω, rfl⟩
  apply propext
  change (W₀ ω ∈ B ∧ σ ω i = j) ↔
    (W₀ ω ∈ B ∧ (W₀ ω, X ω) ∈ cavityCell retained row i j)
  constructor
  · rintro ⟨hw, heq⟩
    exact ⟨hw, heq ▸ hmem⟩
  · rintro ⟨hw, hj⟩
    exact ⟨hw, huniq.unique hmem hj⟩

/-- The conditional allocation formula under the stated atomless difference-law condition. -/
theorem measure_optimal_partner_restrict_retained_atomless
    (P : Measure Ω) [IsFiniteMeasure P] (μ : Measure S) [SFinite μ]
    (W₀ : Ω → W) (X : Ω → S) (hW : Measurable W₀) (hX : Measurable X)
    (hindep : IndepFun W₀ X P) (hlaw : P.map X = μ)
    (retained : W → Fin (n + 1) → Fin (n + 1) → ℝ)
    (row : W × S → Fin (n + 1) → ℝ)
    (hret : ∀ k l, Measurable (fun w ↦ retained w k l))
    (hrow : ∀ j, Measurable (fun z ↦ row z j)) (i j : Fin (n + 1))
    (hatom : ∀ᵐ w ∂P.map W₀, ∀ u v, u ≠ v →
      NullSingletonClass (μ.map (fun s ↦ row (w, s) u - row (w, s) v)))
    (σ : Ω → Assignment (n + 1))
    (hσ : ∀ᵐ ω ∂P, OptimalAssignment
      (Function.update (retained (W₀ ω)) i (row (W₀ ω, X ω))) (σ ω))
    (B : Set W) (hB : MeasurableSet B) :
    P {ω | W₀ ω ∈ B ∧ σ ω i = j} =
      ∫⁻ w in B, cavityCellMass μ retained row i j w ∂P.map W₀ := by
  apply measure_optimal_partner_restrict_retained P μ W₀ X hW hX hindep hlaw
    retained row hret hrow i j ?_ σ hσ B hB
  filter_upwards [hatom] with w hw
  intro u v huv
  have := hw u v huv
  exact measure_cavityScore_eq_zero_of_atomless μ retained row hrow i u v w

end OTSelector.Probability
