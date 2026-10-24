import OTSelector.Finite.ClockFlowNormalization
import OTSelector.Finite.OrderedHallFlow
import OTSelector.Finite.ThresholdClockHallFlow
import OTSelector.Transport.Coupling.ResidualFinitePopulation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawNormalizedReferenceSplit.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawNormalizedReferenceSplit`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerRelativeLawNormalizedReferenceSplit

**Conditions:** An ordered legal graph has a feasible reference and actual class matrices; positive intensities and the displayed finite relative tolerances are supplied.

**Objects:** Normalized retained and residual class flows with exact original conditional marginals and residual mass ≤η+ε.

**Proof detail:** Derive Hall cuts from the actual feasible matrix, choose a tolerance preserving residual feasibility, build the explicit residual clock flow, then divide both pieces by the actual intensity and bound their exact mass.

**Sources:** [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=39), Section 2.6, Remarks 2.27–2.28, pp. 35–37, equations (2.31)–(2.37); [Reinhard Diestel, Graph Theory, 4th electronic edition (2010), corrected reprint 2012](https://diestel-graph-theory.com/Sample.pdf#page=2), Chapter 2 opening matching definition and Section 2.1, first three chapter pages; [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Measurable forward weighted Hall construction](main.tex#measurable-forward-hall), main.tex label measurable-forward-hall, line 6889.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
Explicit normalized finite-reference class splitting for the unchanged original
population, with measurable retained and residual flows and a uniform relative
residual mass bound. All finite Hall constraints are derived from actual legal
class matrices.
-/

open MeasureTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- A legal reference matrix fixes a finite tolerance. Every actual original
legal matrix whose full intensity-weighted class masses meet that tolerance
produces the normalized retained/residual split needed for original population
reconstruction. Actual and reference Hall are derived from their literal flows. -/
theorem exists_tolerance_normalized_reference_classSplit
    {M L : ℕ} (allowed : Fin M → Fin L → Prop)
    (horder : ∀ i i' j j', i ≤ i' → j' ≤ j → allowed i' j' → allowed i j)
    (a₀ : Fin M → ℝ) (b₀ : Fin L → ℝ) (P₀ : Fin M → Fin L → ℝ)
    (hP₀ : ∀ i j, 0 ≤ P₀ i j)
    (hrow₀ : ∀ i, ∑ j, P₀ i j = a₀ i) (hcol₀ : ∀ j, ∑ i, P₀ i j = b₀ j)
    (hzero₀ : ∀ i j, ¬ allowed i j → P₀ i j = 0)
    (d₀ η : ℝ) (hd₀ : 0 < d₀) (htotal₀ : ∑ i, a₀ i = d₀)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (d ε : ℝ) (a : Fin M → ℝ) (b : Fin L → ℝ)
      (A : Fin M → Fin L → ℝ), 0 < d → 0 ≤ ε → d ≤ (1 + ε) * d₀ →
      (∀ i j, 0 ≤ A i j) →
      (∀ i, ∑ j, A i j = a i) → (∀ j, ∑ i, A i j = b j) →
      (∀ i j, ¬ allowed i j → A i j = 0) → (∑ i, a i = 1) →
      (∀ i, |d * a i - a₀ i| ≤ δ) → (∀ j, |d * b j - b₀ j| ≤ δ) →
      let Q := referenceResidualClockFlow a₀ b₀ η (fun i ↦ d * a i) (fun j ↦ d * b j)
      (∀ i j, 0 ≤ (1 - η) * P₀ i j / d) ∧
      (∀ i j, 0 ≤ Q i j / d) ∧
      (∀ i, ∑ j, ((1 - η) * P₀ i j / d + Q i j / d) = a i) ∧
      (∀ j, ∑ i, ((1 - η) * P₀ i j / d + Q i j / d) = b j) ∧
      (∀ i j, ¬ allowed i j → (1 - η) * P₀ i j / d = 0 ∧ Q i j / d = 0) ∧
      (∑ i, ∑ j, Q i j / d) ≤ η + ε := by
  have ha₀ i : 0 ≤ a₀ i := by rw [← hrow₀ i]; exact Finset.sum_nonneg (fun j hj ↦ hP₀ i j)
  have hb₀ j : 0 ≤ b₀ j := by rw [← hcol₀ j]; exact Finset.sum_nonneg (fun i hi ↦ hP₀ i j)
  have hbalance₀ : ∑ i, a₀ i = ∑ j, b₀ j := by
    simp_rw [← hrow₀, ← hcol₀]
    exact Finset.sum_comm
  obtain ⟨δ, hδ, hstable⟩ := exists_tolerance_reference_residual_clockFlow allowed horder a₀ b₀
    ha₀ hb₀ hbalance₀ (finiteClockFlow_hall allowed P₀ a₀ b₀ hP₀ hrow₀ hcol₀ hzero₀) hη
  refine ⟨δ, hδ, ?_⟩
  intro d ε a b A hd hε hupper hA hrowA hcolA hzeroA htotal hclosea hcloseb
  have ha i : 0 ≤ a i := by rw [← hrowA i]; exact Finset.sum_nonneg (fun j hj ↦ hA i j)
  have hb j : 0 ≤ b j := by rw [← hcolA j]; exact Finset.sum_nonneg (fun i hi ↦ hA i j)
  have hbalance : ∑ i, d * a i = ∑ j, d * b j := by
    simp only [← Finset.mul_sum]
    congr 1
    simp_rw [← hrowA, ← hcolA]
    exact Finset.sum_comm
  have hactualHall (C : Finset (Fin M)) : (∑ i ∈ C, d * a i) ≤
      ∑ j ∈ orderedClockNeighbors allowed C, d * b j := by
    simpa only [← Finset.mul_sum] using mul_le_mul_of_nonneg_left
      (finiteClockFlow_hall allowed A a b hA hrowA hcolA hzeroA C) hd.le
  obtain ⟨hQ, hrowQ, hcolQ, hzeroQ⟩ := hstable (fun i ↦ d * a i) (fun j ↦ d * b j)
    (fun i ↦ mul_nonneg hd.le (ha i)) (fun j ↦ mul_nonneg hd.le (hb j))
    hbalance hactualHall hclosea hcloseb
  let Q := referenceResidualClockFlow a₀ b₀ η (fun i ↦ d * a i) (fun j ↦ d * b j)
  have hθ : 0 ≤ 1 - η := sub_nonneg.mpr hη1
  have hwhole := referenceWholeClockFlow_marginals allowed a₀ b₀ (fun i ↦ d * a i)
    (fun j ↦ d * b j) P₀ Q (1 - η) hθ hP₀ hQ hrow₀ hcol₀ hrowQ hcolQ hzero₀ hzeroQ
  have hnormalized := normalizedClockClassFlow_marginals d hd
    (fun i j ↦ (1 - η) * P₀ i j + Q i j) a b allowed
    hwhole.1 hwhole.2.1 hwhole.2.2.1 hwhole.2.2.2
  dsimp only
  refine ⟨fun i j ↦ div_nonneg (mul_nonneg hθ (hP₀ i j)) hd.le,
    fun i j ↦ div_nonneg (hQ i j) hd.le, ?_, ?_, ?_, ?_⟩
  · intro i
    simpa only [add_div] using hnormalized.2.1 i
  · intro j
    simpa only [add_div] using hnormalized.2.2.1 j
  · intro i j hij
    exact ⟨by rw [hzero₀ i j hij, mul_zero, zero_div], by rw [hzeroQ i j hij, zero_div]⟩
  · apply normalized_referenceResidual_mass_le d d₀ η ε hd hd₀ hη.le hη1 hε hupper Q
    apply referenceResidual_flow_total Q (fun i ↦ d * a i) a₀ d d₀ η hrowQ
    · rw [← Finset.mul_sum, htotal, mul_one]
    · exact htotal₀

end OTSelector.Reconstruction

end
end
