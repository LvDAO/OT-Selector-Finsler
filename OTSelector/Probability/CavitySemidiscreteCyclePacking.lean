import OTSelector.Probability.CavitySemidiscretePressureComparison
import OTSelector.Probability.CavitySemidiscreteSourceGlue

/-!
# Finite packing of actual strict cycle witnesses

Each witness uses the smaller original block mass. The explicit corrections glue
because their source supports are disjoint, even when their target labels overlap.
Their total certified improvement is bounded by the actual optimality excess.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S I : Type*} [MeasurableSpace S] [Fintype I]

/-- Finite disjoint-source cycle certificates add without loss in the constant. -/
theorem semidiscrete_cycle_packing_le_excess
    (μ : Measure S) [SFinite μ] (p : Fin (m + 1) → ℝ)
    (a a₀ c : S → Fin (m + 1) → ℝ) (ha : IsSemidiscreteAllocation μ p a)
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (j l : I → Fin (m + 1)) (hjl : ∀ i, j i ≠ l i)
    (A B : I → Set S) (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i k ↦ Disjoint (A i ∪ B i) (A k ∪ B k)))
    (ε : I → ℝ) (hgap : ∀ i, ∀ s ∈ A i, ∀ t ∈ B i,
      ε i ≤ c s (j i) + c t (l i) - c s (l i) - c t (j i)) :
    (∑ i, ε i * min (∫ s in A i, a s (j i) ∂μ) (∫ s in B i, a s (l i) ∂μ)) ≤
      semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c a₀ := by
  classical
  choose b hb hloc hgain using fun i ↦ exists_semidiscrete_cycle_block_exchange
    μ p a c ha hc (j i) (l i) (hjl i) (A i) (B i) (hA i) (hB i) (ε i) (hgap i)
  exact (Finset.sum_le_sum (fun i _ ↦ hgain i)).trans
    (semidiscrete_disjoint_improvements_le_excess
      μ p a a₀ b ha hb c hc h₀ (fun i ↦ A i ∪ B i) hdisj hloc)

/-- The actual average of opposite-tilt optimizers has total packed cycle violation at
most `t * G`, on the same source and target masses. -/
theorem semidiscrete_opposite_tilt_cycle_packing_le
    (μ : Measure S) [IsProbabilityMeasure μ] (p : Fin (m + 1) → ℝ)
    (c g a₀ aplus aminus : S → Fin (m + 1) → ℝ)
    (t G : ℝ) (ht : 0 ≤ t)
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (hplus : IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c s j + t * g s j) aplus)
    (hminus : IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c s j + (-t) * g s j) aminus)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (hg : ∀ k, Integrable (fun s ↦ g s k) μ)
    (hbound : ∀ᵐ s ∂μ, ∀ k, |g s k| ≤ G)
    (j l : I → Fin (m + 1)) (hjl : ∀ i, j i ≠ l i)
    (A B : I → Set S) (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (fun i k ↦ Disjoint (A i ∪ B i) (A k ∪ B k)))
    (ε : I → ℝ) (hgap : ∀ i, ∀ s ∈ A i, ∀ s' ∈ B i,
      ε i ≤ c s (j i) + c s' (l i) - c s (l i) - c s' (j i)) :
    (∑ i, ε i * min
      (∫ s in A i, (aplus s (j i) + aminus s (j i)) / 2 ∂μ)
      (∫ s in B i, (aplus s (l i) + aminus s (l i)) / 2 ∂μ)) ≤ t * G := by
  have hpack := semidiscrete_cycle_packing_le_excess μ p
    (fun s k ↦ (aplus s k + aminus s k) / 2) a₀ c (hplus.1.average hminus.1)
    h₀ hc j l hjl A B hA hB hdisj ε hgap
  have hcmp := semidiscrete_opposite_tilt_excess μ p c g a₀ aplus aminus
    h₀.1 hplus.1 hminus.1 hc hg G hbound t ht h₀.2 hplus.2 hminus.2
  exact hpack.trans (hcmp.2.1.trans hcmp.2.2.1)

end OTSelector.Probability
