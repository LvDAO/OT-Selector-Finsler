import OTSelector.Probability.CavitySemidiscretePressureComparison
import OTSelector.Probability.CavitySemidiscreteSourceGlue
import OTSelector.Probability.CavitySemidiscreteTargetBlockWitness

/-!
# Finite packing of complete target-block cycle witnesses

Whole finite target blocks may be crossed in each local certificate. Explicit
product-marginal corrections glue on disjoint source supports, while target blocks
of different corrections may overlap without changing any prescribed mass.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S I : Type*} [MeasurableSpace S] [Fintype I]

/-- Finite disjoint-source cycle certificates add without loss in the constant. -/
theorem semidiscrete_target_block_packing_le_excess
    (μ : Measure S) [SFinite μ] (p : Fin (m + 1) → ℝ)
    (a a₀ c : S → Fin (m + 1) → ℝ) (ha : IsSemidiscreteAllocation μ p a)
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (J L : I → Finset (Fin (m + 1)))
    (A B : I → Set S) (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hAB : ∀ i, Disjoint (A i) (B i))
    (hdisj : Pairwise (fun i k ↦ Disjoint (A i ∪ B i) (A k ∪ B k)))
    (ε : I → ℝ) (hgap : ∀ i, ∀ s ∈ A i, ∀ t ∈ B i, ∀ j ∈ J i, ∀ k ∈ L i,
      ε i ≤ c s j + c t k - c s k - c t j) :
    (∑ i, ε i * min (semidiscreteBlockMass μ a (A i) (J i))
      (semidiscreteBlockMass μ a (B i) (L i))) ≤
      semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c a₀ := by
  classical
  choose b hb hloc hgain using fun i ↦ exists_semidiscrete_target_block_exchange
    μ p a c ha hc (A i) (B i) (hA i) (hB i) (hAB i) (J i) (L i) (ε i) (hgap i)
  exact (Finset.sum_le_sum (fun i _ ↦ hgain i)).trans
    (semidiscrete_disjoint_improvements_le_excess
      μ p a a₀ b ha hb c hc h₀ (fun i ↦ A i ∪ B i) hdisj hloc)

/-- The actual average of opposite-tilt optimizers has total packed cycle violation at
most `t * G`, on the same source and target masses. -/
theorem semidiscrete_opposite_tilt_target_block_packing_le
    (μ : Measure S) [IsProbabilityMeasure μ] (p : Fin (m + 1) → ℝ)
    (c g a₀ aplus aminus : S → Fin (m + 1) → ℝ)
    (t G : ℝ) (ht : 0 ≤ t)
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (hplus : IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c s j + t * g s j) aplus)
    (hminus : IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c s j + (-t) * g s j) aminus)
    (hc : ∀ k, Integrable (fun s ↦ c s k) μ)
    (hg : ∀ k, Integrable (fun s ↦ g s k) μ)
    (hbound : ∀ᵐ s ∂μ, ∀ k, |g s k| ≤ G)
    (J L : I → Finset (Fin (m + 1)))
    (A B : I → Set S) (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    (hAB : ∀ i, Disjoint (A i) (B i))
    (hdisj : Pairwise (fun i k ↦ Disjoint (A i ∪ B i) (A k ∪ B k)))
    (ε : I → ℝ) (hgap : ∀ i, ∀ s ∈ A i, ∀ s' ∈ B i, ∀ j ∈ J i, ∀ k ∈ L i,
      ε i ≤ c s j + c s' k - c s k - c s' j) :
    (∑ i, ε i * min
      (semidiscreteBlockMass μ (fun s j ↦ (aplus s j + aminus s j) / 2) (A i) (J i))
      (semidiscreteBlockMass μ (fun s j ↦ (aplus s j + aminus s j) / 2) (B i) (L i))) ≤ t * G := by
  have hpack := semidiscrete_target_block_packing_le_excess μ p
    (fun s k ↦ (aplus s k + aminus s k) / 2) a₀ c (hplus.1.average hminus.1)
    h₀ hc J L A B hA hB hAB hdisj ε hgap
  have hcmp := semidiscrete_opposite_tilt_excess μ p c g a₀ aplus aminus
    h₀.1 hplus.1 hminus.1 hc hg G hbound t ht h₀.2 hplus.2 hminus.2
  exact hpack.trans (hcmp.2.1.trans hcmp.2.2.1)

end OTSelector.Probability
