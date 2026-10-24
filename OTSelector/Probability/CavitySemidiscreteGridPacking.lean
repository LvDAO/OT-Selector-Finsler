import OTSelector.Probability.CavitySemidiscreteGridPhase
import OTSelector.Probability.CavitySemidiscreteBlockReadout

/-!
# Actual phase-averaged cycle packing

Cycle certificates are packed using the spatial coordinate of each source.
The lattice cubes and all correction allocations are constructed explicitly.
Jointly measurable moving blocks give the spatial integral bound directly.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {ι S : Type*} [Fintype ι] [MeasurableSpace S]

/-- Actual disjoint-source exchanges, followed by exact grid-phase averaging, bound
all translated cycle violations by the original plan's excess cost. -/
theorem lintegral_semidiscrete_grid_cycle_mass_le
    (μ : Measure S) [SFinite μ] (p : Fin (m + 1) → ℝ)
    (a a₀ c : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a)
    (ham : ∀ j, Measurable (fun s ↦ a s j))
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (loc : S → (ι → ℝ)) (K : ℝ) (hK : 0 < K)
    (A B : (ι → ℝ) → Set S)
    (hA : MeasurableSet {x : (ι → ℝ) × S | x.2 ∈ A x.1})
    (hB : MeasurableSet {x : (ι → ℝ) × S | x.2 ∈ B x.1})
    (hAB : ∀ z, Disjoint (A z) (B z))
    (hcell : ∀ z, A z ∪ B z ⊆ loc ⁻¹' cavityGridCube ι K z)
    (J L : (ι → ℝ) → Finset (Fin (m + 1)))
    (hJ : ∀ j, MeasurableSet {z | j ∈ J z})
    (hL : ∀ j, MeasurableSet {z | j ∈ L z})
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ z, ∀ s ∈ A z, ∀ t ∈ B z, ∀ j ∈ J z, ∀ k ∈ L z,
      ε ≤ c s j + c t k - c s k - c t j) :
    (∫⁻ z, ENNReal.ofReal (ε * min (semidiscreteBlockMass μ a (A z) (J z))
      (semidiscreteBlockMass μ a (B z) (L z)))) ≤
      ENNReal.ofReal (semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c a₀) *
        ENNReal.ofReal K ^ Fintype.card ι := by
  classical
  have hAz (z) : MeasurableSet (A z) :=
    hA.preimage (measurable_const.prodMk measurable_id)
  have hBz (z) : MeasurableSet (B z) :=
    hB.preimage (measurable_const.prodMk measurable_id)
  have hma := measurable_parameterized_semidiscreteBlockMass μ
    (fun x : (ι → ℝ) × S ↦ a x.2) (fun j ↦ (ham j).comp measurable_snd) A hA J hJ
  have hmb := measurable_parameterized_semidiscreteBlockMass μ
    (fun x : (ι → ℝ) × S ↦ a x.2) (fun j ↦ (ham j).comp measurable_snd) B hB L hL
  apply lintegral_le_of_cavityGrid_finite_packing ι K hK _
    ((measurable_const.mul (hma.min hmb)).ennreal_ofReal)
  intro z _ s
  have hdisj : Pairwise (fun i k : s ↦
      Disjoint (A (i.val +ᵥ z) ∪ B (i.val +ᵥ z))
        (A (k.val +ᵥ z) ∪ B (k.val +ᵥ z))) := by
    intro i k hik
    exact ((pairwise_disjoint_cavityGridCube ι K hK z
      (fun heq ↦ hik (Subtype.ext heq))).preimage loc).mono (hcell _) (hcell _)
  have hp := semidiscrete_target_block_packing_le_excess μ p a a₀ c ha h₀ hc
    (fun i : s ↦ J (i.val +ᵥ z)) (fun i : s ↦ L (i.val +ᵥ z))
    (fun i : s ↦ A (i.val +ᵥ z)) (fun i : s ↦ B (i.val +ᵥ z))
    (fun i ↦ hAz _) (fun i ↦ hBz _) (fun i ↦ hAB _) hdisj
    (fun _ ↦ ε) (fun i ↦ hgap (i.val +ᵥ z))
  rw [Finset.sum_coe_sort s (fun g ↦ ε * min
    (semidiscreteBlockMass μ a (A (g +ᵥ z)) (J (g +ᵥ z)))
    (semidiscreteBlockMass μ a (B (g +ᵥ z)) (L (g +ᵥ z))))] at hp
  change (∑ g ∈ s, ENNReal.ofReal (ε * min
    (semidiscreteBlockMass μ a (A (g +ᵥ z)) (J (g +ᵥ z)))
    (semidiscreteBlockMass μ a (B (g +ᵥ z)) (L (g +ᵥ z))))) ≤ _
  have heq := ENNReal.ofReal_sum_of_nonneg (s := s) (f := fun g ↦ ε * min
    (semidiscreteBlockMass μ a (A (g +ᵥ z)) (J (g +ᵥ z)))
    (semidiscreteBlockMass μ a (B (g +ᵥ z)) (L (g +ᵥ z))))
    (fun g _ ↦ mul_nonneg hε (le_min (ha.blockMass_nonneg _ _) (ha.blockMass_nonneg _ _)))
  rw [← heq]
  exact ENNReal.ofReal_le_ofReal hp


/-- The bounded witness used for vague limits satisfies the same actual excess bound. -/
theorem lintegral_semidiscrete_grid_cycle_witness_le
    (μ : Measure S) [SFinite μ] (p : Fin (m + 1) → ℝ)
    (a a₀ c : S → Fin (m + 1) → ℝ)
    (ha : IsSemidiscreteAllocation μ p a)
    (ham : ∀ j, Measurable (fun s ↦ a s j))
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (loc : S → (ι → ℝ)) (K : ℝ) (hK : 0 < K)
    (A B : (ι → ℝ) → Set S)
    (hA : MeasurableSet {x : (ι → ℝ) × S | x.2 ∈ A x.1})
    (hB : MeasurableSet {x : (ι → ℝ) × S | x.2 ∈ B x.1})
    (hAB : ∀ z, Disjoint (A z) (B z))
    (hcell : ∀ z, A z ∪ B z ⊆ loc ⁻¹' cavityGridCube ι K z)
    (J L : (ι → ℝ) → Finset (Fin (m + 1)))
    (hJ : ∀ j, MeasurableSet {z | j ∈ J z})
    (hL : ∀ j, MeasurableSet {z | j ∈ L z})
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ z, ∀ s ∈ A z, ∀ t ∈ B z, ∀ j ∈ J z, ∀ k ∈ L z,
      ε ≤ c s j + c t k - c s k - c t j) :
    (∫⁻ z, ENNReal.ofReal (ε * semidiscreteCycleBlockWitness μ a
      (A z) (B z) (J z) (L z))) ≤
      ENNReal.ofReal (semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ c a₀) *
        ENNReal.ofReal K ^ Fintype.card ι := by
  refine (lintegral_mono (fun z ↦ ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hε))).trans ?_
  exact lintegral_semidiscrete_grid_cycle_mass_le μ p a a₀ c ha ham h₀ hc
    loc K hK A B hA hB hAB hcell J L hJ hL ε hε hgap

end OTSelector.Probability
