import OTSelector.Probability.CavitySemidiscretePressurePhysical

/-!
# Opposite perturbations on the same diffuse source and target masses

Every pair of actual opposite-tilt optimizers has a feasible average. Its unperturbed
excess is bounded by the tilt times the probe bound, uniformly over the full optimal
faces. The individual unperturbed energies satisfy the corresponding two-tilt bound.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Averaging two allocations keeps the same source law and target masses. -/
theorem IsSemidiscreteAllocation.average {μ : Measure S} {p : Fin (m + 1) → ℝ}
    {a b : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (hb : IsSemidiscreteAllocation μ p b) :
    IsSemidiscreteAllocation μ p (fun s j ↦ (a s j + b s j) / 2) := by
  refine ⟨fun j ↦ ((ha.integrable j).add (hb.integrable j)).div_const 2, ?_, ?_, ?_⟩
  · filter_upwards [ha.nonneg, hb.nonneg] with s hsa hsb
    exact fun j ↦ div_nonneg (add_nonneg (hsa j) (hsb j)) (by norm_num)
  · filter_upwards [ha.sum_one, hb.sum_one] with s hsa hsb
    rw [← Finset.sum_div, Finset.sum_add_distrib, hsa, hsb]
    norm_num
  · intro j
    rw [integral_div, integral_add (ha.integrable j) (hb.integrable j), ha.mass, hb.mass]
    ring

/-- The paired objective is affine in the allocation. -/
theorem IsSemidiscreteAllocation.cost_average {μ : Measure S} {p : Fin (m + 1) → ℝ}
    {a b : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (hb : IsSemidiscreteAllocation μ p b)
    (c : S → Fin (m + 1) → ℝ) (hc : ∀ j, Integrable (fun s ↦ c s j) μ) :
    semidiscreteAllocationCost μ c (fun s j ↦ (a s j + b s j) / 2) =
      (semidiscreteAllocationCost μ c a + semidiscreteAllocationCost μ c b) / 2 := by
  unfold semidiscreteAllocationCost
  have heq (s : S) : (∑ j, (a s j + b s j) / 2 * c s j) =
      ((∑ j, a s j * c s j) + ∑ j, b s j * c s j) / 2 := by
    simp only [div_mul_eq_mul_div, add_mul]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
  simp_rw [heq]
  rw [integral_div, integral_add
    (integrable_finsetSum _ (fun j _ ↦ ha.integrable_mul c hc j))
    (integrable_finsetSum _ (fun j _ ↦ hb.integrable_mul c hc j))]

/-- Every feasible paired objective has the exact affine tilt dependence. -/
theorem IsSemidiscreteAllocation.cost_tilt {μ : Measure S} {p : Fin (m + 1) → ℝ}
    {a : S → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (c g : S → Fin (m + 1) → ℝ)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ) (t : ℝ) :
    semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) a =
      semidiscreteAllocationCost μ c a + t * semidiscreteAllocationCost μ g a := by
  unfold semidiscreteAllocationCost
  have heq (s : S) : (∑ j, a s j * (c s j + t * g s j)) =
      (∑ j, a s j * c s j) + t * ∑ j, a s j * g s j := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [heq]
  rw [integral_add (integrable_finsetSum _ (fun j _ ↦ ha.integrable_mul c hc j))
    ((integrable_finsetSum _ (fun j _ ↦ ha.integrable_mul g hg j)).const_mul t),
    integral_const_mul]

/-- The probe bound controls every allocation with constant one, independently of target count. -/
theorem IsSemidiscreteAllocation.abs_cost_le {μ : Measure S} [IsProbabilityMeasure μ]
    {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (g : S → Fin (m + 1) → ℝ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    (G : ℝ) (hbound : ∀ᵐ s ∂μ, ∀ j, |g s j| ≤ G) :
    |semidiscreteAllocationCost μ g a| ≤ G := by
  have h := ha.cost_abs_sub_le g (fun _ _ ↦ 0) hg (fun _ ↦ integrable_const (0 : ℝ)) G
    (hbound.mono fun s hs j ↦ by simpa only [sub_zero] using hs j)
  simpa [semidiscreteAllocationCost] using h

/-- Exact common-environment excess bounds for all choices from the three actual optimal faces. -/
theorem semidiscrete_opposite_tilt_excess
    (μ : Measure S) [IsProbabilityMeasure μ] (p : Fin (m + 1) → ℝ)
    (c g a₀ aplus aminus : S → Fin (m + 1) → ℝ)
    (h₀ : IsSemidiscreteAllocation μ p a₀)
    (hplus : IsSemidiscreteAllocation μ p aplus) (hminus : IsSemidiscreteAllocation μ p aminus)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    (G : ℝ) (hbound : ∀ᵐ s ∂μ, ∀ j, |g s j| ≤ G)
    (t : ℝ) (ht : 0 ≤ t)
    (hopt₀ : ∀ b, IsSemidiscreteAllocation μ p b →
      semidiscreteAllocationCost μ c a₀ ≤ semidiscreteAllocationCost μ c b)
    (hoptplus : ∀ b, IsSemidiscreteAllocation μ p b →
      semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) aplus ≤
        semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) b)
    (hoptminus : ∀ b, IsSemidiscreteAllocation μ p b →
      semidiscreteAllocationCost μ (fun s j ↦ c s j + (-t) * g s j) aminus ≤
        semidiscreteAllocationCost μ (fun s j ↦ c s j + (-t) * g s j) b) :
    let Δ := semidiscreteAllocationCost μ c (fun s j ↦ (aplus s j + aminus s j) / 2) -
      semidiscreteAllocationCost μ c a₀
    0 ≤ Δ ∧
    Δ ≤ t / 2 * (semidiscreteAllocationCost μ g aminus - semidiscreteAllocationCost μ g aplus) ∧
    t / 2 * (semidiscreteAllocationCost μ g aminus - semidiscreteAllocationCost μ g aplus) ≤ t * G ∧
    semidiscreteAllocationCost μ c aplus ≤ semidiscreteAllocationCost μ c a₀ + 2 * t * G ∧
    semidiscreteAllocationCost μ c aminus ≤ semidiscreteAllocationCost μ c a₀ + 2 * t * G := by
  have hav := hplus.average hminus
  have hzero := hopt₀ _ hav
  have hp := hoptplus a₀ h₀
  have hm := hoptminus a₀ h₀
  rw [hplus.cost_tilt c g hc hg t, h₀.cost_tilt c g hc hg t] at hp
  rw [hminus.cost_tilt c g hc hg (-t), h₀.cost_tilt c g hc hg (-t)] at hm
  have hb₀ := abs_le.mp (h₀.abs_cost_le g hg G hbound)
  have hbplus := abs_le.mp (hplus.abs_cost_le g hg G hbound)
  have hbminus := abs_le.mp (hminus.abs_cost_le g hg G hbound)
  dsimp only
  rw [hplus.cost_average hminus c hc] at hzero ⊢
  refine ⟨by linarith, by nlinarith, ?_, ?_, ?_⟩ <;>
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hbplus.1),
      mul_nonneg ht (sub_nonneg.mpr hbplus.2),
      mul_nonneg ht (sub_nonneg.mpr hbminus.1),
      mul_nonneg ht (sub_nonneg.mpr hbminus.2),
      mul_nonneg ht (sub_nonneg.mpr hb₀.1),
      mul_nonneg ht (sub_nonneg.mpr hb₀.2)]

end OTSelector.Probability
