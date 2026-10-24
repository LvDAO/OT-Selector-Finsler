import OTSelector.Probability.CavitySemidiscretePressureValue
import OTSelector.Finite.PressureRegularity

/-!
# Exact Lipschitz bounds for the primal semidiscrete pressure

The source allocation weights sum to one, so an entrywise cost error bounds the entire
normalized objective by the same amount. Taking the actual feasible infima preserves
this bound without assuming attainment or uniqueness at perturbed costs.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S : Type*} [MeasurableSpace S]

/-- Uniform original edge errors bound every feasible allocation's objective error. -/
theorem IsSemidiscreteAllocation.cost_abs_sub_le
    {μ : Measure S} [IsProbabilityMeasure μ] {p : Fin (m + 1) → ℝ}
    {a : S → Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (c d : S → Fin (m + 1) → ℝ)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ) (hd : ∀ j, Integrable (fun s ↦ d s j) μ)
    (B : ℝ) (hbound : ∀ᵐ s ∂μ, ∀ j, |c s j - d s j| ≤ B) :
    |semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ d a| ≤ B := by
  have hci := integrable_finsetSum Finset.univ (fun j _ ↦ ha.integrable_mul c hc j)
  have hdi := integrable_finsetSum Finset.univ (fun j _ ↦ ha.integrable_mul d hd j)
  have hdiff : semidiscreteAllocationCost μ c a - semidiscreteAllocationCost μ d a =
      ∫ s, ∑ j, a s j * (c s j - d s j) ∂μ := by
    unfold semidiscreteAllocationCost
    rw [← integral_sub hci hdi]
    congr 1
    funext s
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [hdiff, ← Real.norm_eq_abs]
  have hb : ∀ᵐ s ∂μ, ‖∑ j, a s j * (c s j - d s j)‖ ≤ B := by
    filter_upwards [ha.nonneg, ha.sum_one, hbound] with s hn hs hb
    calc
      _ ≤ ∑ j, ‖a s j * (c s j - d s j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, a s j * B := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn j), Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hb j) (hn j)
      _ = B := by rw [← Finset.sum_mul, hs, one_mul]
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const hb

/-- The actual semidiscrete infimum has the same uniform edge stability as each competitor. -/
theorem semidiscreteValue_abs_sub_le
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c d : S → Fin (m + 1) → ℝ)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ) (hd : ∀ j, Integrable (fun s ↦ d s j) μ)
    (p : Fin (m + 1) → ℝ) (hp : p ∈ stdSimplex ℝ (Fin (m + 1)))
    (B : ℝ) (hbound : ∀ᵐ s ∂μ, ∀ j, |c s j - d s j| ≤ B) :
    |semidiscreteValue μ c p - semidiscreteValue μ d p| ≤ B := by
  exact Analysis.Convex.abs_sub_le_of_isGLB_image
    (isGLB_semidiscreteValue μ c hc p hp) (isGLB_semidiscreteValue μ d hd p hp)
    (fun a ha ↦ ha.cost_abs_sub_le c d hc hd B hbound)

/-- The primal semidiscrete pressure has exactly the uniform probe Lipschitz constant. -/
theorem lipschitzWith_semidiscreteValue_tilt
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c g : S → Fin (m + 1) → ℝ)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ) (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    (G : ℝ≥0) (hbound : ∀ᵐ s ∂μ, ∀ j, |g s j| ≤ G)
    (p : Fin (m + 1) → ℝ) (hp : p ∈ stdSimplex ℝ (Fin (m + 1))) :
    LipschitzWith G (fun t : ℝ ↦ semidiscreteValue μ (fun s j ↦ c s j + t * g s j) p) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  simp only [Real.dist_eq]
  apply semidiscreteValue_abs_sub_le μ _ _ (fun j ↦ (hc j).add ((hg j).const_mul t))
    (fun j ↦ (hc j).add ((hg j).const_mul u)) p hp
  filter_upwards [hbound] with s hs
  intro j
  calc
    |(c s j + t * g s j) - (c s j + u * g s j)| = |t - u| * |g s j| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ |t - u| * G := mul_le_mul_of_nonneg_left (hs j) (abs_nonneg _)
    _ = (G : ℝ) * |t - u| := mul_comm _ _

end OTSelector.Probability
