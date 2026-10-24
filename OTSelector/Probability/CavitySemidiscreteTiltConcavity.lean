import OTSelector.Probability.CavitySemidiscretePressureValue
import Mathlib.Analysis.Convex.Function

/-!
# Concavity and secant bounds for the tilted semidiscrete value

For fixed Dirichlet masses, the semidiscrete value is an infimum of affine
functions of the tilt, hence concave.  Optimal allocations bracket the secant
slope: the tilted optimum gives a lower bound and the zero-tilt optimum gives an
upper bound.  These are the finite-dimensional ingredients of the one-sided
pressure derivative comparison; no limiting pressure is asserted.
-/

open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {S : Type*} [MeasurableSpace S] {m : ℕ}

/-- The semidiscrete objective of a fixed allocation is affine in the tilt. -/
theorem semidiscreteAllocationCost_tilt_affine
    (μ : Measure S) (c g : S → Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    {p : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ) (t : ℝ) :
    semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) a =
      semidiscreteAllocationCost μ c a + t * semidiscreteAllocationCost μ g a := by
  have h1 : Integrable (fun s ↦ ∑ j, a s j * c s j) μ :=
    integrable_finsetSum Finset.univ (fun j _ ↦ ha.integrable_mul c hc j)
  have h2 : Integrable (fun s ↦ ∑ j, a s j * (t * g s j)) μ :=
    integrable_finsetSum Finset.univ
      (fun j _ ↦ ha.integrable_mul (fun s j ↦ t * g s j)
        (fun j ↦ (hg j).const_mul t) j)
  have h2' : Integrable (fun s ↦ t * ∑ j, a s j * g s j) μ :=
    h2.congr (Eventually.of_forall fun s ↦ by
      change ∑ j, a s j * (t * g s j) = t * ∑ j, a s j * g s j
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring)
  unfold semidiscreteAllocationCost
  calc
    ∫ s, ∑ j, a s j * (c s j + t * g s j) ∂μ
        = ∫ s, ((∑ j, a s j * c s j) + t * ∑ j, a s j * g s j) ∂μ := by
          congr 1
          funext s
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ ↦ by ring
    _ = ∫ s, ∑ j, a s j * c s j ∂μ +
          t * ∫ s, ∑ j, a s j * g s j ∂μ := by
          rw [integral_add h1 h2', integral_const_mul]

/-- The semidiscrete value is concave in the tilt at fixed masses. -/
theorem concaveOn_semidiscreteValue_tilt
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c g : S → Fin (m + 1) → ℝ)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    {p : Fin (m + 1) → ℝ} (hp : p ∈ stdSimplex ℝ (Fin (m + 1))) :
    ConcaveOn ℝ univ
      (fun t ↦ semidiscreteValue μ (fun s j ↦ c s j + t * g s j) p) := by
  apply Analysis.Convex.concaveOn_of_isGLB_image convex_univ
    (fun t _ ↦ isGLB_semidiscreteValue μ _
      (fun j ↦ (hc j).add ((hg j).const_mul t)) p hp)
  intro alloc halloc
  refine ⟨convex_univ, ?_⟩
  intro t _ u _ a b ha hb hab
  change a * semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) alloc +
      b * semidiscreteAllocationCost μ (fun s j ↦ c s j + u * g s j) alloc ≤
    semidiscreteAllocationCost μ (fun s j ↦ c s j + (a * t + b * u) * g s j) alloc
  rw [semidiscreteAllocationCost_tilt_affine μ c g alloc halloc hc hg,
    semidiscreteAllocationCost_tilt_affine μ c g alloc halloc hc hg,
    semidiscreteAllocationCost_tilt_affine μ c g alloc halloc hc hg]
  have h : (a + b) * semidiscreteAllocationCost μ c alloc =
      semidiscreteAllocationCost μ c alloc := by rw [hab, one_mul]
  nlinarith

/-- The zero-tilt optimum gives the upper secant bound for the tilted value. -/
theorem semidiscreteValue_sub_div_le_cost_of_zero_optimal
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c g : S → Fin (m + 1) → ℝ) (a₀ : S → Fin (m + 1) → ℝ)
    {p : Fin (m + 1) → ℝ} (ha₀ : IsSemidiscreteAllocation μ p a₀)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    (hopt : ∀ b, IsSemidiscreteAllocation μ p b →
      semidiscreteAllocationCost μ c a₀ ≤ semidiscreteAllocationCost μ c b)
    {t : ℝ} (ht : 0 < t) :
    (semidiscreteValue μ (fun s j ↦ c s j + t * g s j) p -
        semidiscreteValue μ c p) / t ≤
      semidiscreteAllocationCost μ g a₀ := by
  have hval0 : semidiscreteValue μ c p = semidiscreteAllocationCost μ c a₀ :=
    semidiscreteValue_eq_cost_of_optimal μ c hc p a₀ ha₀ hopt
  have hct : ∀ j, Integrable (fun s ↦ c s j + t * g s j) μ :=
    fun j ↦ (hc j).add ((hg j).const_mul t)
  have hle := semidiscreteValue_le_cost μ _ hct p a₀ ha₀
  rw [semidiscreteAllocationCost_tilt_affine μ c g a₀ ha₀ hc hg t, ← hval0] at hle
  have hgoal : semidiscreteValue μ (fun s j ↦ c s j + t * g s j) p -
      semidiscreteValue μ c p ≤ semidiscreteAllocationCost μ g a₀ * t := by
    rw [hval0]
    linarith
  exact (div_le_iff₀ ht).mpr hgoal

/-- The tilted optimum gives the lower secant bound for the tilted value. -/
theorem cost_le_semidiscreteValue_sub_div_of_tilted_optimal
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c g : S → Fin (m + 1) → ℝ) (a : S → Fin (m + 1) → ℝ)
    {p : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    {t : ℝ} (ht : 0 < t)
    (hopt : ∀ b, IsSemidiscreteAllocation μ p b →
      semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) a ≤
        semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) b) :
    semidiscreteAllocationCost μ g a ≤
      (semidiscreteValue μ (fun s j ↦ c s j + t * g s j) p -
        semidiscreteValue μ c p) / t := by
  have hct : ∀ j, Integrable (fun s ↦ c s j + t * g s j) μ :=
    fun j ↦ (hc j).add ((hg j).const_mul t)
  have hvalt : semidiscreteValue μ (fun s j ↦ c s j + t * g s j) p =
      semidiscreteAllocationCost μ (fun s j ↦ c s j + t * g s j) a :=
    semidiscreteValue_eq_cost_of_optimal μ _ hct p a ha hopt
  have hle := semidiscreteValue_le_cost μ c hc p a ha
  have hsplit := semidiscreteAllocationCost_tilt_affine μ c g a ha hc hg t
  rw [← hvalt] at hsplit
  have hca : semidiscreteAllocationCost μ c a =
      semidiscreteValue μ (fun s j ↦ c s j + t * g s j) p -
        t * semidiscreteAllocationCost μ g a := by
    linarith
  rw [hca] at hle
  rw [le_div_iff₀ ht]
  linarith

end OTSelector.Probability
