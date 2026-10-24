import OTSelector.Probability.CavitySemidiscreteCoupling
import OTSelector.Probability.CavitySemidiscreteBlockReadout

/-!
# Actual coupling masses of allocation blocks

The scalar block masses used in exchange and phase averaging are exactly the
rectangle masses of the original full coupling measures. Arbitrary measurable
source maps include spatial rooting; finite target maps allow repeated points.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal Classical

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S X Y : Type*}
  [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace Y]

/-- The actual source-label coupling assigns a rectangle exactly its allocation mass. -/
theorem IsSemidiscreteAllocation.allocationMeasure_prod
    {μ : Measure S} {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a) (A : Set S) (hA : MeasurableSet A)
    (J : Finset (Fin (m + 1))) :
    semidiscreteAllocationMeasure μ a (A ×ˢ (J : Set (Fin (m + 1)))) =
      ENNReal.ofReal (semidiscreteBlockMass μ a A J) := by
  classical
  have hterm (j : Fin (m + 1)) :
      ((μ.withDensity (fun s ↦ ENNReal.ofReal (a s j))).map (fun s ↦ (s, j)))
        (A ×ˢ (J : Set (Fin (m + 1)))) =
      if j ∈ J then ENNReal.ofReal (∫ s in A, a s j ∂μ) else 0 := by
    rw [Measure.map_apply (show Measurable (fun s : S ↦ (s, j)) from
      measurable_id.prodMk measurable_const) (hA.prod J.measurableSet)]
    by_cases hj : j ∈ J
    · have heq : (fun s : S ↦ (s, j)) ⁻¹' (A ×ˢ (J : Set (Fin (m + 1)))) = A := by
        ext s
        simp [hj]
      rw [heq, withDensity_apply _ hA]
      simp only [hj, ite_true]
      exact (ofReal_integral_eq_lintegral_ofReal (ha.integrable j).integrableOn
        (ae_restrict_of_ae (ha.nonneg.mono fun _ h ↦ h j))).symm
    · have heq : (fun s : S ↦ (s, j)) ⁻¹' (A ×ˢ (J : Set (Fin (m + 1)))) = ∅ := by
        ext s
        simp [hj]
      simp only [heq, measure_empty, hj, ite_false]
  rw [semidiscreteAllocationMeasure, Measure.finsetSum_apply]
  simp_rw [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  exact (ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ integral_nonneg_of_ae
    (ae_restrict_of_ae (ha.nonneg.mono fun _ h ↦ h j)))).symm

/-- Measurable spatial rooting and an arbitrary actual target cloud preserve the
rectangle/block-mass identity, including target collisions. -/
theorem IsSemidiscreteAllocation.map_allocationMeasure_prod
    {μ : Measure S} {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a)
    (f : S → X) (hf : Measurable f) (y : Fin (m + 1) → Y)
    (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ((semidiscreteAllocationMeasure μ a).map (Prod.map f y)) (A ×ˢ B) =
      ENNReal.ofReal (semidiscreteBlockMass μ a (f ⁻¹' A)
        (Finset.univ.filter (fun j ↦ y j ∈ B))) := by
  classical
  rw [Measure.map_apply (hf.prodMap (measurable_of_finite y)) (hA.prod hB)]
  have heq : (Prod.map f y) ⁻¹' (A ×ˢ B) =
      (f ⁻¹' A) ×ˢ (↑(Finset.univ.filter (fun j ↦ y j ∈ B)) : Set (Fin (m + 1))) := by
    ext z
    simp
  rw [heq]
  exact ha.allocationMeasure_prod _ (hA.preimage hf) _

/-- The bounded witness of the actual mass-`N` rooted coupling is exactly the
normalized-allocation witness controlled by the grid theorem. -/
theorem IsSemidiscreteAllocation.scaled_map_cycle_witness
    {μ : Measure S} {p : Fin (m + 1) → ℝ} {a : S → Fin (m + 1) → ℝ}
    (ha : IsSemidiscreteAllocation μ p a)
    (f : S → X) (hf : Measurable f) (y : Fin (m + 1) → Y)
    (A₀ A₁ : Set X) (B₀ B₁ : Set Y)
    (hA₀ : MeasurableSet A₀) (hA₁ : MeasurableSet A₁)
    (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁)
    (N : ℝ) (hN : 0 ≤ N) :
    min 1 (min
      ((ENNReal.ofReal N • (semidiscreteAllocationMeasure μ a).map (Prod.map f y)) (A₀ ×ˢ B₀))
      ((ENNReal.ofReal N • (semidiscreteAllocationMeasure μ a).map (Prod.map f y)) (A₁ ×ˢ B₁))) =
    ENNReal.ofReal (min 1 (N * min
      (semidiscreteBlockMass μ a (f ⁻¹' A₀) (Finset.univ.filter (fun j ↦ y j ∈ B₀)))
      (semidiscreteBlockMass μ a (f ⁻¹' A₁) (Finset.univ.filter (fun j ↦ y j ∈ B₁))))) := by
  classical
  rw [Measure.smul_apply, Measure.smul_apply,
    ha.map_allocationMeasure_prod f hf y A₀ B₀ hA₀ hB₀,
    ha.map_allocationMeasure_prod f hf y A₁ B₁ hA₁ hB₁]
  simp only [smul_eq_mul, mul_min_of_nonneg _ _ hN, ENNReal.ofReal_min,
    ENNReal.ofReal_mul hN, ENNReal.ofReal_one]

end OTSelector.Probability
