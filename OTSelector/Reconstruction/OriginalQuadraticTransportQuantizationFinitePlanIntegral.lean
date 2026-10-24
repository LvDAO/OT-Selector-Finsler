import OTSelector.Transport.Neumann.EndpointCoupling

/-! Literal real integrals of finite transport matrices. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
variable {I J : Type*} [Fintype I] [Fintype J]
  [MeasurableSpace I] [MeasurableSpace J]
  [DiscreteMeasurableSpace I] [DiscreteMeasurableSpace J]

/-- The real integral of any finite plan is its literal matrix-weighted sum. -/
theorem finitePlanMeasure_integral (P : I → J → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (c : I × J → ℝ) :
    Integrable c (finitePlanMeasure P) ∧
      (∫ z, c z ∂finitePlanMeasure P) = ∑ i, ∑ j, P i j * c (i, j) := by
  have hi : ∀ z : I × J, Integrable c
      (ENNReal.ofReal (P z.1 z.2) • Measure.dirac z) := by
    intro z
    exact (integrable_dirac (by finiteness)).smul_measure (by finiteness)
  refine ⟨integrable_finsetSum_measure.mpr (fun z _ ↦ hi z), ?_⟩
  rw [finitePlanMeasure, integral_finsetSum_measure (fun z _ ↦ hi z)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hP _ _),
    smul_eq_mul, Fintype.sum_prod_type]


end OTSelector.Reconstruction
