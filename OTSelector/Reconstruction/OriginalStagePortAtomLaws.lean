import OTSelector.Reconstruction.OriginalStageResidualDensityActualPorts
import OTSelector.Reconstruction.OriginalStageResidualDensityOrientedReflectedMass
import Mathlib.MeasureTheory.Measure.WithDensity

/-! The actual finite port atoms give the literal reflected class measures. -/
open Set Function Filter MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction

/-- Restricting an actual finite unit-atom measure keeps exactly the original atoms whose
unchanged marks belong to the stage. No independence of those atoms is used. -/
theorem originalFiniteEndpointAtoms_restrict {q n : ℕ}
    (points : Fin n → LegalMarkedPhysicalPoint q) (C : Set ℝ) (hC : MeasurableSet C) :
    (∑ i, Measure.dirac (points i)).restrict {p | p.2 ∈ C} =
      ∑ i, if (points i).2 ∈ C then Measure.dirac (points i) else 0 := by
  have hclass : MeasurableSet {p : LegalMarkedPhysicalPoint q | p.2 ∈ C} :=
    hC.preimage measurable_snd
  rw [← Measure.sum_fintype, Measure.restrict_sum _ hclass, Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  exact restrict_dirac

/-- Literal smoothing of the original port atoms is the finite sum of their own reflected
kernels. This is an exact measure readout and assumes no selected spatial law. -/
theorem originalFiniteEndpointAtoms_classDensity {q n : ℕ}
    (points : Fin n → LegalMarkedPhysicalPoint q) (C : Set ℝ) (hC : MeasurableSet C)
    (K : (Fin q → ℝ) → (Fin q → ℝ) → ℝ) (z : Fin q → ℝ) :
    (∫ p in {p | p.2 ∈ C}, K z p.1 ∂(∑ i, Measure.dirac (points i))) =
      ∑ i, if (points i).2 ∈ C then K z (points i).1 else 0 := by
  rw [originalFiniteEndpointAtoms_restrict points C hC, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  · intro i _
    split_ifs
    · exact integrable_dirac (by simp)
    · exact integrable_zero_measure

/-- The literal class density measure is the sum of the same original atoms' smoothed
measures. The nonnegative joint kernel is allowed to be the raw or chosen-frame reflection. -/
theorem originalFiniteEndpointAtoms_classMeasure {q n : ℕ}
    (points : Fin n → LegalMarkedPhysicalPoint q) (C : Set ℝ) (hC : MeasurableSet C)
    (K : (Fin q → ℝ) → (Fin q → ℝ) → ℝ)
    (hK : Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦ K p.1 p.2))
    (hKpos : ∀ z x, 0 ≤ K z x) (σ : Measure (Fin q → ℝ)) :
    σ.withDensity (fun z ↦ ENNReal.ofReal
      (∫ p in {p | p.2 ∈ C}, K z p.1 ∂(∑ i, Measure.dirac (points i)))) =
      ∑ i, if (points i).2 ∈ C then
        σ.withDensity (fun z ↦ ENNReal.ofReal (K z (points i).1)) else 0 := by
  have hm (i : Fin n) : Measurable (fun z ↦ if (points i).2 ∈ C then
      ENNReal.ofReal (K z (points i).1) else 0) := by
    split_ifs
    · exact (hK.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal
    · exact measurable_const
  ext U hU
  rw [withDensity_apply _ hU]
  simp_rw [originalFiniteEndpointAtoms_classDensity points C hC K]
  have heq (z : Fin q → ℝ) :
      ENNReal.ofReal (∑ i, if (points i).2 ∈ C then K z (points i).1 else 0) =
      ∑ i, if (points i).2 ∈ C then ENNReal.ofReal (K z (points i).1) else 0 := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by split_ifs; exact hKpos _ _; exact le_rfl)]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  simp_rw [heq]
  rw [lintegral_finsetSum _ (fun i _ ↦ hm i), Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [withDensity_apply _ hU]

end OTSelector.Reconstruction
