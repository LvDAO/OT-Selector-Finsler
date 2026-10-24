import OTSelector.Reconstruction.OriginalMarkedPressureParameterMeasurability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Actual original thermodynamic pressure limits have measurable versions.
Both conditional laws, all literal coefficients and physical root tilts may vary. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 700000

variable {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B]
  [Nonempty A] [Nonempty B] [StandardBorelSpace A] [StandardBorelSpace B]
  (q : ℕ) (α : Kernel Z A) [IsMarkovKernel α] (β : Kernel Z B) [IsMarkovKernel β]
  {source : Z → A → ℝ} {target : Z → B → ℝ}
  (hs : Measurable (uncurry source)) (ht : Measurable (uncurry target))
  {kin : Z → A → B → (Fin q → ℝ) → ℝ}
  (hk : Measurable (fun p : Z × ((A × B) × (Fin q → ℝ)) ↦
    kin p.1 p.2.1.1 p.2.1.2 p.2.2))
  {probe : Z → A → B → ℝ}
  (hg : Measurable (fun p : Z × (A × B) ↦ probe p.1 p.2.1 p.2.2))
  (tilt : Z → ℝ) (htilt : Measurable tilt)

include hs ht hk hg htilt

/-- Every literal original scale pressure is measurable in the original root,
with its actual root-dependent physical tilt. -/
theorem measurable_original_legalMarkedScalePressure (R : ℝ) :
    Measurable (fun z ↦ legalMarkedScalePressure q (source z) (target z)
      (α z) (β z) (kin z) (probe z) R (tilt z)) := by
  unfold legalMarkedScalePressure
  by_cases hR : 0 < R
  · simp only [hR,↓reduceIte]
    exact (measurable_original_legalMarkedPressure q α β hs ht hk hg
      (Real.toNNReal (R^q)) tilt htilt).div_const _
  · simp only [hR,↓reduceIte]
    exact measurable_const

/-- Pointwise existence of the true original thermodynamic pressure produces
actual measurability; no measurable optimizer or pressure selection is assumed. -/
theorem measurable_original_legalMarkedPressure_limit
    {p : Z → ℝ}
    (hlim : ∀ z, Tendsto (fun R : ℝ ↦ legalMarkedScalePressure q (source z) (target z)
      (α z) (β z) (kin z) (probe z) R (tilt z)) atTop (𝓝 (p z))) :
    Measurable p := by
  apply measurable_of_tendsto_metrizable
    (fun n : ℕ ↦ measurable_original_legalMarkedScalePressure q α β hs ht hk hg tilt htilt
      (n : ℝ))
  rw [tendsto_pi_nhds]
  intro z
  exact (hlim z).comp tendsto_natCast_atTop_atTop

/-- Almost-everywhere true original pressure limits are strongly measurable
for the completed original population integral, without assuming root versions. -/
theorem aestronglyMeasurable_original_legalMarkedPressure_limit
    (lambda : Measure Z) {p : Z → ℝ}
    (hlim : ∀ᵐ z ∂lambda,
      Tendsto (fun R : ℝ ↦ legalMarkedScalePressure q (source z) (target z)
        (α z) (β z) (kin z) (probe z) R (tilt z)) atTop (𝓝 (p z))) :
    AEStronglyMeasurable p lambda := by
  apply AEMeasurable.aestronglyMeasurable
  apply aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n : ℕ ↦ (measurable_original_legalMarkedScalePressure q α β hs ht hk hg tilt htilt
      (n : ℝ)).aemeasurable)
  filter_upwards [hlim] with z hz
  exact hz.comp tendsto_natCast_atTop_atTop

end OTSelector.Reconstruction
