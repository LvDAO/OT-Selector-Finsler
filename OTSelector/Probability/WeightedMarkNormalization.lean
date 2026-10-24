import OTSelector.MeasureTheory.DominatedKernelVariation
import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation

/-!
Conditions: A finite original base measure with an integrable weighted Markov kernel, relative density oscillation and dominated conditional mark laws with a uniform total-variation bound; positive mass is explicit for normalization.

Objects: Actual weighted mass comparison, a finite-law freezing bound and invariance of normalized laws under positive scaling.

Proof detail: Integrate the density oscillation against Markov total mass, combine it with the raw mark-variation estimate, and cancel the actual positive total mass when normalizing.

References: D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; D. H. Fremlin: Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
Relation: A local weighted-kernel normalization estimate. Equal original masses are not imposed; mass discrepancy and conditional mark discrepancy remain separately justified before probability normalization.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.WeightedMarkNormalization.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.WeightedMarkNormalization`; the selected original proof blocks follow. -/
section

/-!
# Original masses and normalized weighted mark laws

Relative intensity oscillation controls the actual cell mass. Together with the
raw mark variation estimate, it supplies probability normalization and a common
submeasure without imposing equal original masses.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Integrating the pointwise intensity estimate preserves its relative error
with respect to the frozen mass. -/
theorem weighted_compProd_mass_error
    (μ : Measure X) [IsFiniteMeasure μ]
    (k : Kernel X Y) [IsMarkovKernel k]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    {ρ : X → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity ρ)]
    (hρ : Measurable ρ) {ρ₀ η : ℝ} (hρ₀ : 0 ≤ ρ₀)
    (hclose : ∀ᵐ x ∂μ, |(ρ x).toReal - ρ₀| ≤ η * ρ₀) :
    |(μ.withDensity ρ ⊗ₘ k).real univ -
      (ρ₀.toNNReal • μ.prod ν).real univ| ≤
      η * (ρ₀.toNNReal • μ.prod ν).real univ := by
  have hfi : (∫⁻ x, ρ x ∂μ) ≠ ∞ := by
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      using measure_ne_top (μ.withDensity ρ) univ
  have hi := integrable_toReal_of_lintegral_ne_top hρ.aemeasurable hfi
  have hmass : (μ.withDensity ρ ⊗ₘ k).real univ = ∫ x, (ρ x).toReal ∂μ := by
    rw [measureReal_def, Measure.compProd_apply_univ, withDensity_apply _ .univ,
      Measure.restrict_univ]
    exact (integral_toReal hρ.aemeasurable (ae_lt_top hρ hfi)).symm
  have hfrozen : (ρ₀.toNNReal • μ.prod ν).real univ = ρ₀ * μ.real univ := by
    rw [measureReal_nnreal_smul_apply, Real.coe_toNNReal _ hρ₀, measureReal_def,
      ← univ_prod_univ, Measure.prod_prod, measure_univ (μ := ν), mul_one]
    rfl
  rw [hmass, hfrozen]
  have hint : ∫ x, ((ρ x).toReal - ρ₀) ∂μ =
      (∫ x, (ρ x).toReal ∂μ) - ρ₀ * μ.real univ := by
    rw [integral_sub hi (integrable_const _), integral_const, smul_eq_mul, mul_comm]
  rw [← hint]
  have hb := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun x ↦ (ρ x).toReal - ρ₀) (C := η * ρ₀) (by
    filter_upwards [hclose] with x hx
    simpa only [Real.norm_eq_abs] using hx)
  simpa only [Real.norm_eq_abs, mul_assoc] using hb

/-- The actual weighted law and the constant-intensity, constant-mark law satisfy
both raw estimates needed for normalization and common-part sampling. -/
theorem weighted_compProd_freezingBound
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure X) [IsFiniteMeasure μ] (τ : Measure Y) [SFinite τ]
    (k : Kernel X Y) [IsMarkovKernel k]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    {ρ : X → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity ρ)]
    (hρ : Measurable ρ) (hk : ∀ᵐ x ∂μ, k x ≪ τ) (hν : ν ≪ τ)
    {ρ₀ η : ℝ} (hρ₀ : 0 ≤ ρ₀) (hη : 0 ≤ η)
    (hclose : ∀ᵐ x ∂μ, |(ρ x).toReal - ρ₀| ≤ η * ρ₀)
    (hmark : ∀ᵐ x ∂μ,
      ((k x).toSignedMeasure - ν.toSignedMeasure).totalVariation univ ≤ ENNReal.ofReal η) :
    FiniteLawFreezingBound (μ.withDensity ρ ⊗ₘ k) (ρ₀.toNNReal • μ.prod ν) η := by
  refine ⟨weighted_compProd_mass_error μ k ν hρ hρ₀ hclose, ?_⟩
  have hraw := totalVariation_weighted_compProd_le_of_absolutelyContinuous
    μ τ k ν hρ hk hν hρ₀ hη hclose hmark
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ univ)) hraw
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hb
  have hprod : (μ.prod ν).real univ = μ.real univ := by
    rw [measureReal_def, ← univ_prod_univ, Measure.prod_prod,
      measure_univ (μ := ν), mul_one]
    rfl
  rw [measureReal_nnreal_smul_apply, Real.coe_toNNReal _ hρ₀, hprod]
  simpa only [measureReal_def, mul_assoc] using hb

/-- Normalizing a positive scalar multiple uses the original measure's own mass. -/
theorem normalizedFiniteLaw_smul (μ : Measure X) [IsFiniteMeasure μ]
    {c : ℝ} (hc : 0 < c) (hμ : 0 < μ.real univ) :
    normalizedFiniteLaw (c.toNNReal • μ) = normalizedFiniteLaw μ := by
  unfold normalizedFiniteLaw
  rw [measureReal_nnreal_smul_apply, Real.coe_toNNReal _ hc.le, smul_smul]
  congr 1
  apply NNReal.coe_injective
  simp only [NNReal.coe_mul, Real.coe_toNNReal _ hc.le,
    Real.coe_toNNReal _ (inv_nonneg.mpr (mul_pos hc hμ).le),
    Real.coe_toNNReal _ (inv_nonneg.mpr hμ.le)]
  field_simp

/-- The normalized frozen law is exactly uniform sampling from the original Haar
cell followed by the original reference conditional mark. -/
theorem normalized_frozen_weighted_law
    (μ : Measure X) [IsFiniteMeasure μ] (ν : Measure Y) [IsProbabilityMeasure ν]
    {c : ℝ} (hc : 0 < c) (hμ : 0 < μ.real univ) :
    normalizedFiniteLaw (c.toNNReal • μ.prod ν) = (normalizedFiniteLaw μ).prod ν := by
  have hprod : (μ.prod ν).real univ = μ.real univ := by
    rw [measureReal_def, ← univ_prod_univ, Measure.prod_prod,
      measure_univ (μ := ν), mul_one]
    rfl
  rw [normalizedFiniteLaw_smul _ hc (hprod ▸ hμ)]
  simp only [normalizedFiniteLaw, hprod, Measure.prod_smul_left]

end OTSelector.Reconstruction

end
