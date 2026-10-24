import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.DensityKernelVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.DensityKernelVariation`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.WeightedKernelVariation

## Lemma skeleton

* **Conditions:** Finite actual/frozen weighted laws with measurable probability mark densities, relative intensity error and a full mark total-variation bound.
* **Objects:** Exact variation density formula and a 2 eta rho0 times base-mass bound, including composition-product kernels.
* **Proof detail:** Express both laws relative to the same product reference, split intensity and mark errors by the triangle inequality, integrate normalized mark densities by Tonelli and identify full signed total variation.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).

Source relation (composition): Full variation of finite positive measures; equal total masses or halved probability-TV conventions are not assumed.
-/

/-!
# Full variation bounds for weighted mark densities

The original and frozen laws need not have equal mass. Relative intensity error
and the full variation of the probability marks contribute separately.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- Full signed variation is the integral of the absolute difference of the actual
finite density laws, without any probability normalization. -/
theorem totalVariation_sub_eq_lintegral_toReal
    {X : Type*} [MeasurableSpace X] (τ μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {f g : X → ℝ≥0∞} (hf : AEMeasurable f τ) (hg : AEMeasurable g τ)
    (hμ : τ.withDensity f = μ) (hν : τ.withDensity g = ν) :
    (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ =
      ∫⁻ x, ‖(f x).toReal - (g x).toReal‖ₑ ∂τ := by
  have hfi : (∫⁻ x, f x ∂τ) ≠ ∞ := by
    simpa only [← hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      using measure_ne_top μ univ
  have hgi : (∫⁻ x, g x ∂τ) ≠ ∞ := by
    simpa only [← hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
      using measure_ne_top ν univ
  have hsm : (τ.withDensityᵥ fun x ↦ (f x).toReal) = μ.toSignedMeasure := by
    simpa only [hμ] using withDensityᵥ_toReal hf hfi
  have htm : (τ.withDensityᵥ fun x ↦ (g x).toReal) = ν.toSignedMeasure := by
    simpa only [hν] using withDensityᵥ_toReal hg hgi
  rw [← hsm, ← htm, ← withDensityᵥ_sub
    (integrable_toReal_of_lintegral_ne_top hf hfi)
    (integrable_toReal_of_lintegral_ne_top hg hgi),
    SignedMeasure.totalVariation_eq_variation,
    Measure.variation_withDensityᵥ ((integrable_toReal_of_lintegral_ne_top hf hfi).sub
      (integrable_toReal_of_lintegral_ne_top hg hgi)),
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rfl

/-- Relative intensity and probability-mark errors bound the original unnormalized
joint density discrepancy by twice the tolerance times the frozen intensity mass. -/
theorem lintegral_weighted_mark_error_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (τ : Measure Y) [SFinite μ] [SFinite τ]
    {ρ : X → ℝ} {H : X × Y → ℝ} {H₀ : Y → ℝ}
    (hρ : Measurable ρ) (hH : Measurable H) (hH₀ : Measurable H₀)
    {ρ₀ η : ℝ} (hρ₀ : 0 ≤ ρ₀) (hη : 0 ≤ η)
    (hnorm : ∀ᵐ x ∂μ, ∫⁻ y, ‖H (x, y)‖ₑ ∂τ = 1)
    (hclose : ∀ᵐ x ∂μ, |ρ x - ρ₀| ≤ η * ρ₀)
    (hmark : ∀ᵐ x ∂μ, ∫⁻ y, ‖H (x, y) - H₀ y‖ₑ ∂τ ≤ ENNReal.ofReal η) :
    (∫⁻ p, ‖ρ p.1 * H p - ρ₀ * H₀ p.2‖ₑ ∂μ.prod τ) ≤
      ENNReal.ofReal (2 * η * ρ₀) * μ univ := by
  rw [lintegral_prod _ (by fun_prop)]
  calc
    _ ≤ ∫⁻ _ : X, ENNReal.ofReal (2 * η * ρ₀) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hnorm, hclose, hmark] with x hn hc hm
      have hpoint (y : Y) : ‖ρ x * H (x, y) - ρ₀ * H₀ y‖ₑ ≤
          ENNReal.ofReal |ρ x - ρ₀| * ‖H (x, y)‖ₑ +
            ENNReal.ofReal ρ₀ * ‖H (x, y) - H₀ y‖ₑ := by
        have heq : ρ x * H (x, y) - ρ₀ * H₀ y =
            (ρ x - ρ₀) * H (x, y) + ρ₀ * (H (x, y) - H₀ y) := by ring
        rw [heq]
        have hb := enorm_add_le ((ρ x - ρ₀) * H (x, y)) (ρ₀ * (H (x, y) - H₀ y))
        simp only [enorm_mul] at hb
        rw [← ofReal_norm (ρ x - ρ₀), ← ofReal_norm ρ₀, Real.norm_eq_abs,
          Real.norm_of_nonneg hρ₀] at hb
        exact hb
      calc
        _ ≤ ∫⁻ y, ENNReal.ofReal |ρ x - ρ₀| * ‖H (x, y)‖ₑ +
            ENNReal.ofReal ρ₀ * ‖H (x, y) - H₀ y‖ₑ ∂τ := lintegral_mono hpoint
        _ = ENNReal.ofReal |ρ x - ρ₀| + ENNReal.ofReal ρ₀ *
            (∫⁻ y, ‖H (x, y) - H₀ y‖ₑ ∂τ) := by
          rw [lintegral_add_left (by fun_prop), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hn, mul_one]
        _ ≤ ENNReal.ofReal (η * ρ₀) + ENNReal.ofReal ρ₀ * ENNReal.ofReal η :=
          add_le_add (ENNReal.ofReal_le_ofReal hc) (by gcongr)
        _ = ENNReal.ofReal (2 * η * ρ₀) := by
          rw [← ENNReal.ofReal_mul hρ₀, ← ENNReal.ofReal_add (mul_nonneg hη hρ₀)
            (mul_nonneg hρ₀ hη)]
          congr 1
          ring
    _ = _ := lintegral_const _

/-- A weighted kernel with a common mark density is the original joint density
law on the product reference measure, including its original mass. -/
theorem weighted_compProd_eq_withDensity_prod
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (τ : Measure Y) [SFinite μ] [SFinite τ]
    (k : Kernel X Y) [IsSFiniteKernel k]
    {ρ : X → ℝ≥0∞} {H : X × Y → ℝ≥0∞}
    (hρ : Measurable ρ) (hH : Measurable H)
    (hk : ∀ᵐ x ∂μ, τ.withDensity (fun y ↦ H (x, y)) = k x) :
    μ.withDensity ρ ⊗ₘ k = (μ.prod τ).withDensity (fun p ↦ ρ p.1 * H p) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_compProd hf,
    lintegral_withDensity_eq_lintegral_mul μ hρ (hf.lintegral_kernel_prod_right'),
    lintegral_withDensity_eq_lintegral_mul (μ.prod τ)
      (by fun_prop : Measurable (fun p : X × Y ↦ ρ p.1 * H p)) hf,
    lintegral_prod _ (by fun_prop)]
  apply lintegral_congr_ae
  filter_upwards [hk] with x hx
  change ρ x * (∫⁻ y, f (x, y) ∂k x) = ∫⁻ y, (ρ x * H (x, y)) * f (x, y) ∂τ
  rw [← hx, lintegral_withDensity_eq_lintegral_mul τ
    (by fun_prop : Measurable (fun y : Y ↦ H (x, y)))
    (by fun_prop : Measurable (fun y : Y ↦ f (x, y))),
    ← lintegral_const_mul _ (by fun_prop)]
  apply lintegral_congr
  intro y
  exact (mul_assoc _ _ _).symm

/-- Actual finite weighted laws have full variation at most the sum of their
intensity and mark errors. They are not rescaled to have equal mass. -/
theorem totalVariation_weighted_mark_laws_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (τ : Measure Y) [SFinite μ] [SFinite τ]
    (actual frozen : Measure (X × Y))
    [IsFiniteMeasure actual] [IsFiniteMeasure frozen]
    {ρ : X → ℝ} {H : X × Y → ℝ} {H₀ : Y → ℝ}
    (hρ : Measurable ρ) (hH : Measurable H) (hH₀ : Measurable H₀)
    (hρpos : ∀ x, 0 ≤ ρ x) (hHpos : ∀ p, 0 ≤ H p) (hH₀pos : ∀ y, 0 ≤ H₀ y)
    {ρ₀ η : ℝ} (hρ₀ : 0 ≤ ρ₀) (hη : 0 ≤ η)
    (hactual : (μ.prod τ).withDensity (fun p ↦ ENNReal.ofReal (ρ p.1 * H p)) = actual)
    (hfrozen : (μ.prod τ).withDensity (fun p ↦ ENNReal.ofReal (ρ₀ * H₀ p.2)) = frozen)
    (hnorm : ∀ᵐ x ∂μ, ∫⁻ y, ‖H (x, y)‖ₑ ∂τ = 1)
    (hclose : ∀ᵐ x ∂μ, |ρ x - ρ₀| ≤ η * ρ₀)
    (hmark : ∀ᵐ x ∂μ, ∫⁻ y, ‖H (x, y) - H₀ y‖ₑ ∂τ ≤ ENNReal.ofReal η) :
    (actual.toSignedMeasure - frozen.toSignedMeasure).totalVariation univ ≤
      ENNReal.ofReal (2 * η * ρ₀) * μ univ := by
  rw [totalVariation_sub_eq_lintegral_toReal (μ.prod τ) actual frozen
    (by fun_prop) (by fun_prop) hactual hfrozen]
  simp_rw [ENNReal.toReal_ofReal (mul_nonneg (hρpos _) (hHpos _)),
    ENNReal.toReal_ofReal (mul_nonneg hρ₀ (hH₀pos _))]
  exact lintegral_weighted_mark_error_le μ τ hρ hH hH₀ hρ₀ hη hnorm hclose hmark

/-- Freezing the original raw intensity and probability mark kernel gives a full
variation error of at most twice the tolerance times the frozen cell mass. -/
theorem totalVariation_weighted_compProd_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsFiniteMeasure μ] (τ : Measure Y) [SFinite τ]
    (k : Kernel X Y) [IsMarkovKernel k]
    (ν : Measure Y) [IsProbabilityMeasure ν]
    {ρ : X → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity ρ)]
    {H : X × Y → ℝ≥0∞} {H₀ : Y → ℝ≥0∞}
    (hρ : Measurable ρ) (hH : Measurable H) (hH₀ : Measurable H₀)
    (hk : ∀ᵐ x ∂μ, τ.withDensity (fun y ↦ H (x, y)) = k x)
    (hν : τ.withDensity H₀ = ν)
    {ρ₀ η : ℝ} (hρ₀ : 0 ≤ ρ₀) (hη : 0 ≤ η)
    (hclose : ∀ᵐ x ∂μ, |(ρ x).toReal - ρ₀| ≤ η * ρ₀)
    (hmark : ∀ᵐ x ∂μ,
      ((k x).toSignedMeasure - ν.toSignedMeasure).totalVariation univ ≤ ENNReal.ofReal η) :
    ((μ.withDensity ρ ⊗ₘ k).toSignedMeasure -
      (ρ₀.toNNReal • μ.prod ν).toSignedMeasure).totalVariation univ ≤
      ENNReal.ofReal (2 * η * ρ₀) * μ univ := by
  have hactual := (weighted_compProd_eq_withDensity_prod μ τ k hρ hH hk).symm
  have hfrozen : (μ.prod τ).withDensity (fun p ↦ ENNReal.ofReal ρ₀ * H₀ p.2) =
      ρ₀.toNNReal • μ.prod ν := by
    calc
      _ = ENNReal.ofReal ρ₀ • (μ.prod τ).withDensity (fun p ↦ H₀ p.2) :=
        withDensity_smul' _ _ ENNReal.ofReal_ne_top
      _ = _ := by
        rw [← prod_withDensity_right hH₀, hν]
        exact Measure.coe_nnreal_smul ρ₀.toNNReal (μ.prod ν)
  rw [totalVariation_sub_eq_lintegral_toReal (μ.prod τ) _ _
    (by fun_prop) (by fun_prop) hactual hfrozen]
  simp_rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hρ₀]
  have hnorm : ∀ᵐ x ∂μ, ∫⁻ y, ‖(H (x, y)).toReal‖ₑ ∂τ = 1 := by
    filter_upwards [hk] with x hx
    have hn : (∫⁻ y, H (x, y) ∂τ) = 1 := by
      have ht := congrArg (fun m : Measure Y ↦ m univ) hx
      simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        measure_univ] using ht
    have hfin : ∀ᵐ y ∂τ, H (x, y) < ∞ := ae_lt_top
      (by fun_prop) (by rw [hn]; exact ENNReal.one_ne_top)
    calc
      _ = ∫⁻ y, H (x, y) ∂τ := by
        apply lintegral_congr_ae
        filter_upwards [hfin] with y hy
        rw [← ofReal_norm, Real.norm_of_nonneg ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hy.ne]
      _ = 1 := hn
  have hmark' : ∀ᵐ x ∂μ,
      ∫⁻ y, ‖(H (x, y)).toReal - (H₀ y).toReal‖ₑ ∂τ ≤ ENNReal.ofReal η := by
    filter_upwards [hk, hmark] with x hx hm
    rw [totalVariation_sub_eq_lintegral_toReal τ (k x) ν
      (by fun_prop) hH₀.aemeasurable hx hν] at hm
    exact hm
  exact lintegral_weighted_mark_error_le μ τ hρ.ennreal_toReal hH.ennreal_toReal
    hH₀.ennreal_toReal hρ₀ hη hnorm hclose hmark'

end OTSelector.Reconstruction

end
