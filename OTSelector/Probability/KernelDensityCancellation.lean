import OTSelector.Transport.Coupling.FiniteClockMixture
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawDensityCancellation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawDensityCancellation`; the selected original proof blocks follow. -/
section

/-!
# Probability.KernelDensityCancellation

## Lemma skeleton

* **Conditions:** A measurable original root density positive almost everywhere, arbitrary measurable real class weights and SFinite component kernels.
* **Objects:** Exact cancellation of root density with the retained kernel normalization, also for finite class flows.
* **Proof detail:** Evaluate the composition products, multiply the positive density by each divided class weight and cancel it almost everywhere; finite sums distribute over the identity.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.

Source relation (composition): Weighted-kernel change of density; positivity is used exactly where division cancels. Real weights are interpreted by the existing nonnegative kernel encoding.
-/

/-!
The original root density cancels the retained conditional normalization in
actual marked population laws. Both arbitrary measurable scalar class weights
and full finite pair-class flows retain the original Haar-cell measure exactly.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The original positive root density cancels its normalization in an actual
retained conditional law, leaving the original Haar cell and fixed class mass. -/
theorem compProd_original_density_cancel
    {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [SFinite μ] (d p : Z → ℝ)
    (hd : Measurable d) (hp : Measurable p) (hpos : ∀ᵐ z ∂μ, 0 < d z)
    (κ : Kernel Z X) [IsSFiniteKernel κ] :
    μ.withDensity (fun z ↦ ENNReal.ofReal (d z)) ⊗ₘ
        classWeightedKernel (fun z ↦ p z / d z) κ =
      μ ⊗ₘ classWeightedKernel p κ := by
  have hratio : Measurable (fun z ↦ p z / d z) :=
    measurable_div.comp (hp.prodMk hd)
  ext A hA
  rw [Measure.compProd_apply hA, Measure.compProd_apply hA,
    lintegral_withDensity_eq_lintegral_mul μ hd.ennreal_ofReal
      (Kernel.measurable_kernel_prodMk_left hA)]
  apply lintegral_congr_ae
  filter_upwards [hpos] with z hz
  simp only [Pi.mul_apply]
  rw [classWeightedKernel_apply _ hratio κ z, classWeightedKernel_apply p hp κ z]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← ENNReal.ofReal_mul hz.le]
  have he : d z * (p z / d z) = p z  := by field_simp [hz.ne']
  rw [he]

/-- Full original finite pair-class laws cancel the same root density, entry
by entry, before either marginal or class observation is taken. -/
theorem compProd_original_density_cancel_classFlow
    {I J Z X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) [SFinite μ] (d : Z → ℝ) (hd : Measurable d)
    (hpos : ∀ᵐ z ∂μ, 0 < d z) (P : I → J → ℝ)
    (α : I → Kernel Z X) (β : J → Kernel Z Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)] :
    μ.withDensity (fun z ↦ ENNReal.ofReal (d z)) ⊗ₘ
        finiteClassPopulationKernel (fun z i j ↦ P i j / d z) α β =
      μ ⊗ₘ finiteClassPopulationKernel (fun _ i j ↦ P i j) α β := by
  classical
  have hm (i j) : Measurable (fun z ↦ P i j / d z) :=
    measurable_div.comp (measurable_const.prodMk hd)
  ext A hA
  rw [Measure.compProd_apply hA, Measure.compProd_apply hA,
    lintegral_withDensity_eq_lintegral_mul μ hd.ennreal_ofReal
      (Kernel.measurable_kernel_prodMk_left hA)]
  apply lintegral_congr_ae
  filter_upwards [hpos] with z hz
  simp only [Pi.mul_apply]
  rw [finiteClassPopulationKernel_apply _ hm α β z,
    finiteClassPopulationKernel_apply (fun _z : Z ↦ P) (fun _ _ ↦ measurable_const) α β z]
  simp only [finiteClassPopulationCoupling, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc, ← ENNReal.ofReal_mul hz.le]
  have he : d z * (P i j / d z) = P i j  := by field_simp [hz.ne']
  rw [he]

end OTSelector.Reconstruction

end
end
