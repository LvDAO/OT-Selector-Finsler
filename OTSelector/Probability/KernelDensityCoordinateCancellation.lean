import OTSelector.Probability.KernelBaseMarginal
import OTSelector.Probability.KernelDensityCancellation
import OTSelector.Transport.Coupling.FiniteClockMixture

/-!
Conditions: Sigma-finite original/root reference measures with an exact coordinate pushforward density d>0 a.e., measurable weights and actual kernels scaled by the reciprocal d in those coordinates.

Objects: Exact cancellation of the original root density in a kernel composition product, including a finite pair-class-flow specialization.

Proof detail: Push the original base to its weighted coordinate measure, apply change of density and cancel d against the explicit reciprocal factor, then sum the same identity over the finite class flow.

References: D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; D. H. Fremlin: 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula.
Relation: A local positive-density coordinate cancellation. Positivity is an explicit a.e. hypothesis, and the original within-bin kernels and raw finite class weights are retained.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawDensityCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawDensityCoordinates`; the selected original proof blocks follow. -/
section

/-!
Original root-coordinate pushforward and exact density cancellation identify
retained marked population laws with their original Haar-cell laws before
class observation. Both scalar weights and full finite pair-class flows are
supported, with the same actual within-bin kernels.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Original coordinate pushforward and density cancellation identify the
literal retained marked law with its Haar-cell law before class observation. -/
theorem compProd_original_coordinate_density_cancel
    {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W] [MeasurableSpace X]
    (r : Measure Z) [SFinite r] (μ : Measure W) [SFinite μ]
    (R : Z → W) (hR : Measurable R)
    (d p : W → ℝ) (hd : Measurable d) (hp : Measurable p)
    (hpos : ∀ᵐ w ∂μ, 0 < d w)
    (hbase : r.map R = μ.withDensity (fun w ↦ ENNReal.ofReal (d w)))
    (K : Kernel Z X) [IsSFiniteKernel K] (κ : Kernel W X) [IsSFiniteKernel κ]
    (hK : ∀ᵐ z ∂r, K z = ENNReal.ofReal (p (R z) / d (R z)) • κ (R z)) :
    (r ⊗ₘ K).map (Prod.map R id) = μ ⊗ₘ classWeightedKernel p κ := by
  have hmratio : Measurable (fun w ↦ p w / d w) := measurable_div.comp (hp.prodMk hd)
  rw [map_compProd_base_of_ae_kernel_eq r K
    (classWeightedKernel (fun w ↦ p w / d w) κ) hR (by
      filter_upwards [hK] with z hz
      rw [classWeightedKernel_apply _ hmratio κ (R z)]
      exact hz.symm), hbase]
  exact compProd_original_density_cancel μ d p hd hp hpos κ

/-- The same bridge transports the whole retained finite pair-class flow,
including both original within-bin clock laws, onto its Haar-cell measure. -/
theorem compProd_original_coordinate_density_cancel_classFlow
    {I J Z W X Y : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Z] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    (r : Measure Z) [SFinite r] (μ : Measure W) [SFinite μ]
    (R : Z → W) (hR : Measurable R) (d : W → ℝ) (hd : Measurable d)
    (hpos : ∀ᵐ w ∂μ, 0 < d w)
    (hbase : r.map R = μ.withDensity (fun w ↦ ENNReal.ofReal (d w)))
    (P : I → J → ℝ) (α : I → Kernel W X) (β : J → Kernel W Y)
    [∀ i, IsSFiniteKernel (α i)] [∀ j, IsSFiniteKernel (β j)]
    (K : Kernel Z (X × Y)) [IsSFiniteKernel K]
    (hK : ∀ᵐ z ∂r, K z = finiteClassPopulationKernel (fun w i j ↦ P i j / d w) α β (R z)) :
    (r ⊗ₘ K).map (Prod.map R id) =
      μ ⊗ₘ finiteClassPopulationKernel (fun _ i j ↦ P i j) α β := by
  rw [map_compProd_base_of_ae_kernel_eq r K _ hR (hK.mono fun z hz ↦ hz.symm), hbase]
  exact compProd_original_density_cancel_classFlow μ d hd hpos P α β

end OTSelector.Reconstruction

end
end
