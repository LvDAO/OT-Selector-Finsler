import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
Conditions: An s-finite base measure, s-finite kernels, a measurable base reparameterization and equality of the reparameterized kernel with the original kernel almost everywhere.

Objects: Exact pushforward equality of the original measure-kernel composition product after changing only its base coordinate.

Proof detail: Evaluate measurable rectangles, use the a.e. kernel equality under the original base integral and identify the transported composition product by the rectangle uniqueness principle.

References: D. H. Fremlin: 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula; Rick Durrett: Section 1.7, Theorem 1.7.2, p. 38.
Relation: A generic composition-product transport identity. No independent resampling or application-specific intensity assumption is included in the selected core.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationSeedIntensityLaw.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationSeedIntensityLaw`; the selected original proof blocks follow. -/
section

/-!
# The original joint population law in actual seed coordinates

The retained physical population pushes forward to its original Haar intensity
and its original scalar conditional kernel. Both colors use the same original
base measure and the same actual coordinate map.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- Changing only the base coordinate preserves the conditional kernel whenever
the new kernel agrees with the original one along that coordinate map. -/
theorem map_compProd_base_of_ae_kernel_eq
    {Z W X : Type*} [MeasurableSpace Z] [MeasurableSpace W] [MeasurableSpace X]
    (μ : Measure Z) [SFinite μ] (k : Kernel Z X) [IsSFiniteKernel k]
    (l : Kernel W X) [IsSFiniteKernel l] {r : Z → W} (hr : Measurable r)
    (heq : ∀ᵐ z ∂μ, l (r z) = k z) :
    (μ ⊗ₘ k).map (Prod.map r id) = μ.map r ⊗ₘ l := by
  ext s hs
  rw [Measure.map_apply (hr.prodMap measurable_id) hs,
    Measure.compProd_apply ((hr.prodMap measurable_id) hs), Measure.compProd_apply hs,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hr]
  apply lintegral_congr_ae
  filter_upwards [heq] with z hz
  rw [hz]
  rfl





end OTSelector.Reconstruction

end
end
