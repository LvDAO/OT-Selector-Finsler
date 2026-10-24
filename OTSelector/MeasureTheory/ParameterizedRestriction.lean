import LeanLevy.RandomMeasure.PoissonRandomMeasure
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.NNReal
import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.HausdorffDimension
import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.LocalFiniteMeasure.Measurability
import OTSelector.MeasureTheory.LocalFiniteMeasureKernel
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalParameterizedRestriction.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalParameterizedRestriction`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ParameterizedRestriction

Conditions: A measurable locally finite measure field on the stated proper second-countable metric Borel carrier and one measurable subset of environment times carrier.
Objects: The original measure restricted to its environment-dependent measurable cell.
Proof detail: Regard the field as the existing S-finite kernel, integrate the product-cell indicator against that kernel, and rewrite the result as each restricted measure evaluation.

## Mathematical sources

- D. H. Fremlin, *Measure Theory, Volume 4*: Section 452A–452F (integration of families and disintegrations), 452M (product disintegration). https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
- D. H. Fremlin, *Measure Theory, Volume 4*: Sections 418A–418C, measurable maps, products, and limits into metrizable/Polish spaces. https://www1.essex.ac.uk/maths/people/fremlin/chap41.pdf#page=106

Source relation: A parameterized kernel-restriction corollary. Measurability belongs to the same original environment and moving set; there is no independent resampling.
-/

/-! # Borel restrictions of the actual plan to environment-dependent cells -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false

/-- Restrict the same actual measure to its environment's literal cell. -/
def originalParameterizedRestriction
    {X Ω : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]
    (μ : Ω → LocalFiniteMeasure X) (U : Set (Ω × X)) (ω : Ω) : LocalFiniteMeasure X :=
  ⟨(μ ω : Measure X).restrict (Prod.mk ω ⁻¹' U), inferInstance⟩

/-- The existing actual S-finite kernel proves measurability of moving-cell restriction. -/
theorem measurable_originalParameterizedRestriction
    {X Ω : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X] [MeasurableSpace Ω]
    (μ : Ω → LocalFiniteMeasure X) (hμ : Measurable μ)
    (U : Set (Ω × X)) (hU : MeasurableSet U) :
    Measurable (originalParameterizedRestriction μ U) := by
  let κ : Kernel Ω X := localFiniteMeasureKernel.comap μ hμ
  apply measurable_localFiniteMeasure_of_measurable_measure
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hm := κ.measurable_kernel_prodMk_left (hU.inter (measurable_snd hA))
  convert hm using 1
  funext ω
  change (μ ω : Measure X).restrict (Prod.mk ω ⁻¹' U) A =
    (μ ω : Measure X) (Prod.mk ω ⁻¹' (U ∩ Prod.snd ⁻¹' A))
  rw [Measure.restrict_apply hA]
  congr 1
  ext x
  simp [and_comm]

end OTSelector.Reconstruction

end
end
