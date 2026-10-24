import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import LeanPool.Vlasov.OT.Coupling
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.HausdorffDimension
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneReadoutMacroscopicMarginals.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneReadoutMacroscopicMarginals`; the selected original proof blocks follow. -/
section

/-!
Conditions: Actual weak convergence of probability laws, a closed set and almost-everywhere support of every approximant there, under the stated outer-approximation topology assumptions.

Objects: The weak limit is carried on the same closed set.

Proof detail: Apply the open-set Portmanteau inequality to its complement and use zero approximating complement mass.

Sources: D. H. Fremlin, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation (https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61).
Relation: Portmanteau closed-carrier corollary. The abstract HasOuterApproxClosed assumptions are retained rather than replaced by a book’s Radon/metric assumptions.
-/

/-!
# Actual original macroscopic scene limits with exact full marginals

The original macro root is retained jointly with both original global plans
and their common integer target carrier. Original feasibility and energy
produce both separate weak stages, positive legal clocks and locally finite
full marginals; the fixed-frame tail and crossing estimates identify both
full limiting marginal pairs exactly.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false







/-- Closed original carriers persist under actual weak convergence. -/
theorem ae_closed_set_of_physicalScene_weak_tendsto
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] [HasOuterApproxClosed S]
    (R : ProbabilityMeasure S) (Pn : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto Pn atTop (𝓝 R)) (K : Set S) (hK : IsClosed K)
    (hmem : ∀ n, ∀ᵐ s ∂(Pn n : Measure S), s ∈ K) :
    ∀ᵐ s ∂(R : Measure S), s ∈ K := by
  have hn : ∀ n, (Pn n : Measure S) Kᶜ = 0 := fun n ↦ hmem n
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hK.isOpen_compl
  change (R : Measure S) Kᶜ ≤ atTop.liminf (fun n ↦ (Pn n : Measure S) Kᶜ) at hle
  simp only [hn, liminf_const] at hle
  exact le_antisymm hle bot_le


end OTSelector.Reconstruction

end
end
