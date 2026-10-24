import LeanLevy.RandomMeasure.PoissonRandomMeasure
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import LeanPool.Vlasov.OT.Coupling
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
Conditions: An arbitrary topological measurable space, any measure and a point with strictly positive singleton outer measure; no Radon, finite-measure or Borel assumption is added.

Objects: The selected general lemma says that a positive-mass singleton belongs to the topological support of the measure.

Proof detail: Every neighborhood contains the point’s singleton; measure monotonicity transfers strict positivity to every neighborhood and hence to support membership.

References: D. H. Fremlin: 411N(b)–(e), p. 6: support, uniqueness, existence, and the closure of the continuous image of a support.
Relation: This is a direct consequence of the neighborhood support definition. All Finsler/original-cloud reconstruction statements elsewhere in the source file are outside this selected command.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalCountingSupportAtomicity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalCountingSupportAtomicity`; the selected original proof blocks follow. -/
section

/-!
# Counting support atomicity

This module closes one direction of support atomicity for counting measures and
records the exact obstruction for the converse.

1. **mem_support_of_singleton_pos**: for an arbitrary measure, a point with
   positive single-point mass belongs to the support.  Proof: every neighbourhood
   U of x contains x, so mu U >= mu {x} > 0 by monotonicity.

2. **countingMeasure_mem_support_of_multiplicity_pos**: for the counting measure
   of a local configuration, every occupied point (positive multiplicity) lies
   in the support, using countingMeasure_singleton.

3. **closure_atomSet_subset_support**: the closure of the atom set is contained
   in the support, since atoms are in the support and the support is closed.

## Exact remaining sub-gap

The CONVERSE (support membership implies positive single-point mass) is NOT
available.  In a non-proper space the support is the closure of the atom set, so
an accumulation point of atoms can lie in the support with zero single-point
mass; the equivalence needs the measure to have finitely many atoms in every
compact neighbourhood (or properness of the carrier plus integer multiplicities).
The library has no lemma evaluating the counting measure on open balls in terms
of the configuration's atoms, nor a finiteness-of-atoms-per-compact lemma, so
the converse - and hence the surjectivity of the matching edge index map onto
the whole scene support - is not derived here.  The affirmative direction and
the closure inclusion are proved; they discharge the hypothesis of
scene_source_mem_support_fst_of_singleton_pos in the direction available.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Positive single-point mass implies support membership.**  For an arbitrary
measure, a point carrying positive mass lies in the support. -/
theorem mem_support_of_singleton_pos
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) {x : X} (hx : 0 < μ {x}) :
    x ∈ μ.support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have hxU : x ∈ U := mem_of_mem_nhds hU
  refine lt_of_lt_of_le hx (measure_mono ?_)
  intro y hy
  rw [mem_singleton_iff] at hy
  subst hy
  exact hxU





end OTSelector.Reconstruction

end
end
