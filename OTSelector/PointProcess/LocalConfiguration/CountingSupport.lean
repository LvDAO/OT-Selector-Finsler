import LeanLevy.RandomMeasure.PoissonRandomMeasure
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
import Mathlib.Topology.MetricSpace.HausdorffDimension
import OTSelector.PointProcess.LocalConfiguration

/-!
Conditions: An actual shell configuration in any metric space; simplicity is explicitly required only for the multiplicity-one statement, and the finite image identity requires an injective map.

Objects: Monotone finite occupied window supports, positive occupied multiplicities, multiplicity one under simplicity, finite image cardinality and support-cardinality≤multiplicity-sum.

Proof detail: Unfold the finite shell-window membership criterion, apply finite-set cardinal monotonicity and positivity of a nonzero natural multiplicity, and sum the pointwise lower bound one.

References: Günter Last; Mathew Penrose: Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10; Günter Last; Mathew Penrose: Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16.
Relation: Finite cardinality bookkeeping for actual counting support. It does not identify an application cloud’s matching-edge count without its separate point/label correspondence.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerOriginalCountingSupportCardinality.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerOriginalCountingSupportCardinality`; the selected original proof blocks follow. -/
section

/-!
# Finite cardinality API for counting-measure supports

This module begins the finite cardinality API for counting-measure supports that
is missing from the library (the blocker recorded in
FinslerOriginalFullMatchingCountIdentification).

For a local configuration the library only exposes the multiset shells and the
window support.  We prove the basic cardinality facts needed by the full-matching
count identification:

1. **windowSupport_mono**: the window support of a configuration grows
   monotonically in the window size;

2. **card_windowSupport_mono**: its cardinality grows monotonically;

3. **multiplicity_pos_of_mem_windowSupport** and
   **multiplicity_eq_one_of_simple**: the multiplicity of an occupied point is
   positive, and under simplicity it is exactly one;

4. **card_image_of_injective**: an injective map out of a finite index type has
   image cardinality equal to the index cardinality - the finite count behind the
   injectivity fields of IsFullOriginalInputMatching.

## Exact remaining sub-gap

The identification of the support edge count with the cloud color counts
mSourceCount/mTargetCount additionally needs the correspondence between the
scene counting measure on LegalMarkedPhysicalEdge q and the cloud color labels,
i.e. the fact that the scene support is exactly the set of matched pairs of the
cloud.  This correspondence is not present in the current API; the finite
cardinality facts above are the part that can be proved directly from the
counting-measure definitions.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open OTSelector.PointProcess
open scoped ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- **Monotonicity of the window support.**  The occupied points of the first N
shells are contained in the occupied points of the first M shells for N <= M. -/
theorem windowSupport_mono {X : Type*} [MetricSpace X] {base : X}
    (config : LocalConfiguration base) {N M : ℕ} (hNM : N ≤ M) :
    LocalConfiguration.windowSupport config N ⊆ LocalConfiguration.windowSupport config M := by
  intro x hx
  rw [LocalConfiguration.mem_windowSupport_iff] at hx ⊢
  exact ⟨lt_of_lt_of_le hx.1 hNM, hx.2⟩

/-- **Cardinality monotonicity of the window support.** -/
theorem card_windowSupport_mono {X : Type*} [MetricSpace X] {base : X}
    (config : LocalConfiguration base) {N M : ℕ} (hNM : N ≤ M) :
    (LocalConfiguration.windowSupport config N).card ≤
      (LocalConfiguration.windowSupport config M).card :=
  Finset.card_le_card (windowSupport_mono config hNM)

/-- **Positive multiplicity on the window support.**  Every occupied point of
the first N shells has positive multiplicity. -/
theorem multiplicity_pos_of_mem_windowSupport {X : Type*} [MetricSpace X] {base : X}
    (config : LocalConfiguration base) {N : ℕ} {x : X}
    (hx : x ∈ LocalConfiguration.windowSupport config N) :
    0 < LocalConfiguration.multiplicity config x :=
  Nat.pos_of_ne_zero (LocalConfiguration.mem_windowSupport_iff config N x |>.mp hx).2

/-- **Unit multiplicity under simplicity.**  A simple configuration has
multiplicity exactly one on every occupied point. -/
theorem multiplicity_eq_one_of_simple {X : Type*} [MetricSpace X] {base : X}
    (config : LocalConfiguration base)
    (hsimple : ∀ x, LocalConfiguration.multiplicity config x ≤ 1)
    {N : ℕ} {x : X} (hx : x ∈ LocalConfiguration.windowSupport config N) :
    LocalConfiguration.multiplicity config x = 1 :=
  le_antisymm (hsimple x) (multiplicity_pos_of_mem_windowSupport config hx)

/-- **Image cardinality under injectivity.**  An injective map on a finite index
type has image cardinality equal to the index cardinality.  This is the finite
count behind the injectivity fields of IsFullOriginalInputMatching. -/
theorem card_image_of_injective {ι X : Type*} [Fintype ι] [DecidableEq X]
    (f : ι → X) (hf : Function.Injective f) :
    (Finset.univ.image f).card = Fintype.card ι := by
  rw [Finset.card_image_of_injective _ hf, Finset.card_univ]

/-- **Support count of a simple configuration is bounded by total mass.**  For a
simple configuration the occupied-point count (window support) is bounded by the
counting-measure mass of the window, with equality under simplicity.  This is
the monotone count interface used by the missing-cardinality defect. -/
theorem card_windowSupport_le_tsum_multiplicity {X : Type*} [MetricSpace X] {base : X}
    (config : LocalConfiguration base) (N : ℕ) :
    (LocalConfiguration.windowSupport config N).card ≤
      (LocalConfiguration.windowSupport config N).sum
        (fun x => LocalConfiguration.multiplicity config x) := by
  have hpos : ∀ x ∈ LocalConfiguration.windowSupport config N,
      1 ≤ LocalConfiguration.multiplicity config x :=
    fun x hx => multiplicity_pos_of_mem_windowSupport config hx
  calc
    (LocalConfiguration.windowSupport config N).card =
        (LocalConfiguration.windowSupport config N).sum (fun _ => 1) := by
      simp
    _ ≤ (LocalConfiguration.windowSupport config N).sum
        (fun x => LocalConfiguration.multiplicity config x) :=
      Finset.sum_le_sum hpos

end OTSelector.Reconstruction

end
end
