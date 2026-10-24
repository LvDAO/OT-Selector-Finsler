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
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import OTSelector.Probability.RadonNikodymMarkCoarsening
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawOriginalCellRefinedMarks.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawOriginalCellRefinedMarks`; the selected original proof blocks follow. -/
section

/-!
# Probability.CellRefinedMarkComponents

## Lemma skeleton

* **Conditions:** Arbitrary original-type-indexed residual/good component measures and cell-indexed bad components, with finite type/cell sets for regrouping.
* **Objects:** A refined tag type and exact regrouping to old types or retained/residual Boolean types.
* **Proof detail:** Define the finite sum type, project each tag to its old or Boolean type and sum the corresponding component fibers.

## Mathematical sources

- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.

Source relation (composition): Combinatorial bookkeeping of positive component measures; no probabilistic independence or geometry is added.
-/

/-! The same original atlas types carry good retained, cell-specific bad, and residual marks. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

/-- Good retained types use only the original atlas index. Bad types also remember their cell.
The false left flag denotes the original residual; the true left flag denotes good retention. -/
abbrev CellRefinedType (C T : Type*) := Sum (Bool × T) (C × T)

/-- Forget the good/bad/residual subdivision, keeping the actual original atlas type. -/
def cellRefinedOldType {C T : Type*} : CellRefinedType C T → T
  | .inl p => p.2
  | .inr p => p.2

/-- Recover the exact original deterministic-subplan flag: true is residual. -/
def cellRefinedSubplanType {C T : Type*} : CellRefinedType C T → Bool × T
  | .inl p => (!p.1, p.2)
  | .inr p => (false, p.2)

/-- The physical component associated to each explicit fine mark. -/
def cellRefinedComponent {X C T : Type*} [MeasurableSpace X]
    (residual good : T → Measure X) (bad : C → T → Measure X) :
    CellRefinedType C T → Measure X
  | .inl p => if p.1 then good p.2 else residual p.2
  | .inr p => bad p.1 p.2

/-- Fiberwise reconstruction keeps each original atlas type separately. -/
theorem cellRefinedComponent_grouped_old {X C T : Type*} [MeasurableSpace X]
    [Fintype C] [Fintype T] (residual good : T → Measure X)
    (bad : C → T → Measure X) (t : T) :
    groupedMarkComponent (cellRefinedComponent residual good bad) cellRefinedOldType t =
      residual t + good t + ∑ c, bad c t := by
  classical
  simp only [groupedMarkComponent, Finset.sum_filter, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_bool, cellRefinedOldType, cellRefinedComponent]
  simp [add_comm]

/-- The original residual fiber is unchanged. -/
theorem cellRefinedComponent_grouped_residual {X C T : Type*} [MeasurableSpace X]
    [Fintype C] [Fintype T] (residual good : T → Measure X)
    (bad : C → T → Measure X) (t : T) :
    groupedMarkComponent (cellRefinedComponent residual good bad) cellRefinedSubplanType
      (true, t) = residual t := by
  classical
  simp only [groupedMarkComponent, Finset.sum_filter, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_bool, cellRefinedSubplanType, cellRefinedComponent]
  simp [add_comm]

/-- The retained fiber is exactly good mass plus its cell-specific discarded pieces. -/
theorem cellRefinedComponent_grouped_retained {X C T : Type*} [MeasurableSpace X]
    [Fintype C] [Fintype T] (residual good : T → Measure X)
    (bad : C → T → Measure X) (t : T) :
    groupedMarkComponent (cellRefinedComponent residual good bad) cellRefinedSubplanType
      (false, t) = good t + ∑ c, bad c t := by
  classical
  simp only [groupedMarkComponent, Finset.sum_filter, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Fintype.sum_bool, cellRefinedSubplanType, cellRefinedComponent]
  simp

end OTSelector.Reconstruction

end
end
