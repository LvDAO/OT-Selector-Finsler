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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import OTSelector.Probability.ConditionalFiniteCoreRecovery

/-!
Conditions: The displayed finite measurable disjoint label cores with their original complement, original source/target populations and a measurable label map.

Objects: An exact measurable finite partition of each original iid experiment by assignments to retained cores or complement, and recovery of the whole iid law by summing the raw restrictions.

Proof detail: Pull the finite core partition back coordinatewise, use disjointness to identify a unique assignment for every sample and sum the disjoint restricted product measures.

References: Rick Durrett: Section 4.1, definition and uniqueness, pp. 205–207; Example 4.1.5, p. 208; Theorem 4.1.9, pp. 210–211; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: A finite partition/decomposition identity. Each color is decomposed separately; it does not impose equal realized core counts or normalize each assignment restriction.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPopulationIIDCoreRecovery.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPopulationIIDCoreRecovery`; the selected original proof blocks follow. -/
section

/-!
# Exact finite core decompositions of the original iid populations

An assignment records one retained core, or the original complement, for each
sample. Summing all assignment restrictions recovers the entire original iid
law. The two colors are handled separately, so no equality of their sample
counts in individual cores is imposed.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

noncomputable section
namespace OTSelector.Reconstruction

/-- A finite family of root cores completed by its original complement. -/
def finitePopulationRootCell {Z J : Type*} (K : J → Set Z) : Option J → Set Z
  | none => (⋃ j, K j)ᶜ
  | some j => K j

/-- The original sample event with one prescribed retained core or complement
for each sample index. -/
def populationIIDCoreEvent {X Z I J : Type*} (a : X → Z) (K : J → Set Z)
    (assignment : I → Option J) : Set (I → X) :=
  univ.pi (fun i ↦ a ⁻¹' finitePopulationRootCell K (assignment i))

variable {X Z I J : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  [Fintype I] [Fintype J] {u : X → ℝ} {a : X → Z} {b : Z × ℝ → X}
  {lambda : Measure Z} {η₀ η₁ : Measure X} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {K : J → Set Z}

/-- The completed original root cells form a measurable partition. -/
theorem FiniteLabelCoreRecovery.root_cells
    (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K) :
    (∀ j, MeasurableSet (finitePopulationRootCell K j)) ∧
      Pairwise (fun i j ↦ Disjoint (finitePopulationRootCell K i)
        (finitePopulationRootCell K j)) ∧
      (⋃ j, finitePopulationRootCell K j) = univ := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    cases j with
    | none => exact (MeasurableSet.iUnion D.measurable).compl
    | some j => exact D.measurable j
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact disjoint_compl_left_iff_subset.mpr (subset_iUnion K j)
    | some i =>
      cases j with
      | none => exact disjoint_compl_right_iff_subset.mpr (subset_iUnion K i)
      | some j => exact D.disjoint (fun h ↦ hij (congrArg some h))
  · apply eq_univ_iff_forall.mpr
    intro z
    by_cases hz : z ∈ ⋃ j, K j
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hz
      exact mem_iUnion.mpr ⟨some j, hj⟩
    · exact mem_iUnion.mpr ⟨none, hz⟩

/-- Every original iid sample configuration belongs to exactly one measurable
assignment event, including samples outside the retained root cores. -/
theorem FiniteLabelCoreRecovery.iid_core_partition
    (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K) (ha : Measurable a) :
    (∀ assignment : I → Option J, MeasurableSet (populationIIDCoreEvent a K assignment)) ∧
      Pairwise (fun assignment assignment' : I → Option J ↦
        Disjoint (populationIIDCoreEvent a K assignment)
          (populationIIDCoreEvent a K assignment')) ∧
      (⋃ assignment : I → Option J, populationIIDCoreEvent a K assignment) = univ := by
  obtain ⟨hm, hd, hc⟩ := D.root_cells
  refine ⟨fun assignment ↦ MeasurableSet.univ_pi (fun i ↦ ha (hm (assignment i))), ?_, ?_⟩
  · intro assignment assignment' hne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ((hd hi).preimage a).set_pi (mem_univ i)
  · apply eq_univ_iff_forall.mpr
    intro x
    have hmem (i : I) : ∃ j, a (x i) ∈ finitePopulationRootCell K j := by
      exact mem_iUnion.mp (hc ▸ mem_univ (a (x i)))
    choose assignment hassign using hmem
    exact mem_iUnion.mpr ⟨assignment, fun i _ ↦ hassign i⟩

/-- Summing the raw assignment restrictions recovers the complete original iid
law for each color, including the original complementary samples. -/
theorem FiniteLabelCoreRecovery.iid_decomposition
    (D : FiniteLabelCoreRecovery u a b lambda η₀ η₁ K) (ha : Measurable a) :
    (∑ assignment : I → Option J,
      (Measure.pi (fun _ : I ↦ η₀)).restrict (populationIIDCoreEvent a K assignment)) =
        Measure.pi (fun _ : I ↦ η₀) ∧
    (∑ assignment : I → Option J,
      (Measure.pi (fun _ : I ↦ η₁)).restrict (populationIIDCoreEvent a K assignment)) =
        Measure.pi (fun _ : I ↦ η₁) := by
  obtain ⟨hm, hd, hc⟩ := D.iid_core_partition (I := I) ha
  have hsum (μ : Measure (I → X)) :
      (∑ assignment : I → Option J, μ.restrict (populationIIDCoreEvent a K assignment)) = μ := by
    rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hd hm, hc, Measure.restrict_univ]
  exact ⟨hsum _, hsum _⟩

end OTSelector.Reconstruction

end
end
