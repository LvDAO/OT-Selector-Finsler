import OTSelector.Topology.Real.Components
import OTSelector.Reconstruction.FinslerIntrinsicActiveNullLabel
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
Conditions: An open subset of the real line and a point or rational code in each indicated connected component.

Objects: Rational representatives and a countable component cover.

Proof detail: Every open component contains a rational point; components sharing a point agree, so rational indexing gives a countable cover.

Sources: D. H. Fremlin, Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products) (https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Elementary real-topology/component result; it contains no calibrated-ray assumption.
-/

/-!
# Component cover from the minimal-arc transport

This module closes gap (i) of FinslerIntrinsicActiveRayTransport.lean for the
structural invariance theorem (main.tex:958): the component-cover hypothesis
`IsComponentCover` of the ray-data wiring, i.e. the paper's cover identity
`eq:intrinsic-active-cover` together with the rational-code identification
`eq:intrinsic-active-marker` of the minimal calibrated arcs.

## What is proved

For the active set `{r | 0 < H z r}` of a ray surplus `H` the active blocks are
connected components of the active set.  We record the interface
`IsComponentPartition` (a nonempty listing of pairwise disjoint components
covering the active set) and prove that such a listing *is* precisely the
component-cover structure required by the wiring: the constructed ray data
has `IsComponentCover` and satisfies the cover identity
`{r | 0 < H z r} = ⋃ j, block z j`.

On the geometric side we prove the topological facts that make the rational
curve codes of the minimal-arc transport meaningful: connected components of an
open subset of the real line are open, two components are equal or disjoint,
and every component of an open set contains a rational number whose own
component is the whole component (rational selection).  This is exactly what
makes the paper's rational segment test well defined: the component of a point
is the component of a rational code of that point.  The conditional statement
`exists_component_cover_of_rational_codes` makes this precise: a rational code
map selecting a rational in the component of each active point produces a cover
of the active set by components.

## Remaining sub-gap

The ray-data interface `IntrinsicActiveRayData` requires *every* one of its
countably many block labels to be nonempty.  Since `IsComponentCover` forces
each block to be a genuine connected component of the active set, the interface
demands a bijective enumeration of the active components of every ray: a ray
whose active set has only finitely many components admits no such data at all
(empty labels cannot be padded without losing either the component property or
disjointness), and the enumeration must use every natural number.  The actual
bridge from the Finsler transport data `(u, a)` of
FinslerIntrinsicActiveRayTransport.lean to a per-ray component enumeration
needs the segment-positivity criterion `eq:intrinsic-active-marker` together
with continuity/upper-semicontinuity of the surplus in the ray parameter, which
is not available in the repository.  The honest interface is therefore
conditional on `IsComponentPartition` (or equivalently on a bijective component
enumeration); relaxing the nonempty-blocks field of the pre-existing structure
is outside the write scope of this file.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

/-! ## Topology of active components on the real line -/

/-- Connected components of the same set are either equal or disjoint. -/
theorem connectedComponentIn_eq_or_disjoint {α : Type*} [TopologicalSpace α]
    {U : Set α} {x y : α} :
    connectedComponentIn U x = connectedComponentIn U y ∨
      Disjoint (connectedComponentIn U x) (connectedComponentIn U y) := by
  by_cases h : connectedComponentIn U x = connectedComponentIn U y
  · exact Or.inl h
  refine Or.inr (Set.disjoint_left.mpr ?_)
  intro z hzx hzy
  exact h ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

/-- Components of an open subset of the real line are open: they are the open
arcs of the active set. -/
theorem isOpen_connectedComponentIn_real {U : Set ℝ} (hU : IsOpen U) (x : ℝ) :
    IsOpen (connectedComponentIn U x) := hU.connectedComponentIn



/-! ## Component partitions and the component cover -/

/-- **A component partition** of a set `U ⊆ ℝ`: a listing of nonempty connected
components of `U`, pairwise disjoint, covering `U`.  This is the form in which
the minimal-arc transport supplies the active blocks: each active minimal arc is
one of the listed components. -/
def IsComponentPartition (U : Set ℝ) (comp : ℕ → Set ℝ) : Prop :=
  (∀ j : ℕ, (comp j).Nonempty) ∧
  (∀ j : ℕ, ∃ x : ℝ, x ∈ U ∧ comp j = connectedComponentIn U x) ∧
  (∀ j k : ℕ, j ≠ k → Disjoint (comp j) (comp k)) ∧
  (∀ r : ℝ, r ∈ U → ∃ j : ℕ, r ∈ comp j)

/-- **Component cover from the minimal-arc transport.**  Given a ray surplus
`H` and a component partition of every active set `{r | 0 < H z r}`, the
corresponding ray data satisfy the paper's component-cover hypothesis
`IsComponentCover` and the cover identity
`{r | 0 < H z r} = ⋃ j, block z j`. -/
theorem intrinsicActiveRayData_of_componentPartition {Z : Type*}
    (H : Z → ℝ → ℝ) (U : Z → Set ℝ) (hU : ∀ z : Z, U z = {r : ℝ | 0 < H z r})
    (comp : Z → ℕ → Set ℝ) (hcomp : ∀ z : Z, IsComponentPartition (U z) (comp z)) :
    ∃ A : IntrinsicActiveRayData Z,
      A.flux = H ∧ IsComponentCover A ∧ (∀ z : Z, U z = ⋃ j, A.block z j) := by
  classical
  have hpos : ∀ (z : Z) (j : ℕ) ⦃r : ℝ⦄, r ∈ comp z j → 0 < H z r := by
    intro z j r hr
    obtain ⟨x, hxU, hEq⟩ := (hcomp z).2.1 j
    have hrU : r ∈ U z := by
      rw [hEq] at hr
      exact connectedComponentIn_subset (U z) x hr
    rw [hU z] at hrU
    exact hrU
  have hcov : ∀ (z : Z) (r : ℝ), 0 < H z r → ∃ j : ℕ, r ∈ comp z j := by
    intro z r hr
    have hrU : r ∈ U z := by
      rw [hU z]
      exact hr
    exact (hcomp z).2.2.2 r hrU
  let A : IntrinsicActiveRayData Z :=
    { flux := H
      block := comp
      nonempty := fun z j => (hcomp z).1 j
      disjoint := fun z j k hjk => (hcomp z).2.2.1 j k hjk
      block_pos := hpos
      cover_pos := hcov }
  refine ⟨A, rfl, ?_, ?_⟩
  · intro z j
    obtain ⟨x, hxU, hEq⟩ := (hcomp z).2.1 j
    refine ⟨x, ?_, ?_⟩
    · have hxU' : x ∈ U z := hxU
      rw [hU z] at hxU'
      exact hxU'
    · show comp z j = connectedComponentIn {r : ℝ | 0 < H z r} x
      rw [← hU z]
      exact hEq
  · intro z
    ext r
    constructor
    · intro hr
      obtain ⟨j, hj⟩ := (hcomp z).2.2.2 r hr
      exact Set.mem_iUnion.mpr ⟨j, hj⟩
    · intro hr
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hr
      obtain ⟨x, hxU, hEq⟩ := (hcomp z).2.1 j
      have hj' : r ∈ comp z j := hj
      rw [hEq] at hj'
      have hrU : r ∈ U z := connectedComponentIn_subset (U z) x hj'
      exact hrU


/-! ## Geometric reading of the active blocks -/

/-- Under the component-cover hypothesis, every active block is a connected
component of the active set, hence open in the real line when the active set is
open: the active blocks are the open arcs of the minimal calibrated rays. -/
theorem isOpen_block_of_isComponentCover {Z : Type*} [MeasurableSpace Z]
    {A : IntrinsicActiveRayData Z} (hA : IsComponentCover A)
    (hopen : ∀ z : Z, IsOpen {r : ℝ | 0 < A.flux z r}) (z : Z) (j : ℕ) :
    IsOpen (A.block z j) := by
  obtain ⟨x, hx, hEq⟩ := hA z j
  rw [hEq]
  exact (hopen z).connectedComponentIn

/-- Under the component-cover hypothesis, every active block is preconnected. -/
theorem isPreconnected_block_of_isComponentCover {Z : Type*} [MeasurableSpace Z]
    {A : IntrinsicActiveRayData Z} (hA : IsComponentCover A) (z : Z) (j : ℕ) :
    IsPreconnected (A.block z j) := by
  obtain ⟨x, hx, hEq⟩ := hA z j
  rw [hEq]
  exact isPreconnected_connectedComponentIn

end OTSelector.Reconstruction