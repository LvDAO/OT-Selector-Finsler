import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerIntrinsicActiveComponentCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerIntrinsicActiveComponentCover`; the selected original proof blocks follow. -/
section

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





/-- **Rational selection.**  Every component of an open subset of the real line
contains a rational number, and the component of that rational is the whole
component.  This is the topological content of the paper's rational curve codes
`eq:intrinsic-active-marker`. -/
theorem exists_rat_connectedComponentIn_eq {U : Set ℝ} (hU : IsOpen U) {x : ℝ}
    (hx : x ∈ U) :
    ∃ q : ℚ, ((q : ℝ) ∈ connectedComponentIn U x) ∧
      connectedComponentIn U (q : ℝ) = connectedComponentIn U x := by
  have hnon : (connectedComponentIn U x).Nonempty := ⟨x, mem_connectedComponentIn hx⟩
  have hopen : IsOpen (connectedComponentIn U x) := hU.connectedComponentIn
  obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hopen hnon
  exact ⟨q, hq, (connectedComponentIn_eq hq).symm⟩

/-! ## Component partitions and the component cover -/




/-- **Rational-code cover.**  The rational curve codes of the minimal-arc
transport: if a rational code map selects, for every active point `r`, a
rational number in the component of `r`, then the components of the rational
codes cover the active set.  No enumeration of the components is needed: the
index set is `ℚ` itself, which is exactly what the minimal-arc transport
provides. -/
theorem exists_component_cover_of_rational_codes {U : Set ℝ} (hU : IsOpen U)
    (c : ℝ → ℚ) (hc : ∀ r : ℝ, r ∈ U → (c r : ℝ) ∈ connectedComponentIn U r) :
    ∃ comp : ℚ → Set ℝ,
      (∀ q : ℚ, comp q = ∅ ∨ ∃ x : ℝ, x ∈ U ∧
        comp q = connectedComponentIn U x) ∧
      (∀ r : ℝ, r ∈ U → ∃ q : ℚ, r ∈ comp q) := by
  classical
  let comp : ℚ → Set ℝ :=
    fun q => if (q : ℝ) ∈ U then connectedComponentIn U (q : ℝ) else ∅
  have hcomp_pos : ∀ q : ℚ, (q : ℝ) ∈ U →
      comp q = connectedComponentIn U (q : ℝ) := by
    intro q hq
    simp only [comp]
    rw [if_pos hq]
  refine ⟨comp, fun q => ?_, fun r hr => ?_⟩
  · by_cases hq : (q : ℝ) ∈ U
    · exact Or.inr ⟨(q : ℝ), hq, hcomp_pos q hq⟩
    · refine Or.inl ?_
      simp only [comp]
      rw [if_neg hq]
  · refine ⟨c r, ?_⟩
    have hqU : ((c r : ℚ) : ℝ) ∈ U :=
      connectedComponentIn_subset U r (hc r hr)
    rw [hcomp_pos (c r) hqU]
    rw [← connectedComponentIn_eq (hc r hr)]
    exact mem_connectedComponentIn hr

/-! ## Geometric reading of the active blocks -/





end OTSelector.Reconstruction
end
end
