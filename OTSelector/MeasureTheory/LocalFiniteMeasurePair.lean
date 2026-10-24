import Mathlib.MeasureTheory.Integral.Regular
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Semicontinuity.Basic
import OTSelector.MeasureTheory.LocalFiniteMeasure

/-!
## Lemma skeleton

* **Conditions:** Two locally finite measures on the same product measurable topological space.
* **Objects:** A Cartesian pair retaining the historical declaration name CavityLocalScene.
* **Proof detail:** Form the Cartesian product of the two measure carriers; no mathematical proof is added.

## Mathematical sources

* Olav Kallenberg, *Random Measures, Theory and Applications (Springer 2017)*, Chapter 4 opening, pp. 109–110, and Section 4.1 “Weak and vague topologies”, pp. 111–117.
  https://link.springer.com/chapter/10.1007/978-3-319-41598-7_4
* Terence Tao, *Analysis I*, Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.
  https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean

**Relationship to the sources:** This is a type alias/implementation adapter. The references explain its measure factors and ordinary Cartesian products, not this project-specific name.
-/

/-!
# Pairs of locally finite measures

A pair keeps two locally finite measures on the same product space, without
introducing a transport model. The existing declaration name remains available
for the application's two-plan scene and for generic marginal closure lemmas.
-/

namespace OTSelector.Probability

/-- Two actual locally finite measures on the same product space. -/
abbrev CavityLocalScene (X Y : Type*) [TopologicalSpace X] [MeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] :=
  LocalFiniteMeasure (X × Y) × LocalFiniteMeasure (X × Y)

end OTSelector.Probability
