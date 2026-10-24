import OTSelector.PointProcess.LocalConfigurationTuple
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Multiset.Sort
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
## Lemma skeleton

* **Conditions:** An arbitrary finite index type or finite subset of observations.
* **Objects:** A finite Dirac-sum local configuration retaining repeated observations.
* **Proof detail:** Reindex the finite tuple and verify the same counting measure in each local shell.

## Mathematical sources

* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22

**Relationship to the sources:** The finite Dirac-sum and multiplicities are classical; LocalConfiguration shell packaging is the project representation, not a theorem attributed to the book.
-/

/-! # Finite atomic measures as configurations

The shell configuration retains repeated locations. These adapters extend the
existing `Fin n` tuple constructor to any finite index type and to finite sets.

## Mathematical source

Günter Last and Mathew Penrose, *Lectures on the Poisson Process*, §2.1, pp. 9–10,
equations (2.1) and (2.2): a counting measure is a sum of Dirac masses and its
integral is the corresponding sum. Page 10 explicitly permits repeated points
and their multiplicities. Author version (21 August 2017):
https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22 .
The shell representation and finite-index conversion are Lean adapters for that
counting-measure principle, using `LocalConfiguration.ofTuple`.

-/

open MeasureTheory
open scoped BigOperators

namespace OTSelector.PointProcess

/-- Any finite labeled atomic measure has a shell configuration with the same multiplicities. -/
theorem exists_configuration_sum_dirac {X I : Type*} [MetricSpace X]
    [MeasurableSpace X] [Fintype I] (base : X) (f : I → X) :
    ∃ c : PointProcess.LocalConfiguration base,
      PointProcess.LocalConfiguration.countingMeasure c = ∑ i, Measure.dirac (f i) := by
  classical
  let e := (Fintype.equivFin I).symm
  refine ⟨PointProcess.LocalConfiguration.ofTuple base (fun i ↦ f (e i)), ?_⟩
  rw [PointProcess.LocalConfiguration.countingMeasure_ofTuple]
  exact e.sum_comp (fun i ↦ Measure.dirac (f i))

/-- A finite-set-indexed Dirac sum is represented without removing repeated locations. -/
theorem exists_configuration_finset_dirac {X I : Type*} [MetricSpace X]
    [MeasurableSpace X] (base : X) (s : Finset I) (f : I → X) :
    ∃ c : PointProcess.LocalConfiguration base,
      PointProcess.LocalConfiguration.countingMeasure c = ∑ i ∈ s, Measure.dirac (f i) := by
  classical
  obtain ⟨c, hc⟩ := exists_configuration_sum_dirac base (fun i : s ↦ f i)
  refine ⟨c, hc.trans ?_⟩
  exact Finset.sum_coe_sort s (fun i ↦ Measure.dirac (f i))

end OTSelector.PointProcess
