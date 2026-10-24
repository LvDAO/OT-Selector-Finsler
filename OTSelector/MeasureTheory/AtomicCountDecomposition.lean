import Mathlib.Data.Fintype.Card
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Real

/-!
## Lemma skeleton

* **Conditions:** An exact positive decomposition of finite sums of Dirac masses, with a finite port measure; repeated physical locations are permitted.
* **Objects:** Exact unused count equals port mass plus retained reserve count, and its finite-type-cardinality bound.
* **Proof detail:** Evaluate the measure identity on the whole space, convert finite masses to real values, and bound the retained finite-set cardinality by its ambient type cardinality.

## Mathematical sources

* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22

**Relationship to the sources:** Elementary counting-measure consequence of the Dirac-sum representation, preserving multiplicity.
-/

/-! Exact unused-label counts from the actual remaining endpoint measure. -/
open Set MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction

/-- The original remaining-measure identity determines the literal number
of unused labels. It includes coincident observations and empty arrays. -/
theorem originalUnusedCount_eq_portMass_add_keptReserveCount
    {X I J : Type*} [MeasurableSpace X] [DecidableEq I] [DecidableEq J]
    (S : Finset I) (T : Finset J) (x : I → X) (y : J → X)
    (ports : Measure X) [IsFiniteMeasure ports]
    (h : (∑ i ∈ S, Measure.dirac (x i)) = ports + ∑ j ∈ T, Measure.dirac (y j)) :
    (S.card : ℝ) = ports.real univ + T.card := by
  have hm := congrArg (fun μ : Measure X ↦ μ univ) h
  have he : (S.card : ℝ≥0∞) = ports univ + T.card := by
    simpa [Measure.finsetSum_apply] using hm
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_add (measure_ne_top ports univ) (by simp)] at hr
  simpa only [ENNReal.toReal_natCast, measureReal_def] using hr

/-- Deleting original reserves can only decrease the reserve part of the
unused-label count; the true port mass is charged without a count oracle. -/
theorem originalUnusedCount_le_portMass_add_reserveCount
    {X I J : Type*} [MeasurableSpace X] [DecidableEq I] [DecidableEq J] [Fintype J]
    (S : Finset I) (T : Finset J) (x : I → X) (y : J → X)
    (ports : Measure X) [IsFiniteMeasure ports]
    (h : (∑ i ∈ S, Measure.dirac (x i)) = ports + ∑ j ∈ T, Measure.dirac (y j)) :
    (S.card : ℝ) ≤ ports.real univ + Fintype.card J := by
  rw [originalUnusedCount_eq_portMass_add_keptReserveCount S T x y ports h]
  have hc : (T.card : ℝ) ≤ (Fintype.card J : ℝ) := by exact_mod_cast Finset.card_le_univ T
  exact add_le_add le_rfl hc

end OTSelector.Reconstruction
