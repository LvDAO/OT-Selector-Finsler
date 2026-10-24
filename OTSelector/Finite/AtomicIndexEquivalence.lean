import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Finite.AtomicIndexEquivalence

## Lemma skeleton

* **Conditions:** Finite indexed atom families whose sums of Dirac measures agree; singletons are measurable. Subsequent pullbacks have an explicit value-preserving index equivalence.

* **Objects:** An atom-value-preserving index bijection, and preservation of sums, conditional masses and quadratic integral costs under it.

* **Proof detail:** Evaluate the equal counting measures on each singleton to match multiplicities, build equivalences on equal-value fibers, and combine them. Reindex every later finite sum through that same equivalence.

## Mathematical sources

- [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22): Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (corollary): Local multiplicity-preserving reindexing, without assuming that repeated observations have distinct values.
-/

/-! Relabel counted original observations without assuming that their values are distinct. -/

open MeasureTheory
open scoped ENNReal BigOperators Classical

noncomputable section
namespace OTSelector.Reconstruction

/-- Equality of finite counting measures gives a genuine value-preserving
equivalence of the original labels, including repeated values and empty arrays. -/
theorem exists_originalIndexEquiv_of_sum_dirac_eq
    {X I J : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [Fintype I] [Fintype J]
    (x : I → X) (y : J → X) (h : (∑ i, Measure.dirac (x i)) = ∑ j, Measure.dirac (y j)) :
    ∃ e : I ≃ J, ∀ i, x i = y (e i) := by
  classical
  have hc (a : X) : Fintype.card {i // x i = a} = Fintype.card {j // y j = a} := by
    have ha := congrArg (fun μ : Measure X ↦ μ {a}) h
    have ha' : (Fintype.card {i // x i = a} : ℝ≥0∞) = Fintype.card {j // y j = a} := by
      simpa [Measure.finsetSum_apply, Set.indicator_apply, Fintype.card_subtype] using ha
    exact_mod_cast ha'
  let ef := fun a ↦ Fintype.equivOfCardEq (hc a)
  exact ⟨Equiv.ofFiberEquiv ef, fun i ↦ (Equiv.ofFiberEquiv_map ef i).symm⟩

/-- Every additive quantity attached to the unchanged point and its new label
has exactly the same total after reindexing. -/
theorem originalIndexEquiv_sum_pullback
    {X I J A : Type*} [Fintype I] [Fintype J] [AddCommMonoid A]
    (x : I → X) (y : J → X) (e : I ≃ J) (he : ∀ i, x i = y (e i))
    (F : X → J → A) : (∑ i, F (x i) (e i)) = ∑ j, F (y j) j :=
  Fintype.sum_equiv e _ _ fun i ↦ by rw [he i]

/-- Pulling population laws back to the original marked labels preserves
probability, total mass, actual endpoint energy, each clock-class measure sum,
and all individual deviation integrability statements. -/
theorem originalAtomFamily_pullback_spec
    {X E I J : Type*} [Fintype I] [Fintype J] [PseudoMetricSpace E] [MeasurableSpace E]
    (x : I → X) (y : J → X) (e : I ≃ J) (he : ∀ i, x i = y (e i))
    (position : X → E) (clock : X → ℝ) (κ : J → Measure E)
    (hκ : ∀ j, IsProbabilityMeasure (κ j)) :
    (∀ i, IsProbabilityMeasure (κ (e i))) ∧
      (∑ i, κ (e i)) = ∑ j, κ j ∧
      (∑ i, ∫ v, dist (position (x i)) v ^ 2 ∂κ (e i)) =
        ∑ j, ∫ v, dist (position (y j)) v ^ 2 ∂κ j ∧
      (∀ C : Set ℝ, (∑ i, if clock (x i) ∈ C then κ (e i) else 0) =
        ∑ j, if clock (y j) ∈ C then κ j else 0) ∧
      ((∀ i, Integrable (fun v ↦ dist (position (x i)) v ^ 2) (κ (e i))) ↔
        ∀ j, Integrable (fun v ↦ dist (position (y j)) v ^ 2) (κ j)) := by
  classical
  refine ⟨fun i ↦ hκ (e i), e.sum_comp κ,
    originalIndexEquiv_sum_pullback x y e he (fun a j ↦ ∫ v, dist (position a) v ^ 2 ∂κ j),
    fun C ↦ originalIndexEquiv_sum_pullback x y e he
      (fun a j ↦ if clock a ∈ C then κ j else 0), ?_⟩
  simp_rw [he]
  exact e.forall_congr_right (q := fun j ↦ Integrable (fun v ↦ dist (position (y j)) v ^ 2) (κ j))

end OTSelector.Reconstruction
