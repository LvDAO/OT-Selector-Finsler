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
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.ProperSpace
import OTSelector.MeasureTheory.FiniteMultisetEncoding
import OTSelector.PointProcess.LocalConfiguration
import OTSelector.PointProcess.LocalConfigurationMultiset
import OTSelector.PointProcess.LocalConfigurationWindow

/-!
## Lemma skeleton

* **Conditions:** X is a metric measurable space for the shell Dirac sums and countingMeasure definition. BorelSpace X is additionally used for singleton multiplicities, injectivity, ball formulas and local finiteness. StandardBorelSpace X is additionally required for the measurability claims of the shell-code-to-measure maps.
* **Objects:** shellMeasure: finite sum of Dirac measures of the multiset in a single shell; countingMeasure: countable sum of all shell measures; window config N: the finite multiset of atoms in the open integer-radius ball; multiplicity config x: the natural atom count retained by the shell code
* **Proof detail:** Form the finite Dirac sum on each shell and then the countable sum of measures. Use measurable-set evaluation of finite and countable sums to compute masses. Only the unique shell containing a point contributes to its singleton mass, yielding multiset extensionality and injectivity. Only finitely many shells meet an integer ball; dominate any bounded set by such a ball. Combine measurable Dirac, multiset finite sums and countable measure sums.

## Mathematical sources

* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22
* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.4, Definition 2.11 and following integer-ball exhaustion criterion, p. 16.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=28
* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.1, pp. 10–11, evaluation-generated counting-measure sigma-algebra and Definition 2.1; Section 2.4, Proposition 2.14 proof, pp. 17–18.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31.
  https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30

**Relationship to the sources:** The sum-of-Dirac measure and multiplicities are classical. Shell decomposition, singleton injectivity, bounded-window finiteness and measurable decoding are derived representation adapters.
-/

/-!
# The actual counting measure of a local configuration

Each shell contributes the finite sum of its point Dirac measures.  Summing the shells defines
the locally finite counting measure, retaining every encoded multiplicity.  This construction
is measurable for the shell-code measurable structure and the evaluation measurable structure
on measures; it does not use a topology on the configuration space.
-/

open MeasureTheory Set Topology
open scoped BigOperators Classical ENNReal

namespace OTSelector.PointProcess.LocalConfiguration

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {base : X}

/-- The finite atomic measure contributed by one shell, with multiplicities. -/
noncomputable def shellMeasure (config : LocalConfiguration base) (n : ℕ) : Measure X :=
  ((config n).map (fun x ↦ Measure.dirac x.val)).sum

/-- The counting measure decoded from all shells, with multiplicities. -/
noncomputable def countingMeasure (config : LocalConfiguration base) : Measure X :=
  Measure.sum (shellMeasure config)

theorem countingMeasure_apply (config : LocalConfiguration base) {s : Set X}
    (hs : MeasurableSet s) :
    countingMeasure config s = ∑' n, shellMeasure config n s :=
  Measure.sum_apply _ hs

omit [MetricSpace X] in
private theorem sum_dirac_apply (m : Multiset X) {s : Set X} (hs : MeasurableSet s) :
    (m.map Measure.dirac).sum s = (m.map (s.indicator (fun _ ↦ (1 : ℝ≥0∞)))).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons x m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Measure.add_apply,
        Measure.dirac_apply' _ hs, ih]
      rfl

theorem shellMeasure_apply (config : LocalConfiguration base) (n : ℕ) {s : Set X}
    (hs : MeasurableSet s) :
    shellMeasure config n s =
      ((config n).map (fun x ↦ s.indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val)).sum := by
  have h := sum_dirac_apply ((config n).map Subtype.val) hs
  simpa only [shellMeasure, Multiset.map_map, Function.comp_def] using h

section Borel

variable [BorelSpace X]

private theorem sum_dirac_singleton (m : Multiset X) (x : X) :
    (m.map Measure.dirac).sum {x} = (m.count x : ℝ≥0∞) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons y m ih =>
      by_cases h : y = x
      · subst y
        simp [Measure.add_apply, ih, add_comm]
      · simp [Measure.add_apply, ih, h, Ne.symm h]

/-- A single shell has precisely the encoded atom mass. -/
theorem shellMeasure_singleton (config : LocalConfiguration base) (n : ℕ) (x : X) :
    shellMeasure config n {x} =
      if n = shellIndex base x then (multiplicity config x : ℝ≥0∞) else 0 := by
  have h := sum_dirac_singleton ((config n).map Subtype.val) x
  simpa only [shellMeasure, Multiset.map_map, Function.comp_def, count_shell_map, Nat.cast_ite,
    Nat.cast_zero] using h

/-- Singleton masses recover the original multiplicities exactly. -/
@[simp]
theorem countingMeasure_singleton (config : LocalConfiguration base) (x : X) :
    countingMeasure config {x} = (multiplicity config x : ℝ≥0∞) := by
  rw [countingMeasure_apply config (measurableSet_singleton x)]
  simp [shellMeasure_singleton]

/-- Decoding a configuration as a measure loses no information. -/
theorem countingMeasure_injective :
    Function.Injective (countingMeasure : LocalConfiguration base → Measure X) := by
  intro config config' h
  apply toLocallyFinsupp_injective
  ext x
  have hx := congrArg (fun μ : Measure X ↦ μ {x}) h
  simpa using hx

/-- Integer balls contain all atoms of precisely the first finitely many shells. -/
theorem shellMeasure_ball (config : LocalConfiguration base) (n N : ℕ) :
    shellMeasure config n (Metric.ball base (N : ℝ)) =
      if n < N then ((config n).card : ℝ≥0∞) else 0 := by
  rw [shellMeasure_apply config n Metric.isOpen_ball.measurableSet]
  have hmem (x : Shell base n) : x.val ∈ Metric.ball base (N : ℝ) ↔ n < N := by
    rw [Metric.mem_ball, ← shellIndex_lt_iff, x.property]
  by_cases hn : n < N
  · simp only [hn, ↓reduceIte]
    have hmap : (config n).map
        (fun x ↦ (Metric.ball base (N : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val) =
        (config n).map (fun _ ↦ (1 : ℝ≥0∞)) := by
      apply Multiset.map_congr rfl
      intro x hx
      exact Set.indicator_of_mem ((hmem x).mpr hn) _
    rw [hmap]
    simp
  · simp only [hn, ↓reduceIte]
    have hmap : (config n).map
        (fun x ↦ (Metric.ball base (N : ℝ)).indicator (fun _ ↦ (1 : ℝ≥0∞)) x.val) =
        (config n).map (fun _ ↦ (0 : ℝ≥0∞)) := by
      apply Multiset.map_congr rfl
      intro x hx
      exact Set.indicator_of_notMem (fun hx ↦ hn ((hmem x).mp hx)) _
    rw [hmap]
    simp

/-- The mass of an integer-radius ball is its finite-window point count. -/
@[simp]
theorem countingMeasure_ball (config : LocalConfiguration base) (N : ℕ) :
    countingMeasure config (Metric.ball base (N : ℝ)) = ((window config N).card : ℝ≥0∞) := by
  rw [countingMeasure_apply config Metric.isOpen_ball.measurableSet]
  rw [tsum_eq_sum (s := Finset.range N)]
  · simp only [shellMeasure_ball]
    rw [card_window, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range.mp hn, ↓reduceIte]
  · intro n hn
    simp [shellMeasure_ball, Finset.mem_range.mpr.mt hn]

/-- Every bounded observation set has finite counting mass. -/
theorem countingMeasure_lt_top_of_isBounded (config : LocalConfiguration base)
    {s : Set X} (hs : Bornology.IsBounded s) : countingMeasure config s < ∞ := by
  obtain ⟨R, hR⟩ := hs.subset_ball base
  obtain ⟨N, hN⟩ := exists_nat_gt R
  apply lt_of_le_of_lt (measure_mono (hR.trans (Metric.ball_subset_ball hN.le)))
  rw [countingMeasure_ball]
  exact ENNReal.natCast_lt_top _

/-- Local finiteness follows from the finite shell windows. -/
instance instIsLocallyFiniteMeasure (config : LocalConfiguration base) :
    IsLocallyFiniteMeasure (countingMeasure config) where
  finiteAtNhds x := by
    refine ⟨Metric.ball x 1, Metric.ball_mem_nhds x zero_lt_one, ?_⟩
    exact countingMeasure_lt_top_of_isBounded config Metric.isBounded_ball

end Borel

section Measurable

variable [BorelSpace X] [StandardBorelSpace X]

@[fun_prop]
theorem measurable_shellMeasure (n : ℕ) :
    Measurable (fun config : LocalConfiguration base ↦ shellMeasure config n) :=
  (MultisetEncoding.measurable_sum_map
    (Measure.measurable_dirac.comp measurable_subtype_coe)).comp (measurable_shell n)

/-- The actual counting measure is a measurable random-measure observable. -/
@[fun_prop]
theorem measurable_countingMeasure :
    Measurable (countingMeasure : LocalConfiguration base → Measure X) := by
  apply Measure.measurable_measure.mpr
  intro s hs
  simp_rw [countingMeasure_apply _ hs]
  exact Measurable.tsum (fun n ↦ (Measure.measurable_coe hs).comp (measurable_shellMeasure n))

end Measurable

end OTSelector.PointProcess.LocalConfiguration
