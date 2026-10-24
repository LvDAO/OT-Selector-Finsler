import OTSelector.PointProcess.LocalConfigurationMeasurable

/-!
## Lemma skeleton

* **Conditions:** X is metric; base is an arbitrary shell origin; the input is any finite labeled tuple Fin n -> X, including n=0. The measure identity only additionally needs a measurable space. Constructor measurability additionally requires the Borel standard-Borel assumptions. The nonzero-multiplicity characterization needs BorelSpace X and permits repeated tuple locations.
* **Objects:** ofTuple base points: one shell multiset formed by inserting every original tuple point into its unique shell; countingMeasure ofTuple: the actual finite sum of original Dirac masses, with all repeated atoms; multiplicity: the retained count at an arbitrary point x
* **Proof detail:** For each shell sum the singleton multiset of each tuple point whose shell index is that shell. Evaluate the shell/counting measure and exchange the finite index sum with the countable shell sum; each tuple label contributes in exactly one shell. Use measurable_iff_countingMeasure_comp and measurability of the finite Dirac sum to prove constructor measurability. Evaluate singleton masses and use nonnegative finite-sum zero criteria for the nonzero-multiplicity equivalence.

## Mathematical sources

* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.1, pp. 9–10, equations (2.1)–(2.2); multiplicities explicitly allowed on p. 10.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22
* Günter Last; Mathew Penrose, *Lectures on the Poisson Process (author version, 21 August 2017)*, Section 2.1, pp. 10–11, evaluation-generated counting-measure sigma-algebra and Definition 2.1; Section 2.4, Proposition 2.14 proof, pp. 17–18.
  https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=22
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 424B(b)–(d), 424C–424D, pp. 30–31; Section 424G, p. 31.
  https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=30

**Relationship to the sources:** This is the exact finite-tuple-to-shell-code adapter to the Dirac-sum principle. Repeated locations are retained; neither simplicity nor an iid/Poisson distribution is assumed.
-/

/-!
# Original finite arrays as integer configurations

The shell encoding preserves every original target label and multiplicity. Its
counting measure is exactly the finite sum of original Dirac measures, and the
constructor is measurable across shell boundaries.
-/

open MeasureTheory Set Function
open scoped BigOperators Classical ENNReal

namespace OTSelector.PointProcess
namespace LocalConfiguration

variable {X : Type*} [MetricSpace X] {base : X}

/-- A finite labeled array encoded by its shell multisets, retaining repeated points. -/
noncomputable def ofTuple {n : ℕ} (base : X) (points : Fin n → X) :
    LocalConfiguration base :=
  fun k ↦ ∑ i, if h : shellIndex base (points i) = k then {⟨points i, h⟩} else 0

private theorem sum_map_finset {Y Z : Type*} [AddCommMonoid Z] {ι : Type*}
    (s : Finset ι) (m : ι → Multiset Y) (f : Y → Z) :
    ((∑ i ∈ s, m i).map f).sum = ∑ i ∈ s, ((m i).map f).sum := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih, Multiset.map_add]

/-- Encoding a finite tuple gives exactly its finite atomic measure. -/
@[simp]
theorem countingMeasure_ofTuple [MeasurableSpace X] {n : ℕ} (points : Fin n → X) :
    countingMeasure (ofTuple base points) = ∑ i, Measure.dirac (points i) := by
  ext s hs
  rw [countingMeasure_apply _ hs, Measure.finsetSum_apply]
  have hshell (k : ℕ) :
      shellMeasure (ofTuple base points) k s =
        ∑ i, if shellIndex base (points i) = k then
          s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (points i) else 0 := by
    rw [shellMeasure_apply _ _ hs]
    simp only [ofTuple, sum_map_finset]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  simp_rw [hshell]
  rw [Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [tsum_eq_single (shellIndex base (points i))]
  · rw [ite_eq_left rfl, Measure.dirac_apply' _ hs]
    rfl
  · intro k hk
    simp [Ne.symm hk]

/-- The finite tuple constructor is measurable, including at shell boundaries. -/
@[fun_prop]
theorem measurable_ofTuple [MeasurableSpace X] [BorelSpace X] [StandardBorelSpace X]
    (base : X) (n : ℕ) : Measurable (ofTuple (n := n) base) := by
  apply measurable_iff_countingMeasure_comp.mpr
  simp_rw [countingMeasure_ofTuple]
  exact Finset.measurable_sum _ fun i _ ↦
    Measure.measurable_dirac.comp (measurable_pi_apply i)

section Borel

variable [MeasurableSpace X] [BorelSpace X]

/-- Nonzero multiplicity in an actual finite tuple means that one of its labels is present. -/
theorem multiplicity_ofTuple_ne_zero_iff {n : ℕ} (points : Fin n → X) (x : X) :
    multiplicity (ofTuple base points) x ≠ 0 ↔ ∃ i, points i = x := by
  have heq := countingMeasure_singleton (ofTuple base points) x
  rw [countingMeasure_ofTuple, MeasureTheory.Measure.finsetSum_apply] at heq
  have hz : (multiplicity (ofTuple base points) x : ℝ≥0∞) = 0 ↔
      ∀ i, points i ≠ x := by
    rw [← heq]
    rw [Finset.sum_eq_zero_iff]
    simp only [Finset.mem_univ, forall_const]
    apply forall_congr'
    intro i
    by_cases hi : points i = x <;>
      simp [MeasureTheory.Measure.dirac_apply', hi]
  simpa only [Nat.cast_eq_zero, not_forall, not_not] using not_congr hz

end Borel
end LocalConfiguration

end OTSelector.PointProcess
