import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Probability.CDF
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration
import OTSelector.Probability.CountConditioning
import OTSelector.Probability.NestedCDF

/-!
Conditions: An iid sample, a measurable selection region with both region and complement having nonzero probability, measurable score and a positive selected count in the tail estimate.

Objects: Patternwise iid selected score laws, conditional CDF Markov tails and their mixture over membership patterns.

Proof detail: Condition on the entire membership pattern, reindex its selected coordinates to obtain the product conditional law, apply the actual CDF expectation/Markov bound and sum the pattern mixture.

Sources: Rick Durrett, Section 2.1.2, Theorems 2.1.11–2.1.13, pp. 48–49 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56); D. H. Fremlin, Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set (https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14); Bruce K. Driver, Section 12.5, Proposition 12.32 (Reflection Principle), pp. 139–140, equation (12.11) (https://mathweb.ucsd.edu/~bdriver/280_06-07/Lecture_Notes/N25_2p.pdf#page=147); Rick Durrett, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30 (https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37).
Relation: Conditional finite-pattern consequence. Conditioning only on the count does not make the original labeled coordinates iid, and the bound remains polynomial rather than exponential DKW.
-/


/-!
# Conditional empirical CDFs inside a selected region

An iid sample conditioned only on its number of visits to a set is not iid in its original
labeling.  This module conditions on every full membership pattern, applies the one-dimensional
Kolmogorov bound to the reindexed selected coordinates, and then mixes the patternwise estimates.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace OTSelector.Probability.ConditionalNestedCDF

set_option linter.style.haveILetI false

open OTSelector.CountConditioning
open OTSelector.Probability.NestedCDF

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Applying a measurable score to the selected coordinates preserves their conditional
independence on a full membership pattern. -/
theorem score_selected_iIndep_cond_membershipPattern
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card = k) (score : Ω → ℝ) (hscore : Measurable score) :
    iIndepFun
      (fun j sample ↦ score (selectedCoordinates J hJ sample j))
      ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]) := by
  exact (selectedCoordinates_iIndep_cond_membershipPattern P A hA hA0 hAc0 J hJ).comp
    (fun _ z ↦ score z) (fun _ ↦ hscore)

/-- Every scored selected coordinate has the pushforward of the one-point conditional law. -/
theorem map_score_selectedCoordinate_cond_membershipPattern
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card = k) (score : Ω → ℝ) (hscore : Measurable score)
    (j : Fin k) :
    ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]).map
        (fun sample ↦ score (selectedCoordinates J hJ sample j)) =
      (P[|A]).map score := by
  change ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]).map
      (score ∘ fun sample ↦ selectedCoordinates J hJ sample j) = (P[|A]).map score
  rw [← Measure.map_map hscore (measurable_selectedCoordinate J hJ j),
    map_selectedCoordinate_cond_membershipPattern P A hA hA0 hAc0 J hJ j]

/-- On a nonempty full pattern, the scored selected observations satisfy the Kolmogorov Markov
tail bound under the conditional product law. -/
theorem selected_ksDist_tail_pattern
    {n k : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (J : Finset (Fin n)) (hJ : J.card = k) (hk : 0 < k)
    (score : Ω → ℝ) (hscore : Measurable score) {ε : ℝ} (hε : 0 < ε) :
    let μJ := (Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]
    let Q := (P[|A]).map score
    let X : Fin k → (Fin n → Ω) → ℝ :=
      fun j sample ↦ score (selectedCoordinates J hJ sample j)
    μJ.real {sample | ε ≤ ksDist X Q sample} ≤ 4 / (ε * Real.sqrt k) := by
  dsimp only
  letI : IsProbabilityMeasure
      ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]) :=
    cond_isProbabilityMeasure (measure_membershipPattern_ne_zero P A hA0 hAc0 J)
  letI : IsProbabilityMeasure (P[|A]) := cond_isProbabilityMeasure hA0
  letI : IsProbabilityMeasure ((P[|A]).map score) :=
    Measure.isProbabilityMeasure_map hscore.aemeasurable
  exact ksDist_tail_markov hk ((P[|A]).map score)
    (fun j sample ↦ score (selectedCoordinates J hJ sample j))
    (fun j ↦ hscore.comp (measurable_selectedCoordinate J hJ j))
    (score_selected_iIndep_cond_membershipPattern P A hA hA0 hAc0 J hJ score hscore)
    (map_score_selectedCoordinate_cond_membershipPattern P A hA hA0 hAc0 J hJ score hscore)
    hε

/-- Patternwise bad Kolmogorov event at the natural count scale.  Empty patterns contribute the
empty event, since there is no empirical CDF to estimate. -/
noncomputable def patternKSEvent
    {n : ℕ} (P : Measure Ω) (A : Set Ω) (score : Ω → ℝ) (d : ℝ)
    (J : Finset (Fin n)) : Set (Fin n → Ω) :=
  if _hJ : 0 < J.card then
    {sample | d / Real.sqrt J.card ≤
      ksDist
        (fun j : Fin J.card ↦
          fun sample' ↦ score (selectedCoordinates J rfl sample' j))
        ((P[|A]).map score) sample}
  else ∅

/-- Every nonempty pattern has the same `4 / d` upper tail after scaling the empirical CDF by the
square root of its selected count. -/
theorem cond_patternKSEvent_le
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (score : Ω → ℝ) (hscore : Measurable score) {d : ℝ} (hd : 0 < d)
    (J : Finset (Fin n)) :
    ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J])
        (patternKSEvent P A score d J) ≤ ENNReal.ofReal (4 / d) := by
  by_cases hJ : 0 < J.card
  · have hsqrt : 0 < Real.sqrt (J.card : ℝ) :=
      Real.sqrt_pos.2 (Nat.cast_pos.2 hJ)
    have hreal := selected_ksDist_tail_pattern P A hA hA0 hAc0 J rfl hJ score hscore
      (div_pos hd hsqrt)
    have hbound :
        ((Measure.pi (fun _ : Fin n ↦ P))[|membershipPattern A J]).real
            (patternKSEvent P A score d J) ≤ 4 / d := by
      rw [patternKSEvent, dite_eq_left hJ]
      calc
        _ ≤ 4 / ((d / Real.sqrt J.card) * Real.sqrt J.card) := hreal
        _ = 4 / d := by field_simp
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal hbound
  · rw [patternKSEvent, dite_eq_right hJ]
    simp

/-- Mixing the full-pattern bounds returns an unconditional iid-sample bound without asserting
that the original labels are iid after conditioning on the total count. -/
theorem measure_patternKSEvent_le
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hA0 : P A ≠ 0) (hAc0 : P Aᶜ ≠ 0)
    (score : Ω → ℝ) (hscore : Measurable score) {d : ℝ} (hd : 0 < d) :
    Measure.pi (fun _ : Fin n ↦ P)
        (patternwiseEvent A (patternKSEvent P A score d)) ≤ ENNReal.ofReal (4 / d) := by
  exact CountConditioning.measure_patternwiseEvent_le P A hA
    (patternKSEvent P A score d) (ENNReal.ofReal (4 / d))
    (cond_patternKSEvent_le P A hA hA0 hAc0 score hscore hd)

end OTSelector.Probability.ConditionalNestedCDF
