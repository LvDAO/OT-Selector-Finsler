import OTSelector.MeasureTheory.ShiftedGridCrossing
import OTSelector.Probability.SpatialAveraging
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.MarkedRelativeLawFluxPeriods.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.MarkedRelativeLawFluxPeriods`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ShiftedGridPeriods

## Lemma skeleton

* **Conditions:** Positive grid spacing and a positive integer number of periods; periodic bounded measurable phase observables.
* **Objects:** Identical one-period and multi-period uniform phase means and crossing probabilities, then coordinate-product crossing bounds.
* **Proof detail:** Split the long phase interval into integer translates of one fundamental interval, use periodicity and translation invariance and cancel normalization.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap44.pdf#page=6): Sections 441A (invariant measure definition) and 441J (integration under an invariant action), pp. 2 and 6; Section 443A, pp. 19–20 (Haar measurability).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14): Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set.

Source relation (composition): Elementary periodic averaging for one common commensurate phase; no independence between grid scales is imposed.
-/

/-!
# One common grid phase for finitely many commensurate scales

A uniform phase over an integer number of grid periods gives exactly the same
crossing probability as one period. This allows a single actual phase to be
used across a finite nested grid hierarchy.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- A bounded measurable periodic observable has the same actual uniform-phase
mean over any positive integer number of periods. -/
theorem integral_spatialRootLaw_nat_periods_eq
    {ell : ℝ} (hell : 0 < ell) {n : ℕ} (hn : 0 < n)
    {f : ℝ → ℝ} (hf : Measurable f) (hperiod : Function.Periodic f ell)
    {B : ℝ} (hbound : ∀ u, ‖f u‖ ≤ B) :
    (∫ u, f u ∂spatialRootLaw 0 ((n : ℝ) * ell)) =
      ∫ u, f u ∂spatialRootLaw 0 ell := by
  have hi (a b : ℝ) : IntervalIntegrable f volume a b := by
    constructor <;> exact ⟨hf.aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Filter.Eventually.of_forall hbound)⟩
  have hper := hperiod.intervalIntegral_add_zsmul_eq (n : ℤ) 0 hi
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast] at hper
  rw [integral_spatialRootLaw (by positivity : (0 : ℝ) ≤ (n : ℝ) * ell),
    integral_spatialRootLaw hell.le]
  simp only [sub_zero]
  rw [hper]
  have hnR : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- Incrementing the phase by one grid spacing shifts every integer cell label
by exactly one. -/
theorem shiftedGridCell_add_period {ell : ℝ} (hell : 0 < ell) (u x : ℝ) :
    shiftedGridCell ell (u + ell) x = shiftedGridCell ell u x - 1 := by
  unfold shiftedGridCell
  have h : (x - (u + ell)) / ell = (x - u) / ell - (1 : ℤ) := by
    push_cast
    field_simp
    ring
  rw [h, Int.floor_sub_intCast]

/-- The actual crossing mass is unchanged when the phase cell is replaced by
any positive integer number of grid periods. -/
theorem spatialRootLaw_shiftedGrid_crossing_nat_periods_eq
    {ell : ℝ} (hell : 0 < ell) {n : ℕ} (hn : 0 < n) (x y : ℝ) :
    spatialRootLaw 0 ((n : ℝ) * ell)
        {u | shiftedGridCell ell u x ≠ shiftedGridCell ell u y} =
      spatialRootLaw 0 ell {u | shiftedGridCell ell u x ≠ shiftedGridCell ell u y} := by
  classical
  let S := {u | shiftedGridCell ell u x ≠ shiftedGridCell ell u y}
  let f := S.indicator (fun _ ↦ (1 : ℝ))
  have hm : Measurable f := measurable_const.indicator (measurableSet_shiftedGridCrossing ell x y)
  have hper : Function.Periodic f ell := by
    intro u
    simp [f, S, Set.indicator, shiftedGridCell_add_period hell]
  have hb (u : ℝ) : ‖f u‖ ≤ 1 := by
    dsimp only [f]
    by_cases hu : u ∈ S <;> simp [hu]
  have heq := integral_spatialRootLaw_nat_periods_eq hell hn hm hper hb
  rw [integral_indicator_const (μ := spatialRootLaw 0 ((n : ℝ) * ell)) 1
      (measurableSet_shiftedGridCrossing ell x y),
    integral_indicator_const (μ := spatialRootLaw 0 ell) 1
      (measurableSet_shiftedGridCrossing ell x y)] at heq
  simp only [Measure.real, smul_eq_mul, mul_one] at heq
  have : IsProbabilityMeasure (spatialRootLaw 0 ((n : ℝ) * ell)) :=
    spatialRootLaw_isProbability (by positivity)
  have : IsProbabilityMeasure (spatialRootLaw 0 ell) := spatialRootLaw_isProbability hell
  apply le_antisymm
  · exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp heq.le
  · exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp heq.ge

/-- Actual crossing probability on any commensurate larger uniform phase cell. -/
theorem spatialRootLaw_shiftedGrid_crossing_nat_periods_le
    {ell : ℝ} (hell : 0 < ell) {n : ℕ} (hn : 0 < n) (x y : ℝ) :
    spatialRootLaw 0 ((n : ℝ) * ell)
      {u | shiftedGridCell ell u x ≠ shiftedGridCell ell u y} ≤
        ENNReal.ofReal (|x - y| / ell) := by
  rw [spatialRootLaw_shiftedGrid_crossing_nat_periods_eq hell hn]
  exact spatialRootLaw_shiftedGrid_crossing_le hell x y

/-- One independent common phase per coordinate controls every finer scale
whose spacing divides the phase window by a positive integer. -/
theorem shiftedGridPhaseLaw_crossing_nat_periods_le
    {q : ℕ} {ell : ℝ} (hell : 0 < ell) {n : ℕ} (hn : 0 < n)
    (x y : Fin q → ℝ) :
    shiftedGridPhaseLaw q ((n : ℝ) * ell)
      {u | shiftedGridCells ell u x ≠ shiftedGridCells ell u y} ≤
        ENNReal.ofReal ((∑ i, |x i - y i|) / ell) := by
  have hW : 0 < (n : ℝ) * ell := by positivity
  have : IsProbabilityMeasure (spatialRootLaw 0 ((n : ℝ) * ell)) :=
    spatialRootLaw_isProbability hW
  have hsub : {u | shiftedGridCells ell u x ≠ shiftedGridCells ell u y} ⊆
      ⋃ i : Fin q, {u | shiftedGridCell ell (u i) (x i) ≠ shiftedGridCell ell (u i) (y i)} := by
    intro u hu
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    by_contra h
    push Not at h
    exact hu (funext h)
  calc
    _ ≤ ∑ i : Fin q, shiftedGridPhaseLaw q ((n : ℝ) * ell)
        {u | shiftedGridCell ell (u i) (x i) ≠ shiftedGridCell ell (u i) (y i)} :=
      (measure_mono hsub).trans (measure_iUnion_fintype_le _ _)
    _ = ∑ i : Fin q, spatialRootLaw 0 ((n : ℝ) * ell)
        {u | shiftedGridCell ell u (x i) ≠ shiftedGridCell ell u (y i)} := by
      apply Finset.sum_congr rfl
      intro i hi
      have heval : (shiftedGridPhaseLaw q ((n : ℝ) * ell)).map (Function.eval i) =
          spatialRootLaw 0 ((n : ℝ) * ell) := by
        unfold shiftedGridPhaseLaw
        rw [Measure.pi_map_eval]
        simp
      rw [← heval, Measure.map_apply (measurable_pi_apply i)
        (measurableSet_shiftedGridCrossing ell (x i) (y i))]
      rfl
    _ ≤ ∑ i : Fin q, ENNReal.ofReal (|x i - y i| / ell) :=
      Finset.sum_le_sum fun i _ ↦ spatialRootLaw_shiftedGrid_crossing_nat_periods_le hell hn _ _
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ by positivity), Finset.sum_div]

end OTSelector.Probability

end
end
