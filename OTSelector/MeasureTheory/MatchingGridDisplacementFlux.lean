import OTSelector.Finite.MatchingCellDiscrepancy
import OTSelector.Finite.PartialMatching
import OTSelector.MeasureTheory.ShiftedGridCrossing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawFluxEnergy.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawFluxEnergy`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.MatchingGridDisplacementFlux

## Lemma skeleton

* **Conditions:** A fixed finite partial matching between arbitrary point arrays, positive grid spacing and positive Young parameter.
* **Objects:** Average retained crossing count, its quadratic-energy bound and free histogram imbalance estimates.
* **Proof detail:** Sum the endpointwise uniform-phase crossing probability over actual retained edges, apply scalar Young to each coordinate displacement and compare full/free histograms edge by edge.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap44.pdf#page=6): Sections 441A (invariant measure definition) and 441J (integration under an invariant action), pp. 2 and 6; Section 443A, pp. 19–20 (Haar measurability).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=144): Section 5B, Theorem 5.28 (Tonelli), printed p. 129, PDF page 144.
- [Stephen Boyd; Lieven Vandenberghe, Convex Optimization](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108): Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94.
- [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean): Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11.

Source relation (composition): Deterministic matching followed by phase averaging; the matching may depend arbitrarily on the point arrays.
-/

/-!
# Retained-edge crossing flux from actual displacement energy

The retained matching is fixed while the auxiliary grid phase is averaged.
Its choice may depend arbitrarily on the original point arrays. The mean
crossing count is bounded by its actual total coordinate displacement divided
by the grid spacing, and hence by its quadratic displacement energy.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

variable {m n q : ℕ}

/-- The number of retained matching edges which cross a translated grid cell. -/
def retainedGridCrossings (σ : OTSelector.PartialMatching m n) (ell : ℝ)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ) (u : Fin q → ℝ) : ℝ := by
  classical
  exact ∑ e ∈ σ.edges,
    if shiftedGridCells ell u (x e.1) ≠ shiftedGridCells ell u (y e.2) then 1 else 0

/-- Total coordinate displacement on exactly the retained edges. -/
def retainedCoordinateDisplacement (σ : OTSelector.PartialMatching m n)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ) : ℝ :=
  ∑ e ∈ σ.edges, ∑ i, |x e.1 i - y e.2 i|

/-- Quadratic transverse displacement on exactly the retained edges. -/
def retainedSquaredDisplacement (σ : OTSelector.PartialMatching m n)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ) : ℝ :=
  ∑ e ∈ σ.edges, ∑ i, (x e.1 i - y e.2 i) ^ 2

theorem measurable_retainedGridCrossings (σ : OTSelector.PartialMatching m n) (ell : ℝ)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ) :
    Measurable (retainedGridCrossings σ ell x y) := by
  classical
  exact Finset.measurable_sum _ fun e _ ↦ Measurable.ite
    (measurableSet_shiftedGridCells_crossing ell (x e.1) (y e.2))
    measurable_const measurable_const

/-- No selected-endpoint distribution enters this expectation: the only
randomness averaged here is the independent uniform phase. -/
theorem integral_retainedGridCrossings_le
    (σ : OTSelector.PartialMatching m n) {ell : ℝ} (hell : 0 < ell)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ) :
    ∫ u, retainedGridCrossings σ ell x y u ∂(shiftedGridPhaseLaw q ell) ≤
      retainedCoordinateDisplacement σ x y / ell := by
  classical
  have : IsProbabilityMeasure (shiftedGridPhaseLaw q ell) :=
    shiftedGridPhaseLaw_probability q hell
  have hi (e : Fin m × Fin n) : Integrable (fun u : Fin q → ℝ ↦
      if shiftedGridCells ell u (x e.1) ≠ shiftedGridCells ell u (y e.2) then (1 : ℝ)
      else 0) (shiftedGridPhaseLaw q ell) := by
    have hm : Measurable (fun u : Fin q → ℝ ↦
        if shiftedGridCells ell u (x e.1) ≠ shiftedGridCells ell u (y e.2) then (1 : ℝ)
        else 0) := Measurable.ite
        (measurableSet_shiftedGridCells_crossing ell (x e.1) (y e.2))
        measurable_const measurable_const
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards with u
    split_ifs <;> norm_num
  unfold retainedGridCrossings retainedCoordinateDisplacement
  rw [integral_finsetSum _ (fun e _ ↦ hi e), Finset.sum_div]
  apply Finset.sum_le_sum
  intro e he
  have hmass := shiftedGridPhaseLaw_crossing_le hell (x e.1) (y e.2)
  have hδ : 0 ≤ (∑ i, |x e.1 i - y e.2 i|) / ell := by positivity
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmass
  rw [ENNReal.toReal_ofReal hδ] at hreal
  have hrepr : (fun u : Fin q → ℝ ↦
      if shiftedGridCells ell u (x e.1) ≠ shiftedGridCells ell u (y e.2) then (1 : ℝ)
      else 0) = {u | shiftedGridCells ell u (x e.1) ≠
        shiftedGridCells ell u (y e.2)}.indicator (fun _ ↦ (1 : ℝ)) := by
    funext u
    by_cases hu : shiftedGridCells ell u (x e.1) = shiftedGridCells ell u (y e.2) <;>
      simp [Set.indicator, hu]
  rw [hrepr, integral_indicator_const (μ := shiftedGridPhaseLaw q ell)
    (s := {u | shiftedGridCells ell u (x e.1) ≠ shiftedGridCells ell u (y e.2)}) 1
    (measurableSet_shiftedGridCells_crossing ell (x e.1) (y e.2))]
  simpa only [Measure.real, smul_eq_mul, mul_one] using hreal

/-- Coordinatewise Young's inequality converts the actual crossing budget to
a relative quadratic-energy term and an explicit retained-count remainder. -/
theorem retainedCoordinateDisplacement_div_le_energy
    (σ : OTSelector.PartialMatching m n) {ell η : ℝ} (hell : 0 < ell) (hη : 0 < η)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ) :
    retainedCoordinateDisplacement σ x y / ell ≤
      η * retainedSquaredDisplacement σ x y +
        (σ.card : ℝ) * q / (4 * η * ell ^ 2) := by
  classical
  have hpoint (d : ℝ) : |d| / ell ≤ η * d ^ 2 + 1 / (4 * η * ell ^ 2) := by
    have hs := sq_nonneg (2 * η * ell * |d| - 1)
    apply (sub_le_iff_le_add').mp
    apply (le_div_iff₀ (show 0 < 4 * η * ell ^ 2 by positivity)).mpr
    field_simp
    by_cases hd : 0 ≤ d
    · rw [abs_of_nonneg hd] at hs ⊢
      nlinarith
    · rw [abs_of_neg (lt_of_not_ge hd)] at hs ⊢
      nlinarith
  unfold retainedCoordinateDisplacement retainedSquaredDisplacement
  rw [Finset.sum_div]
  calc
    _ ≤ ∑ e ∈ σ.edges, ∑ i : Fin q,
        (η * (x e.1 i - y e.2 i) ^ 2 + 1 / (4 * η * ell ^ 2)) := by
      apply Finset.sum_le_sum
      intro e he
      rw [Finset.sum_div]
      exact Finset.sum_le_sum fun i _ ↦ hpoint _
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, OTSelector.PartialMatching.card]
      ring

/-- The actual grid-crossing expectation is controlled by retained kinetic
energy at every positive grid spacing and absorption parameter. -/
theorem integral_retainedGridCrossings_le_energy
    (σ : OTSelector.PartialMatching m n) {ell η : ℝ} (hell : 0 < ell) (hη : 0 < η)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ) :
    ∫ u, retainedGridCrossings σ ell x y u ∂(shiftedGridPhaseLaw q ell) ≤
      η * retainedSquaredDisplacement σ x y +
        (σ.card : ℝ) * q / (4 * η * ell ^ 2) :=
  (integral_retainedGridCrossings_le σ hell x y).trans
    (retainedCoordinateDisplacement_div_le_energy σ hell hη x y)

/-- The exact finite histogram discrepancy for selected source and target
index sets, using a finite readout of the actual translated grid. -/
def gridHistogramImbalance {C : Type*} [Fintype C] [DecidableEq C]
    (S : Finset (Fin m)) (T : Finset (Fin n)) (readout : (Fin q → ℤ) → C) (ell : ℝ)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ) (u : Fin q → ℝ) : ℝ :=
  ∑ c, |(∑ i ∈ S, if readout (shiftedGridCells ell u (x i)) = c then (1 : ℝ) else 0) -
    (∑ j ∈ T, if readout (shiftedGridCells ell u (y j)) = c then (1 : ℝ) else 0)|

/-- Arbitrary selected-orphan histograms are bounded pathwise by original
histograms and the retained matching's actual grid crossings. -/
theorem gridHistogramImbalance_free_le
    {C : Type*} [Fintype C] [DecidableEq C]
    (σ : OTSelector.PartialMatching m n) (readout : (Fin q → ℤ) → C) (ell : ℝ)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ) (u : Fin q → ℝ) :
    gridHistogramImbalance σ.freeRows σ.freeCols readout ell x y u ≤
      gridHistogramImbalance Finset.univ Finset.univ readout ell x y u +
        2 * retainedGridCrossings σ ell x y u := by
  classical
  have h := σ.sum_abs_free_cell_imbalance_le_original_add_crossings
    (fun i ↦ readout (shiftedGridCells ell u (x i)))
    (fun j ↦ readout (shiftedGridCells ell u (y j)))
  have hcross : ((σ.edges.filter fun e ↦ readout (shiftedGridCells ell u (x e.1)) ≠
      readout (shiftedGridCells ell u (y e.2))).card : ℝ) ≤
        retainedGridCrossings σ ell x y u := by
    rw [Finset.card_filter]
    push_cast
    unfold retainedGridCrossings
    apply Finset.sum_le_sum
    intro e he
    by_cases heq : shiftedGridCells ell u (x e.1) = shiftedGridCells ell u (y e.2)
    · simp [heq]
    · simp only [ite_eq_left heq]
      split_ifs <;> norm_num
  change _ ≤ gridHistogramImbalance Finset.univ Finset.univ readout ell x y u +
    2 * ((σ.edges.filter fun e ↦ readout (shiftedGridCells ell u (x e.1)) ≠
      readout (shiftedGridCells ell u (y e.2))).card : ℝ) at h
  exact h.trans (by linarith)

/-- The finite histogram is integrable for every finite phase measure; this
uses measurability of the readout and finite original sample sizes. -/
theorem integrable_gridHistogramImbalance
    {C : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace C]
    [MeasurableSingletonClass C]
    (S : Finset (Fin m)) (T : Finset (Fin n)) (readout : (Fin q → ℤ) → C)
    (hreadout : Measurable readout) (ell : ℝ)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ)
    (P : Measure (Fin q → ℝ)) [IsFiniteMeasure P] :
    Integrable (gridHistogramImbalance S T readout ell x y) P := by
  have hi (z : Fin q → ℝ) (c : C) : Integrable (fun u : Fin q → ℝ ↦
      if readout (shiftedGridCells ell u z) = c then (1 : ℝ) else 0) P := by
    have hm : Measurable (fun u : Fin q → ℝ ↦
        if readout (shiftedGridCells ell u z) = c then (1 : ℝ) else 0) :=
      Measurable.ite ((measurableSet_singleton c).preimage
        (hreadout.comp (measurable_shiftedGridCells ell z))) measurable_const measurable_const
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards with u
    split_ifs <;> norm_num
  exact integrable_finsetSum _ fun c _ ↦
    ((integrable_finsetSum S fun i _ ↦ hi (x i) c).sub
      (integrable_finsetSum T fun j _ ↦ hi (y j) c)).abs

/-- Averaging actual adaptive-orphan histograms preserves only the original
histogram expectation and an explicitly controlled retained-edge flux. -/
theorem integral_gridHistogramImbalance_free_le
    {C : Type*} [Fintype C] [DecidableEq C] [MeasurableSpace C]
    [MeasurableSingletonClass C]
    (σ : OTSelector.PartialMatching m n) (readout : (Fin q → ℤ) → C)
    (hreadout : Measurable readout) {ell : ℝ} (hell : 0 < ell)
    (x : Fin m → Fin q → ℝ) (y : Fin n → Fin q → ℝ) :
    (∫ u, gridHistogramImbalance σ.freeRows σ.freeCols readout ell x y u
      ∂(shiftedGridPhaseLaw q ell)) ≤
      (∫ u, gridHistogramImbalance Finset.univ Finset.univ readout ell x y u
        ∂(shiftedGridPhaseLaw q ell)) +
        2 * retainedCoordinateDisplacement σ x y / ell := by
  classical
  have : IsProbabilityMeasure (shiftedGridPhaseLaw q ell) :=
    shiftedGridPhaseLaw_probability q hell
  have hfree := integrable_gridHistogramImbalance σ.freeRows σ.freeCols
    readout hreadout ell x y (shiftedGridPhaseLaw q ell)
  have hfull := integrable_gridHistogramImbalance Finset.univ Finset.univ
    readout hreadout ell x y (shiftedGridPhaseLaw q ell)
  have hcross : Integrable (retainedGridCrossings σ ell x y) (shiftedGridPhaseLaw q ell) := by
    unfold retainedGridCrossings
    apply integrable_finsetSum
    intro e he
    have hm : Measurable (fun u : Fin q → ℝ ↦
        if shiftedGridCells ell u (x e.1) ≠ shiftedGridCells ell u (y e.2) then (1 : ℝ)
        else 0) := Measurable.ite
          (measurableSet_shiftedGridCells_crossing ell (x e.1) (y e.2))
          measurable_const measurable_const
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards with u
    split_ifs <;> norm_num
  have hmono := integral_mono hfree (hfull.add (hcross.const_mul 2))
    (gridHistogramImbalance_free_le σ readout ell x y)
  have hsplit : (∫ u, gridHistogramImbalance Finset.univ Finset.univ readout ell x y u +
        2 * retainedGridCrossings σ ell x y u ∂(shiftedGridPhaseLaw q ell)) =
      (∫ u, gridHistogramImbalance Finset.univ Finset.univ readout ell x y u
        ∂(shiftedGridPhaseLaw q ell)) +
      2 * (∫ u, retainedGridCrossings σ ell x y u ∂(shiftedGridPhaseLaw q ell)) := by
    rw [integral_add hfull (hcross.const_mul 2), integral_const_mul]
  change _ ≤ ∫ u, gridHistogramImbalance Finset.univ Finset.univ readout ell x y u +
    2 * retainedGridCrossings σ ell x y u ∂(shiftedGridPhaseLaw q ell) at hmono
  rw [hsplit] at hmono
  have hb := integral_retainedGridCrossings_le σ hell x y
  have hb2 := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)
  exact hmono.trans (by
    simpa only [mul_div_assoc] using add_le_add_right hb2
      (∫ u, gridHistogramImbalance Finset.univ Finset.univ readout ell x y u
        ∂(shiftedGridPhaseLaw q ell)))

end OTSelector.Reconstruction

end
end
