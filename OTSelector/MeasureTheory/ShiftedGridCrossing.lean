import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import OTSelector.Probability.SpatialAveraging
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.MarkedRelativeLawFluxGrid.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.MarkedRelativeLawFluxGrid`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.ShiftedGridCrossing

## Lemma skeleton

* **Conditions:** Positive grid spacing, real endpoints and the uniform phase on one fundamental interval, then its finite coordinate product.
* **Objects:** Exact average lattice-boundary count and crossing/readout crossing probability at most coordinate l1 displacement divided by spacing.
* **Proof detail:** Unfold the translated lattice fundamental-domain integral, bound different-cell incidence by a boundary between the endpoints, normalize, and use the finite coordinate union bound.

## Mathematical sources

- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap44.pdf#page=6): Sections 441A (invariant measure definition) and 441J (integration under an invariant action), pp. 2 and 6; Section 443A, pp. 19–20 (Haar measurability).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=14): Section 251W(g)–(h), pp. 14–15: finite product measures, sigma-finiteness and regrouping by a partition of the coordinate set.

Source relation (composition): Explicit shifted-grid averaging; it applies to arbitrary endpoint pairs and does not add independence from a selected matching.
-/

/-!
# Crossing budgets for an actual uniformly translated grid

Two real points lie in different grid cells only if a lattice boundary lies
between them. Averaging the boundary count over one fundamental phase interval
gives the displacement divided by the grid spacing. This argument applies to
each retained edge of an arbitrarily selected matching.
-/

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

/-- Integer label of the cell in the grid with spacing `ell` and phase `u`. -/
def shiftedGridCell (ell u x : ℝ) : ℤ := ⌊(x - u) / ell⌋

theorem measurable_shiftedGridCell (ell x : ℝ) :
    Measurable (fun u ↦ shiftedGridCell ell u x) :=
  Int.measurable_floor.comp ((measurable_const.sub measurable_id).div_const ell)

theorem measurableSet_shiftedGridCrossing (ell x y : ℝ) :
    MeasurableSet {u | shiftedGridCell ell u x ≠ shiftedGridCell ell u y} :=
  (measurableSet_eq_fun (measurable_shiftedGridCell ell x)
    (measurable_shiftedGridCell ell y)).compl

/-- Averaging the complete lattice-boundary count over one actual phase cell
counts each point of an interval once. -/
theorem lintegral_shiftedGrid_boundary_count {ell : ℝ} (hell : 0 < ell) (x y : ℝ) :
    (∫⁻ u in Ioc 0 ell, ∑' g : AddSubgroup.zmultiples ell,
      (Ioc x y).indicator (fun _ ↦ (1 : ℝ≥0∞)) ((g : ℝ) + u)) =
        ENNReal.ofReal (y - x) := by
  let W := (Ioc x y).indicator (fun _ ↦ (1 : ℝ≥0∞))
  have hW : Measurable W := measurable_const.indicator measurableSet_Ioc
  have hfd := isAddFundamentalDomain_Ioc hell (0 : ℝ) volume
  calc
    _ = ∑' g : AddSubgroup.zmultiples ell, ∫⁻ u in Ioc 0 ell, W ((g : ℝ) + u) :=
      lintegral_tsum (fun g ↦
        (hW.comp (measurable_const.add measurable_id)).aemeasurable)
    _ = ∫⁻ u, W u := by
      simpa only [zero_add, AddSubgroup.vadd_def, vadd_eq_add] using
        (hfd.lintegral_eq_tsum'' W).symm
    _ = _ := by simp [W]

/-- The actual phase measure of grid-cell disagreement is at most the distance
between the points; the phase interval has length `ell`. -/
theorem volume_shiftedGrid_crossing_le {ell : ℝ} (hell : 0 < ell) (x y : ℝ) :
    volume.restrict (Ioc 0 ell)
      {u | shiftedGridCell ell u x ≠ shiftedGridCell ell u y} ≤
        ENNReal.ofReal |x - y| := by
  classical
  wlog hxy : x ≤ y generalizing x y
  · simpa only [ne_comm, abs_sub_comm] using this y x (le_of_not_ge hxy)
  have hdom (u : ℝ) :
      {v | shiftedGridCell ell v x ≠ shiftedGridCell ell v y}.indicator
        (fun _ ↦ (1 : ℝ≥0∞)) u ≤
      ∑' g : AddSubgroup.zmultiples ell,
        (Ioc x y).indicator (fun _ ↦ (1 : ℝ≥0∞)) ((g : ℝ) + u) := by
    by_cases hu : shiftedGridCell ell u x = shiftedGridCell ell u y
    · have hnot : u ∉ {v | shiftedGridCell ell v x ≠ shiftedGridCell ell v y} :=
        fun h ↦ h hu
      rw [Set.indicator_of_notMem hnot]
      exact zero_le
    · let k : ℤ := ⌊(x - u) / ell⌋ + 1
      have hle : ⌊(x - u) / ell⌋ ≤ ⌊(y - u) / ell⌋ :=
        Int.floor_mono (div_le_div_of_nonneg_right (sub_le_sub_right hxy u) hell.le)
      have hk : k ≤ ⌊(y - u) / ell⌋ := by
        dsimp only [shiftedGridCell] at hu
        dsimp only [k]
        omega
      have hx : x - u < (k : ℝ) * ell := by
        apply (div_lt_iff₀ hell).mp
        simpa only [k, Int.cast_add, Int.cast_one] using Int.lt_floor_add_one ((x - u) / ell)
      have hy : (k : ℝ) * ell ≤ y - u :=
        (le_div_iff₀ hell).mp (Int.le_floor.mp hk)
      let g : AddSubgroup.zmultiples ell :=
        ⟨k • ell, AddSubgroup.zsmul_mem_zmultiples ell k⟩
      have hmem : (g : ℝ) + u ∈ Ioc x y := by
        change x < k • ell + u ∧ k • ell + u ≤ y
        simp only [zsmul_eq_mul]
        constructor <;> linarith
      rw [Set.indicator_of_mem (show u ∈ {v | shiftedGridCell ell v x ≠
        shiftedGridCell ell v y} from hu)]
      exact (by simp [hmem] :
        (1 : ℝ≥0∞) ≤ (Ioc x y).indicator (fun _ ↦ (1 : ℝ≥0∞)) ((g : ℝ) + u)).trans
          (ENNReal.le_tsum g)
  have hi := lintegral_mono (μ := volume.restrict (Ioc 0 ell)) hdom
  rw [lintegral_indicator (measurableSet_shiftedGridCrossing ell x y),
    lintegral_const, Measure.restrict_apply_univ, one_mul,
    lintegral_shiftedGrid_boundary_count hell x y] at hi
  simpa only [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)] using hi

/-- Crossing probability under the actual independent uniform grid phase. -/
theorem spatialRootLaw_shiftedGrid_crossing_le {ell : ℝ} (hell : 0 < ell) (x y : ℝ) :
    spatialRootLaw 0 ell {u | shiftedGridCell ell u x ≠ shiftedGridCell ell u y} ≤
      ENNReal.ofReal (|x - y| / ell) := by
  rw [spatialRootLaw, cond_apply measurableSet_Ioc, Real.volume_Ioc, sub_zero]
  have hm := volume_shiftedGrid_crossing_le hell x y
  rw [Measure.restrict_apply (measurableSet_shiftedGridCrossing ell x y), Set.inter_comm] at hm
  have hmul := mul_le_mul_right hm (ENNReal.ofReal ell)⁻¹
  rw [ENNReal.ofReal_div_of_pos hell, div_eq_mul_inv]
  exact hmul.trans_eq (mul_comm _ _)

/-- An independent uniform grid phase in each transverse coordinate. -/
def shiftedGridPhaseLaw (q : ℕ) (ell : ℝ) : Measure (Fin q → ℝ) :=
  Measure.pi fun _ : Fin q ↦ spatialRootLaw 0 ell

theorem shiftedGridPhaseLaw_probability (q : ℕ) {ell : ℝ} (hell : 0 < ell) :
    IsProbabilityMeasure (shiftedGridPhaseLaw q ell) := by
  have : IsProbabilityMeasure (spatialRootLaw 0 ell) := spatialRootLaw_isProbability hell
  dsimp only [shiftedGridPhaseLaw]
  infer_instance

/-- The full coordinate label of the translated cubic grid. -/
def shiftedGridCells {q : ℕ} (ell : ℝ) (u x : Fin q → ℝ) : Fin q → ℤ :=
  fun i ↦ shiftedGridCell ell (u i) (x i)

theorem measurable_shiftedGridCells {q : ℕ} (ell : ℝ) (x : Fin q → ℝ) :
    Measurable (fun u ↦ shiftedGridCells ell u x) :=
  measurable_pi_lambda _ fun i ↦ (measurable_shiftedGridCell ell (x i)).comp
    (measurable_pi_apply i)

theorem measurableSet_shiftedGridCells_crossing {q : ℕ} (ell : ℝ)
    (x y : Fin q → ℝ) :
    MeasurableSet {u | shiftedGridCells ell u x ≠ shiftedGridCells ell u y} :=
  (measurableSet_eq_fun (measurable_shiftedGridCells ell x)
    (measurable_shiftedGridCells ell y)).compl

/-- The actual cubic-grid crossing probability is bounded by the sum of the
coordinate displacements divided by the grid spacing. -/
theorem shiftedGridPhaseLaw_crossing_le {q : ℕ} {ell : ℝ} (hell : 0 < ell)
    (x y : Fin q → ℝ) :
    shiftedGridPhaseLaw q ell {u | shiftedGridCells ell u x ≠ shiftedGridCells ell u y} ≤
      ENNReal.ofReal ((∑ i, |x i - y i|) / ell) := by
  classical
  have : IsProbabilityMeasure (spatialRootLaw 0 ell) := spatialRootLaw_isProbability hell
  let A : Fin q → Set (Fin q → ℝ) :=
    fun i ↦ {u | shiftedGridCell ell (u i) (x i) ≠ shiftedGridCell ell (u i) (y i)}
  have hcover : {u | shiftedGridCells ell u x ≠ shiftedGridCells ell u y} = ⋃ i, A i := by
    ext u
    simp only [Set.mem_iUnion]
    change shiftedGridCells ell u x ≠ shiftedGridCells ell u y ↔
      ∃ i, shiftedGridCell ell (u i) (x i) ≠ shiftedGridCell ell (u i) (y i)
    constructor
    · intro h
      by_contra hn
      apply h
      funext i
      by_contra hi
      exact hn ⟨i, hi⟩
    · rintro ⟨i, hi⟩ h
      exact hi (congrFun h i)
  have hcoord (i : Fin q) : shiftedGridPhaseLaw q ell (A i) ≤
      ENNReal.ofReal (|x i - y i| / ell) := by
    have hmap : (shiftedGridPhaseLaw q ell).map (Function.eval i) =
        spatialRootLaw 0 ell := by
      dsimp only [shiftedGridPhaseLaw]
      rw [Measure.pi_map_eval]
      simp
    have h := spatialRootLaw_shiftedGrid_crossing_le hell (x i) (y i)
    rw [← hmap, Measure.map_apply (measurable_pi_apply i)
      (measurableSet_shiftedGridCrossing ell (x i) (y i))] at h
    exact h
  rw [hcover]
  calc shiftedGridPhaseLaw q ell (⋃ i, A i)
      ≤ ∑ i, shiftedGridPhaseLaw q ell (A i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i, ENNReal.ofReal (|x i - y i| / ell) := Finset.sum_le_sum fun i _ ↦ hcoord i
    _ = _ := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ div_nonneg (abs_nonneg _) hell.le),
        ← Finset.sum_div]

/-- Any deterministic finite cell readout inherits the same crossing budget.
This permits bounded-cell versions of the grid without an exact cube-law
hypothesis for either population. -/
theorem shiftedGridPhaseLaw_readout_crossing_le {q : ℕ} {ell : ℝ} (hell : 0 < ell)
    {C : Type*} (readout : (Fin q → ℤ) → C) (x y : Fin q → ℝ) :
    shiftedGridPhaseLaw q ell
      {u | readout (shiftedGridCells ell u x) ≠ readout (shiftedGridCells ell u y)} ≤
      ENNReal.ofReal ((∑ i, |x i - y i|) / ell) := by
  apply (measure_mono ?_).trans (shiftedGridPhaseLaw_crossing_le hell x y)
  intro u hu hxy
  exact hu (congrArg readout hxy)

end OTSelector.Probability

end
end
