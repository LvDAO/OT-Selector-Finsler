import OTSelector.Reconstruction.FinslerRelativeLawReserveEnergyRelative
import OTSelector.MeasureTheory.ShiftedGridPeriods
import OTSelector.Probability.PoissonDyadicDiscrepancy

/-!
# One actual translated finite dyadic hierarchy

All levels use the same uniform phase in a unit cube. Integer-grid readouts
realize a genuine nested finite hierarchy. For original points in the closed
unit cube and phase in `(0,1]`, its explicit weights majorize quadratic cost.
The restriction is a coordinate normalization of a bounded physical block.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Embed an original unit cube into the translated double cube. -/
def shiftedDyadicRepairPoint {q : ℕ} (u x : Fin q → ℝ) : Fin q → ℝ :=
  fun i ↦ (x i - u i + 1) / 2

/-- A finite level of the same translated dyadic hierarchy. -/
def shiftedDyadicRepairCell (q k : ℕ) (u x : Fin q → ℝ) : Fin q → Fin (2 ^ (k + 1)) :=
  OTSelector.dyadicCell q (k + 1) (shiftedDyadicRepairPoint u x)

/-- Actual integer-grid readout for a finite dyadic level. -/
def shiftedDyadicRepairReadout (q k : ℕ) (z : Fin q → ℤ) : Fin q → Fin (2 ^ (k + 1)) :=
  fun i ↦ ⟨(z i + (2 : ℤ) ^ k).toNat % (2 ^ (k + 1)),
    Nat.mod_lt _ (by positivity)⟩

theorem shiftedDyadicRepairCell_eq_readout (q k : ℕ) (u x : Fin q → ℝ) :
    shiftedDyadicRepairCell q k u x = shiftedDyadicRepairReadout q k
      (shiftedGridCells (((2 : ℝ) ^ k)⁻¹) u x) := by
  funext i
  apply Fin.ext
  unfold shiftedDyadicRepairCell OTSelector.dyadicCell shiftedDyadicRepairPoint
    shiftedDyadicRepairReadout shiftedGridCells shiftedGridCell
  simp only
  rw [← Int.floor_toNat]
  have heq : (2 : ℝ) ^ (k + 1) * ((x i - u i + 1) / 2) =
      (x i - u i) / ((2 : ℝ) ^ k)⁻¹ + (((2 : ℤ) ^ k) : ℝ) := by
    push_cast
    rw [pow_succ]
    field_simp
  rw [heq]
  have hfloor : ⌊(x i - u i) / ((2 : ℝ) ^ k)⁻¹ + (2 : ℝ) ^ k⌋ =
      ⌊(x i - u i) / ((2 : ℝ) ^ k)⁻¹⌋ + (2 : ℤ) ^ k := by
    simpa only [Int.cast_pow, Int.cast_ofNat] using
      Int.floor_add_intCast ((x i - u i) / ((2 : ℝ) ^ k)⁻¹) ((2 : ℤ) ^ k)
  simp only [Int.cast_ofNat]
  rw [hfloor]

theorem shiftedDyadicRepairCell_nested {q k l : ℕ} (hkl : k ≤ l)
    (u x y : Fin q → ℝ)
    (h : shiftedDyadicRepairCell q l u x = shiftedDyadicRepairCell q l u y) :
    shiftedDyadicRepairCell q k u x = shiftedDyadicRepairCell q k u y :=
  OTSelector.dyadicCell_nested_global (Nat.add_le_add_right hkl 1) h

theorem measurable_shiftedDyadicRepairCell (q k : ℕ) :
    Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦ shiftedDyadicRepairCell q k p.1 p.2) := by
  apply (measurable_dyadicCell q (k + 1)).comp
  exact measurable_pi_lambda _ fun i ↦
    ((((measurable_pi_apply i).comp measurable_snd).sub
      ((measurable_pi_apply i).comp measurable_fst)).add_const 1).div_const 2

/-- The actual common phase controls each finer finite cell readout by the
corresponding grid spacing. All hierarchy levels use the same phase law. -/
theorem shiftedGridPhaseLaw_shiftedDyadicRepairCell_crossing_le
    {q : ℕ} (k : ℕ) (x y : Fin q → ℝ) :
    shiftedGridPhaseLaw q 1
      {u | shiftedDyadicRepairCell q k u x ≠ shiftedDyadicRepairCell q k u y} ≤
        ENNReal.ofReal ((∑ i, |x i - y i|) / ((2 : ℝ) ^ k)⁻¹) := by
  have hsub : {u | shiftedDyadicRepairCell q k u x ≠ shiftedDyadicRepairCell q k u y} ⊆
      {u | shiftedGridCells (((2 : ℝ) ^ k)⁻¹) u x ≠
        shiftedGridCells (((2 : ℝ) ^ k)⁻¹) u y} := by
    intro u hu heq
    exact hu (by simp only [shiftedDyadicRepairCell_eq_readout, heq])
  have h := shiftedGridPhaseLaw_crossing_nat_periods_le
    (show 0 < ((2 : ℝ) ^ k)⁻¹ by positivity)
    (show 0 < (2 ^ k : ℕ) by positivity) x y
  have hwidth : ((2 ^ k : ℕ) : ℝ) * ((2 : ℝ) ^ k)⁻¹ = 1 := by
    push_cast
    exact mul_inv_cancel₀ (by positivity)
  rw [hwidth] at h
  exact (measure_mono hsub).trans h

/-- The actual translated points lie in the half-open normalized cube whenever
the original points lie in the closed unit cube and the phase is in `(0,1]`. -/
theorem shiftedDyadicRepairPoint_mem_cube {q : ℕ} (u x : Fin q → ℝ)
    (hu : ∀ i, 0 < u i ∧ u i ≤ 1) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∀ i, 0 ≤ shiftedDyadicRepairPoint u x i ∧ shiftedDyadicRepairPoint u x i < 1 := by
  intro i
  unfold shiftedDyadicRepairPoint
  constructor <;> linarith [(hu i).1, (hu i).2, (hx i).1, (hx i).2]

/-- Concrete hierarchy weights majorize actual quadratic displacement after
normalizing any bounded block to the unit cube. -/
theorem sq_dist_le_shiftedDyadicRepair_partitionDistance
    {q K : ℕ} (u x y : Fin q → ℝ)
    (hu : ∀ i, 0 < u i ∧ u i ≤ 1)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    ∑ i, (x i - y i) ^ 2 ≤ (4 * q : ℝ) * (1 / 4 : ℝ) ^ K +
      ∑ k : Fin K, (8 * q : ℝ) * (1 / 4 : ℝ) ^ (k : ℕ) *
        partitionDistance (shiftedDyadicRepairCell q k u x) (shiftedDyadicRepairCell q k u y) := by
  have h := OTSelector.sq_dist_le_dyadic_partitionDistance (q := q) (K := K + 1)
    (by omega) (shiftedDyadicRepairPoint_mem_cube u x hu hx)
    (shiftedDyadicRepairPoint_mem_cube u y hu hy)
  have hscale : (∑ i, (x i - y i) ^ 2) =
      4 * ∑ i, (shiftedDyadicRepairPoint u x i - shiftedDyadicRepairPoint u y i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    unfold shiftedDyadicRepairPoint
    ring
  rw [hscale]
  apply (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 4)).trans_eq
  have hzero : partitionDistance (OTSelector.dyadicCell q 0 (shiftedDyadicRepairPoint u x))
      (OTSelector.dyadicCell q 0 (shiftedDyadicRepairPoint u y)) = 0 := by
    have heq : OTSelector.dyadicCell q 0 (shiftedDyadicRepairPoint u x) =
        OTSelector.dyadicCell q 0 (shiftedDyadicRepairPoint u y) := by
      funext i
      apply Fin.ext
      simp [OTSelector.dyadicCell]
    simp only [partitionDistance, ite_eq_left heq]
  rw [Finset.sum_range_succ']
  simp only [hzero, mul_zero, add_zero, pow_succ]
  rw [mul_add, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ (8 * q : ℝ) * (1 / 4 : ℝ) ^ k *
    partitionDistance (shiftedDyadicRepairCell q k u x) (shiftedDyadicRepairCell q k u y)) K]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k hk
    unfold shiftedDyadicRepairCell
    ring

end OTSelector.Reconstruction
