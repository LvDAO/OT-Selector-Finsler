import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonReserveClockSlack
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Real.Sqrt

/-!
# Finite mesh concentration on the original Poisson reserve

All counts use the unchanged original prefix.  A fixed finite mesh is chosen
before the intensity tends to infinity; no selected endpoints receive a new law.
-/
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Sum the actual original prefix counting errors over finitely many fixed clock sets. -/
def originalReserveFiniteDeviation {J : Type*} [Fintype J] (q : ℕ)
    (α : Measure ℝ) (r : ℝ≥0) (U : J → Set ℝ) (z : MarkedCloudSpace q ℝ) : ℝ :=
  ∑ j : J, |(originalReserveClockCount q (U j) z : ℝ) - (r : ℝ) * (α (U j)).toReal|

theorem originalReserveFiniteDeviation_nonneg {J : Type*} [Fintype J]
    (q : ℕ) (α : Measure ℝ) (r : ℝ≥0) (U : J → Set ℝ) (z : MarkedCloudSpace q ℝ) :
    0 ≤ originalReserveFiniteDeviation q α r U z :=
  Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- The original Poisson law supplies the finite mesh error bound directly. -/
theorem originalReserveFiniteDeviation_integrable_bound {J : Type*} [Fintype J]
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α] (r : ℝ≥0)
    (U : J → Set ℝ) (hU : ∀ j, MeasurableSet (U j)) :
    Integrable (originalReserveFiniteDeviation q α r U) (markedPoissonLaw q ℝ α r) ∧
      (∫ z, originalReserveFiniteDeviation q α r U z ∂markedPoissonLaw q ℝ α r) ≤
        (Fintype.card J : ℝ) * Real.sqrt (r : ℝ) := by
  have hj (j : J) := originalReserveClockCount_deviation_integrable_bound q α r (hU j)
  refine ⟨integrable_finsetSum _ (fun j _ ↦ (hj j).1), ?_⟩
  unfold originalReserveFiniteDeviation
  rw [integral_finsetSum _ (fun j _ ↦ (hj j).1)]
  exact (Finset.sum_le_sum (fun j _ ↦ (hj j).2)).trans_eq (by simp)

/-- A finite mesh's normalized counting error has an explicit vanishing probability bound. -/
theorem originalReserveFiniteDeviation_failure_bound {J : Type*} [Fintype J]
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α]
    (r : ℝ≥0) (hr : 0 < r) {δ : ℝ} (hδ : 0 < δ)
    (U : J → Set ℝ) (hU : ∀ j, MeasurableSet (U j)) :
    (markedPoissonLaw q ℝ α r).real
      {z | (r : ℝ) * δ ≤ originalReserveFiniteDeviation q α r U z} ≤
        (Fintype.card J : ℝ) / (δ * Real.sqrt (r : ℝ)) := by
  have hrR : 0 < (r : ℝ) := hr
  have ht : 0 < (r : ℝ) * δ := mul_pos hrR hδ
  obtain ⟨hI, hB⟩ := originalReserveFiniteDeviation_integrable_bound q α r U hU
  have hm := mul_meas_ge_le_integral_of_nonneg
    (.of_forall (originalReserveFiniteDeviation_nonneg q α r U)) hI ((r : ℝ) * δ)
  have hb : (markedPoissonLaw q ℝ α r).real
      {z | (r : ℝ) * δ ≤ originalReserveFiniteDeviation q α r U z} ≤
        ((Fintype.card J : ℝ) * Real.sqrt (r : ℝ)) / ((r : ℝ) * δ) := by
    apply (le_div_iff₀ ht).mpr
    simpa only [mul_comm] using hm.trans hB
  apply hb.trans_eq
  have hspos := Real.sqrt_pos.2 hrR
  have hs := Real.sq_sqrt hrR.le
  field_simp
  nlinarith

/-- Any increasing original volume sequence gives finite mesh concentration. -/
theorem tendsto_originalReserveFiniteDeviation_failure_zero {J : Type*} [Fintype J]
    (q : ℕ) (α : Measure ℝ) [IsProbabilityMeasure α]
    (r : ℕ → ℝ≥0) (hr : ∀ n, 0 < r n)
    (hrtop : Tendsto (fun n ↦ (r n : ℝ)) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) (U : J → Set ℝ) (hU : ∀ j, MeasurableSet (U j)) :
    Tendsto (fun n ↦ (markedPoissonLaw q ℝ α (r n)).real
      {z | (r n : ℝ) * δ ≤ originalReserveFiniteDeviation q α (r n) U z})
      atTop (𝓝 0) := by
  have hb : Tendsto (fun n ↦ (Fintype.card J : ℝ) /
      (δ * Real.sqrt (r n : ℝ))) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (Fintype.card J : ℝ) / δ)).mul
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hrtop))
    simpa only [Function.comp_def, div_eq_mul_inv, mul_inv_rev, mul_assoc,
      mul_left_comm, mul_comm, mul_zero, zero_mul] using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ ↦ ENNReal.toReal_nonneg)
    (fun n ↦ originalReserveFiniteDeviation_failure_bound q α (r n) (hr n) hδ U hU)

end OTSelector.Reconstruction
