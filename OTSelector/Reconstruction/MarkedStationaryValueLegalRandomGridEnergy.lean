import OTSelector.MeasureTheory.ShiftedGridCrossing
import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalScene

/-!
# Actual random-grid crossing energy, without a third displacement moment

The original edge measure is kept fixed while the independent grid phase is
averaged. The exact crossing probability is bounded by the minimum of one and
the coordinate-displacement budget. Thus finite quadratic energy suffices for
vanishing discarded crossing energy as the grid spacing grows.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The original endpoint coordinates and the independent grid phase have a
joint measurable cell readout. -/
theorem measurable_joint_shiftedGridCells {q : ℕ} (ell : ℝ) :
    Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦ shiftedGridCells ell p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  have hm : Measurable (fun p : (Fin q → ℝ) × (Fin q → ℝ) ↦ (p.2 i - p.1 i) / ell) := by
    simpa only [Function.comp_def, Pi.sub_apply] using
      (((measurable_pi_apply i).comp (measurable_snd :
        Measurable (Prod.snd : (Fin q → ℝ) × (Fin q → ℝ) → (Fin q → ℝ)))).sub
        ((measurable_pi_apply i).comp measurable_fst)).div_const ell
  exact Int.measurable_floor.comp hm

/-- An actual edge crosses with probability at most the bounded first-order
geometric budget; source and target positions are arbitrary and unselected. -/
theorem shiftedGridPhaseLaw_crossing_le_min_norm {q : ℕ} {ell : ℝ} (hell : 0 < ell)
    (x y : Fin q → ℝ) :
    shiftedGridPhaseLaw q ell {u | shiftedGridCells ell u x ≠ shiftedGridCells ell u y} ≤
      ENNReal.ofReal (min 1 ((q : ℝ) * ‖y - x‖ / ell)) := by
  have : IsProbabilityMeasure (shiftedGridPhaseLaw q ell) := shiftedGridPhaseLaw_probability q hell
  have hs : ∑ i : Fin q, |x i - y i| ≤ (q : ℝ) * ‖y - x‖ := by
    calc
      _ ≤ ∑ _ : Fin q, ‖y - x‖ := Finset.sum_le_sum (fun i _ ↦ by
        simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] using norm_le_pi_norm (y - x) i)
      _ = _ := by simp
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
  apply le_min (show shiftedGridPhaseLaw q ell _ ≤ 1 from
    (measure_mono (subset_univ _)).trans_eq (measure_univ))
  apply (shiftedGridPhaseLaw_crossing_le hell x y).trans
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hs hell.le)

/-- Independent random-grid averaging charges the energy of the actual
original crossed edges, retaining arbitrary dependence inside the edge plan.
The weight may be any nonnegative measurable original edge readout. -/
theorem lintegral_shiftedGrid_crossing_energy_le
    (q : ℕ) {ell : ℝ} (hell : 0 < ell)
    (Γ : Measure (LegalMarkedPhysicalEdge q)) [SFinite Γ]
    (w : LegalMarkedPhysicalEdge q → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ u, ∫⁻ e, (if shiftedGridCells ell u e.1.1 ≠ shiftedGridCells ell u e.2.1
      then w e else 0) ∂Γ ∂shiftedGridPhaseLaw q ell) ≤
      ∫⁻ e, w e * ENNReal.ofReal (min 1 ((q : ℝ) * ‖e.2.1 - e.1.1‖ / ell)) ∂Γ := by
  classical
  have : IsProbabilityMeasure (shiftedGridPhaseLaw q ell) := shiftedGridPhaseLaw_probability q hell
  have hs : Measurable (fun p : (Fin q → ℝ) × LegalMarkedPhysicalEdge q ↦
      shiftedGridCells ell p.1 p.2.1.1) :=
    (measurable_joint_shiftedGridCells ell).comp (measurable_fst.prodMk measurable_snd.fst.fst)
  have ht : Measurable (fun p : (Fin q → ℝ) × LegalMarkedPhysicalEdge q ↦
      shiftedGridCells ell p.1 p.2.2.1) :=
    (measurable_joint_shiftedGridCells ell).comp (measurable_fst.prodMk measurable_snd.snd.fst)
  have hm : Measurable (fun p : (Fin q → ℝ) × LegalMarkedPhysicalEdge q ↦
      if shiftedGridCells ell p.1 p.2.1.1 ≠ shiftedGridCells ell p.1 p.2.2.1 then w p.2 else 0) :=
    (hw.comp measurable_snd).ite (measurableSet_eq_fun hs ht).compl measurable_const
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_mono
  intro e
  have he : (∫⁻ u, (if shiftedGridCells ell u e.1.1 ≠ shiftedGridCells ell u e.2.1
      then w e else 0) ∂shiftedGridPhaseLaw q ell) =
      w e * shiftedGridPhaseLaw q ell {u | shiftedGridCells ell u e.1.1 ≠ shiftedGridCells ell u e.2.1} := by
    have hrepr : (fun u ↦ if shiftedGridCells ell u e.1.1 ≠ shiftedGridCells ell u e.2.1
        then w e else 0) = {u | shiftedGridCells ell u e.1.1 ≠ shiftedGridCells ell u e.2.1}.indicator
          (fun _ ↦ w e) := by
      funext u
      by_cases h : shiftedGridCells ell u e.1.1 ≠ shiftedGridCells ell u e.2.1 <;> simp [h]
    rw [hrepr, lintegral_indicator (measurableSet_shiftedGridCells_crossing ell e.1.1 e.2.1), lintegral_const, Measure.restrict_apply_univ]
  exact he.le.trans (mul_le_mul_of_nonneg_left (shiftedGridPhaseLaw_crossing_le_min_norm hell e.1.1 e.2.1) bot_le)

end OTSelector.Reconstruction
