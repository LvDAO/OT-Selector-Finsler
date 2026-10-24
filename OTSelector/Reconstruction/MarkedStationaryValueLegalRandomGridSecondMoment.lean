import OTSelector.Reconstruction.MarkedStationaryValueLegalRandomGridEnergy
import OTSelector.Probability.BoundarySecondMomentTail

/-!
# Vanishing original crossing energy from a second moment alone

The measure of actual original edges is held fixed. Its finite second moment,
combined with the actual independent phase crossing bound, makes the entire
phase-averaged discarded quadratic energy tend to zero. No third moment or
law for adaptive unmatched endpoints is introduced.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The same original finite-second-moment edge measure loses vanishing
quadratic energy under independent grids with spacings tending to infinity. -/
theorem tendsto_lintegral_shiftedGrid_crossing_squared_energy_zero
    (q : ℕ) (Γ : Measure (LegalMarkedPhysicalEdge q)) [SFinite Γ]
    (hi : Integrable (fun e : LegalMarkedPhysicalEdge q ↦ ‖e.2.1 - e.1.1‖ ^ 2) Γ)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ u, ∫⁻ e, (if shiftedGridCells (R n) u e.1.1 ≠
        shiftedGridCells (R n) u e.2.1 then ENNReal.ofReal (‖e.2.1 - e.1.1‖ ^ 2) else 0)
      ∂Γ ∂shiftedGridPhaseLaw q (R n)) atTop (𝓝 0) := by
  have hf : Measurable (fun e : LegalMarkedPhysicalEdge q ↦ ‖e.2.1 - e.1.1‖) :=
    (measurable_snd.fst.sub measurable_fst.fst).norm
  let F (n : ℕ) (e : LegalMarkedPhysicalEdge q) : ℝ :=
    ‖e.2.1 - e.1.1‖ ^ 2 * min 1 ((q : ℝ) * ‖e.2.1 - e.1.1‖ / R n)
  have hn (n : ℕ) (e : LegalMarkedPhysicalEdge q) : 0 ≤ F n e :=
    mul_nonneg (sq_nonneg _) (le_min zero_le_one
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (hRpos n).le))
  have hFI (n : ℕ) : Integrable (F n) Γ := by
    apply hi.mono' (((hf.pow_const 2).mul (measurable_const.min
      ((measurable_const.mul hf).div_const (R n)))).aestronglyMeasurable)
    filter_upwards with e
    change |F n e| ≤ ‖e.2.1 - e.1.1‖ ^ 2
    rw [abs_of_nonneg (hn n e)]
    exact mul_le_of_le_one_right (sq_nonneg _) (min_le_left _ _)
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (∫ e, F n e ∂Γ)) atTop (𝓝 0) := by
    have h := tendsto_weighted_crossing_second_moment_zero Γ
      (fun e : LegalMarkedPhysicalEdge q ↦ ‖e.2.1 - e.1.1‖) hf hi (q : ℝ) (Nat.cast_nonneg _)
      R hRpos hR
    simpa only [F, Function.comp_def, abs_of_nonneg (norm_nonneg _), ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
  intro n
  have h := lintegral_shiftedGrid_crossing_energy_le q (hRpos n) Γ
    (fun e ↦ ENNReal.ofReal (‖e.2.1 - e.1.1‖ ^ 2)) (hf.pow_const 2).ennreal_ofReal
  apply h.trans_eq
  change _ = ENNReal.ofReal (∫ e, F n e ∂Γ)
  rw [ofReal_integral_eq_lintegral_ofReal (hFI n) (.of_forall (hn n))]
  apply lintegral_congr_ae
  filter_upwards with e
  exact (ENNReal.ofReal_mul (sq_nonneg _)).symm

end OTSelector.Reconstruction
