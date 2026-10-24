import OTSelector.Reconstruction.MarkedStationaryValueLegalRandomGridEnergy
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryGridEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Vanishing original grid-cut energy for every integrable weight

The actual original mean edge measure is held fixed. Independent grid phases
lose vanishing mass of every integrable original weight, even when weighted
kinetic energy does not control the unweighted displacement second moment.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalStationaryWeightedGridTailInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalStationaryWeightedGridTailPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- A fixed actual edge measure loses vanishing integrable weight under an
independent random grid. No displacement moment is required. -/
theorem tendsto_lintegral_shiftedGrid_crossing_integrable_weight_zero
    (q : ℕ) (Γ : Measure (LegalMarkedPhysicalEdge q)) [SFinite Γ]
    (w : LegalMarkedPhysicalEdge q → ℝ) (hw : Measurable w) (hi : Integrable w Γ)
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ u, ∫⁻ e,
        (if shiftedGridCells (R n) u e.1.1 ≠ shiftedGridCells (R n) u e.2.1
          then ENNReal.ofReal (w e) else 0) ∂Γ ∂shiftedGridPhaseLaw q (R n))
      atTop (𝓝 0) := by
  have hd : Measurable (fun e : LegalMarkedPhysicalEdge q ↦ ‖e.2.1 - e.1.1‖) :=
    (measurable_snd.fst.sub measurable_fst.fst).norm
  let F (n : ℕ) (e : LegalMarkedPhysicalEdge q) : ℝ :=
    max (w e) 0 * min 1 ((q : ℝ) * ‖e.2.1 - e.1.1‖ / R n)
  have hn (n : ℕ) (e : LegalMarkedPhysicalEdge q) : 0 ≤ F n e :=
    mul_nonneg (le_max_right _ _) (le_min zero_le_one
      (div_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (hRpos n).le))
  have hFm (n : ℕ) : Measurable (F n) :=
    (hw.max measurable_const).mul (measurable_const.min
      ((measurable_const.mul hd).div_const (R n)))
  have hdom (n : ℕ) (e : LegalMarkedPhysicalEdge q) : ‖F n e‖ ≤ max (w e) 0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hn n e)]
    exact mul_le_of_le_one_right (le_max_right _ _) (min_le_left _ _)
  have hFI (n : ℕ) : Integrable (F n) Γ :=
    hi.pos_part.mono' (hFm n).aestronglyMeasurable (.of_forall (hdom n))
  have hpoint (e : LegalMarkedPhysicalEdge q) : Tendsto (fun n ↦ F n e) atTop (𝓝 0) := by
    have hdlim : Tendsto (fun n ↦ (q : ℝ) * ‖e.2.1 - e.1.1‖ / R n) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, Function.comp_def, mul_zero] using
        (tendsto_const_nhds (x := (q : ℝ) * ‖e.2.1 - e.1.1‖)).mul
          (tendsto_inv_atTop_zero.comp hR)
    simpa only [F, min_eq_right zero_le_one, mul_zero] using
      (tendsto_const_nhds (x := max (w e) 0)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).min hdlim)
  have hreal : Tendsto (fun n ↦ ∫ e, F n e ∂Γ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun e ↦ max (w e) 0)
      (F := F) (f := fun _ ↦ (0 : ℝ))
      (fun n ↦ (hFm n).aestronglyMeasurable) hi.pos_part
      (fun n ↦ .of_forall (hdom n)) (.of_forall hpoint)
    simpa only [integral_zero] using h
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (∫ e, F n e ∂Γ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ ↦ bot_le)
  intro n
  have h := lintegral_shiftedGrid_crossing_energy_le q (hRpos n) Γ
    (fun e ↦ ENNReal.ofReal (w e)) hw.ennreal_ofReal
  apply h.trans_eq
  change _ = ENNReal.ofReal (∫ e, F n e ∂Γ)
  rw [ofReal_integral_eq_lintegral_ofReal (hFI n) (.of_forall (hn n))]
  apply lintegral_congr_ae
  filter_upwards with e
  have hmax : max (ENNReal.ofReal (w e)) 0 = ENNReal.ofReal (w e) :=
    max_eq_left (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (w e) from bot_le)
  simp only [F, ENNReal.ofReal_mul (le_max_right (w e) 0), ENNReal.ofReal_max,
    ENNReal.ofReal_zero, hmax]

/-- Exact original Palm integrability supplies the actual source-unit mean
plan's weight, without any independent law for selected matching endpoints. -/
theorem integrable_sourceUnitMeanPlan_palm_readout
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (w : PhysicalPairPalmMark (Fin q) → ℝ)
    (hi : Integrable w (legalMarkedJointPalm q M.law)) :
    Integrable (fun e : LegalMarkedPhysicalEdge q ↦ w (physicalPairAnchor e).2)
      (legalMarkedSourceUnitMeanPlan q M.law) := by
  have h : Integrable w ((legalMarkedSourceUnitMeanPlan q M.law).map
      (fun e ↦ (physicalPairAnchor e).2)) := by
    rw [map_legalMarkedSourceUnitMeanPlan_pairMark]
    exact hi
  exact h.comp_measurable measurable_physicalPairAnchor.snd

/-- Every integrable original Palm weight loses vanishing actual weight of
cut edges in the same scene/source-unit expectation. -/
theorem tendsto_original_stationary_shiftedGrid_crossing_palm_weight_zero
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (w : PhysicalPairPalmMark (Fin q) → ℝ) (hw : Measurable w)
    (hi : Integrable w (legalMarkedJointPalm q M.law))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ u, ∫⁻ scene,
        ∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ palmUnitCube (Fin q)},
          (if shiftedGridCells (R n) u e.1.1 ≠ shiftedGridCells (R n) u e.2.1
            then ENNReal.ofReal (w (physicalPairAnchor e).2) else 0)
          ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q))
        ∂(legalMarkedInputPairLaw q M.law : Measure
          (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
      ∂shiftedGridPhaseLaw q (R n)) atTop (𝓝 0) := by
  have hlim := tendsto_lintegral_shiftedGrid_crossing_integrable_weight_zero q
    (legalMarkedSourceUnitMeanPlan q M.law) (fun e ↦ w (physicalPairAnchor e).2)
    (hw.comp measurable_physicalPairAnchor.snd) (integrable_sourceUnitMeanPlan_palm_readout M w hi)
    R hRpos hR
  refine hlim.congr' (Filter.Eventually.of_forall (fun n ↦ ?_))
  apply lintegral_congr_ae
  filter_upwards with u
  have hs : Measurable (fun e : LegalMarkedPhysicalEdge q ↦ shiftedGridCells (R n) u e.1.1) :=
    (measurable_joint_shiftedGridCells (R n)).comp (measurable_const.prodMk measurable_fst.fst)
  have ht : Measurable (fun e : LegalMarkedPhysicalEdge q ↦ shiftedGridCells (R n) u e.2.1) :=
    (measurable_joint_shiftedGridCells (R n)).comp (measurable_const.prodMk measurable_snd.fst)
  have hwcut : Measurable (fun e : LegalMarkedPhysicalEdge q ↦
      if shiftedGridCells (R n) u e.1.1 ≠ shiftedGridCells (R n) u e.2.1
        then ENNReal.ofReal (w (physicalPairAnchor e).2) else 0) :=
    ((hw.comp measurable_physicalPairAnchor.snd).ennreal_ofReal).ite
      (measurableSet_eq_fun hs ht).compl measurable_const
  exact setLIntegral_physicalSceneMeanPlan _ hwcut (measurableSet_palmUnitCube (Fin q))

/-- The genuine original kinetic energy of any weighted stationary matching
loses vanishing mass under the independent random grid. No finite displacement
second moment is required. -/
theorem tendsto_original_stationary_shiftedGrid_crossing_kinetic_zero
    {q : ℕ} {α β : Measure ℝ} {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (M : LegalWeightedStationaryPoissonMatching q α β kin g)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (R : ℕ → ℝ) (hRpos : ∀ n, 0 < R n) (hR : Tendsto R atTop atTop) :
    Tendsto (fun n ↦ ∫⁻ u, ∫⁻ scene,
        ∫⁻ e in {e : LegalMarkedPhysicalEdge q | e.1.1 ∈ palmUnitCube (Fin q)},
          (if shiftedGridCells (R n) u e.1.1 ≠ shiftedGridCells (R n) u e.2.1
            then ENNReal.ofReal (kin e.1.2 e.2.2 (e.2.1 - e.1.1)) else 0)
          ∂(scene.1 : Measure (LegalMarkedPhysicalEdge q))
        ∂(legalMarkedInputPairLaw q M.law : Measure
          (CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q)))
      ∂shiftedGridPhaseLaw q (R n)) atTop (𝓝 0) := by
  exact tendsto_original_stationary_shiftedGrid_crossing_palm_weight_zero M
    (fun m ↦ kin m.1.1 m.1.2 m.2) hk M.kinetic_integrable R hRpos hR

end OTSelector.Reconstruction
