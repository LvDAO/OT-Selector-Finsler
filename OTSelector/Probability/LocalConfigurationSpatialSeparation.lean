import OTSelector.Probability.WeakClosedConstraint
import OTSelector.PointProcess.LocalConfigurationPairWitness
import OTSelector.PointProcess.LocalConfiguration.MeasureSupport
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Spatial separation from original close-pair budgets

Open pair events pass their probability bounds to the same weak scene limit.
Vanishing small-ball volume then excludes two distinct occupied marked targets
at the same spatial position. This conclusion does not impose a simple-cloud
assumption on the approximating samples or require a prescribed Poisson limit.
-/

open MeasureTheory Set Function Filter Topology TopologicalSpace
open scoped ENNReal

noncomputable section
namespace OTSelector.Probability

open PointProcess PointProcess.LocalConfiguration

variable {ι B : Type*} [Fintype ι] [MetricSpace B]

/-- A nearby spatial pair whose marks remain separated. -/
def markedSpatialNearPair (W : Set (ι → ℝ)) (δ e : ℝ) :
    Set (((ι → ℝ) × B) × ((ι → ℝ) × B)) :=
  {p | p.1.1 ∈ W ∧ dist p.1.1 p.2.1 < e ∧ δ < dist p.1.2 p.2.2}

theorem isOpen_markedSpatialNearPair {W : Set (ι → ℝ)} (hW : IsOpen W) (δ e : ℝ) :
    IsOpen (markedSpatialNearPair (B := B) W δ e) :=
  (hW.preimage continuous_fst.fst).inter
    ((isOpen_lt (continuous_fst.fst.dist continuous_snd.fst) continuous_const).inter
      (isOpen_lt continuous_const (continuous_fst.snd.dist continuous_snd.snd)))

/-- In a positive spatial dimension, the volumes of shrinking balls vanish. -/
theorem tendsto_volume_ball_natRadius_zero [Nonempty ι] :
    Tendsto (fun n : ℕ ↦ volume (Metric.ball (0 : ι → ℝ) (1 / ((n : ℝ) + 1))))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun r : ℝ ↦ volume (Metric.ball (0 : ι → ℝ) r))
      (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_measure_biInter_gt (μ := (volume : Measure (ι → ℝ)))
      (s := fun r ↦ Metric.ball 0 r)
      (a := (0 : ℝ)) (fun _ _ ↦ Metric.isOpen_ball.measurableSet.nullMeasurableSet)
      (fun _ _ _ hij ↦ Metric.ball_subset_ball hij)
      ⟨1, zero_lt_one, measure_ball_lt_top.ne⟩
    simpa only [Metric.biInter_gt_ball, Metric.closedBall_zero, measure_singleton,
      Function.comp_def]
      using h
  apply ht.comp
  exact tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall (fun n ↦ by
      change (0 : ℝ) < 1 / ((n : ℝ) + 1)
      positivity)⟩

section WeakLimit

variable [ProperSpace B] {base : (ι → ℝ) × B}
  {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
  [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]

local instance spatialSeparationTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base

/-- A uniform original bound on an open pair event survives weak convergence. -/
theorem measure_hasPairIn_le_of_weak_tendsto
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P))
    (config : Ω → LocalConfiguration base) (hc : Continuous config)
    {R : Set (((ι → ℝ) × B) × ((ι → ℝ) × B))} (hR : IsOpen R)
    {V : ℝ≥0∞}
    (hb : ∀ n, (Pn n : Measure Ω) {ω | HasPairIn R (config ω)} ≤ V) :
    (P : Measure Ω) {ω | HasPairIn R (config ω)} ≤ V := by
  exact OTSelector.Probability.measure_open_le_of_tendsto_bounds P Pn hweak _
    ((isOpen_hasPairIn hR).preimage hc) (fun _ ↦ V) V tendsto_const_nhds hb

set_option backward.isDefEq.respectTransparency false in
/-- Original vanishing close-pair budgets exclude spatial collisions in the
same common weak limit. The countable cloud itself supplies the target set. -/
theorem ae_spatial_injective_of_weak_pair_budget [Nonempty ι]
    (P : ProbabilityMeasure Ω) (Pn : ℕ → ProbabilityMeasure Ω)
    (hweak : Tendsto Pn atTop (𝓝 P))
    (config : Ω → LocalConfiguration base) (hc : Continuous config)
    (hb : ∀ n j k m : ℕ, (Pn n : Measure Ω) {ω | HasPairIn
        (markedSpatialNearPair (Metric.ball (0 : ι → ℝ) ((j : ℝ) + 1))
          (1 / ((k : ℝ) + 1)) (1 / ((m : ℝ) + 1))) (config ω)} ≤
      volume (Metric.ball (0 : ι → ℝ) ((j : ℝ) + 1)) *
        volume (Metric.ball (0 : ι → ℝ) (1 / ((m : ℝ) + 1)))) :
    ∀ᵐ ω ∂(P : Measure Ω),
      Set.InjOn Prod.fst (Function.support (multiplicity (config ω))) := by
  let E (j k m : ℕ) : Set Ω := {ω | HasPairIn
    (markedSpatialNearPair (Metric.ball (0 : ι → ℝ) ((j : ℝ) + 1))
      (1 / ((k : ℝ) + 1)) (1 / ((m : ℝ) + 1))) (config ω)}
  have hnull (j k : ℕ) : (P : Measure Ω) (⋂ m, E j k m) = 0 := by
    apply le_antisymm _ bot_le
    have ht := ENNReal.Tendsto.const_mul (tendsto_volume_ball_natRadius_zero (ι := ι))
      (Or.inr (measure_ball_lt_top.ne :
        volume (Metric.ball (0 : ι → ℝ) ((j : ℝ) + 1)) ≠ ∞))
    simp only [mul_zero] at ht
    apply ge_of_tendsto ht
    apply Eventually.of_forall
    intro m
    exact (measure_mono (iInter_subset _ m)).trans
      (measure_hasPairIn_le_of_weak_tendsto P Pn hweak config hc
        (isOpen_markedSpatialNearPair Metric.isOpen_ball _ _) (fun n ↦ hb n j k m))
  have hae : ∀ j k : ℕ, ∀ᵐ ω ∂(P : Measure Ω), ω ∉ ⋂ m, E j k m := by
    intro j k
    rw [ae_iff]
    convert hnull j k using 1
    congr 1
    ext ω
    simp only [mem_ofPred_eq, not_not, mem_iInter]
  filter_upwards [ae_all_iff.mpr (fun j ↦ ae_all_iff.mpr (hae j))] with ω hω
  intro x hx y hy hxy
  by_contra hne
  have hmark : x.2 ≠ y.2 := fun heq ↦ hne (Prod.ext hxy heq)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (dist_pos.mpr hmark)
  obtain ⟨j, hj⟩ := exists_nat_gt (dist x.1 (0 : ι → ℝ))
  apply hω j k
  apply mem_iInter.mpr
  intro m
  refine ⟨x, y, hx, hy, ?_, ?_, hk⟩
  · change dist x.1 0 < (j : ℝ) + 1
    exact hj.trans (lt_add_one _)
  · change dist x.1 y.1 < 1 / ((m : ℝ) + 1)
    rw [hxy, dist_self]
    positivity

end WeakLimit
end OTSelector.Probability
