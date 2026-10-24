import OTSelector.Reconstruction.FinslerOriginalWindowChartExtension
import OTSelector.Geometry.Finsler.CalibratedReach
import Mathlib.Topology.Baire.Lemmas

/-!
# Uniform two-sided reach on a chart ball from the calibrated-interior cover

`FinslerOriginalWindowChartExtension.lean` reduced the construction of
`WindowChartData` from the pre-atlas family to a single geometric input: a compact
chart ball `closedBall y ρ` in a chart target whose points all admit two-sided
calibration partners at one fixed distance `δ`.  The calibrated-interior cover
supplies such partners at a fixed distance only on its own compact trimmed contact
pieces, not on an arbitrary chart ball.

## What this file proves

The calibrated interior has a countable compact trimmed contact cover
`F.exists_compact_trimmed_contact_cover`: compact pieces `K i` and endpoint
carriers `A i` with `⋃ i, K i = calibratedInterior u`, and on `K i` every point
has forward and backward calibrated partners at the *prescribed* distance
`1 / (i.1 + 1)`.

Restricted to the chart ball, that is a countable cover by sets closed in the ball.
The ball is an open subset of the finite-dimensional space, hence Baire, so the
union of their interiors is dense; in particular some piece has nonempty interior.
That interior contains a full metric ball around a point `z` of the original chart
ball, and on that ball the fixed prescribed distance of the corresponding cover
piece gives uniform two-sided reach.

Thus any chart ball whose chart image lies in the calibrated interior contains a
*sub*-chart-ball on which the uniform two-sided reach hypothesis holds.  This
sub-ball is exactly what the C1,1 ball-core refinement consumes.

## Exact remaining input

The hypothesis `hinterior`: the chart ball's chart image lies in the
calibrated interior.  For a compact chart ball this follows from the pre-atlas
calibrated-interior cover; it replaces the previously assumed uniform reach, and
is weaker: the cover gives interior membership pointwise, and this file turns it
back into a *uniform* distance on a smaller chart ball.
-/
open Set Function Metric Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe uE uM

variable {E : Type uE} {M : Type uM}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## Uniform reach on a sub-chart-ball of the calibrated interior -/

/-- **Uniform two-sided reach on a chart sub-ball from the calibrated-interior cover.**
Suppose a chart ball `closedBall y ρ` lies in the chart target and every point of it
maps into the calibrated interior.  Then a smaller chart ball `closedBall y' ρ' ⊆
closedBall y ρ` carries two-sided calibration partners at one fixed distance `δ > 0`.

The proof restricts the countable compact trimmed contact cover of the calibrated
interior to the open ball, uses the Baire property of the open ball to find a cover
piece with nonempty interior there, and reads the fixed prescribed distance of that
piece as the uniform reach distance. -/
theorem exists_chartBall_uniformReach
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {y : E} {rho : ℝ} (hrho : 0 < rho)
    (hyball : closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hinterior : letI : MetricSpace M := F.metricSpace;
      ∀ z ∈ closedBall y rho,
        (extChartAt 𝓘(ℝ, E) old).symm z ∈ OTSelector.Geometry.calibratedInterior u) :
    ∃ (y' : E) (rho' : ℝ) (delta : ℝ), 0 < rho' ∧ 0 < delta ∧
      closedBall y' rho' ⊆ closedBall y rho ∧
      CalibratedPartners F u old delta (closedBall y' rho') := by
  letI : MetricSpace M := F.metricSpace
  classical
  obtain ⟨Kt, At, hKA, hcover, hcontact⟩ := F.exists_compact_trimmed_contact_cover hcomplete hu
  let V : Set E := ball y rho
  have hVopen : IsOpen V := isOpen_ball
  have hVsub : V ⊆ (extChartAt 𝓘(ℝ, E) old).target := fun z hz =>
    hyball (ball_subset_closedBall hz)
  have hgcont : Continuous (fun z : V => (extChartAt 𝓘(ℝ, E) old).symm (z : E)) :=
    (continuousOn_extChartAt_symm (I := 𝓘(ℝ, E)) old).comp_continuous
      continuous_subtype_val (fun z => hVsub z.2)
  let f : ℕ × ℕ → Set V := fun i =>
    {z : V | (extChartAt 𝓘(ℝ, E) old).symm (z : E) ∈ Kt i}
  have hfclosed : ∀ i, IsClosed (f i) := by
    intro i
    exact (hKA i).1.isClosed.preimage hgcont
  have hcoverV : (univ : Set V) ⊆ ⋃ i, f i := by
    intro z _
    have hzK : (extChartAt 𝓘(ℝ, E) old).symm (z : E) ∈ ⋃ i, Kt i := by
      rw [hcover]
      exact hinterior z.1 (ball_subset_closedBall z.2)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzK
    exact mem_iUnion.mpr ⟨i, hi⟩
  haveI : Nonempty V := ⟨⟨y, mem_ball_self hrho⟩⟩
  haveI hVB : BaireSpace V := hVopen.baireSpace
  have hdense : Dense (⋃ i, interior (f i)) :=
    IsGδ.dense_iUnion_interior_of_closed (f := f) IsGδ.univ dense_univ hfclosed hcoverV
  have hne : (⋃ i, interior (f i)).Nonempty := hdense.nonempty
  obtain ⟨z, hzint⟩ := hne
  rw [mem_iUnion] at hzint
  obtain ⟨i, hzint⟩ := hzint
  obtain ⟨eps, heps, hepsub⟩ :=
    Metric.isOpen_iff.mp (isOpen_interior : IsOpen (interior (f i))) z hzint
  have hzV : dist (z : E) y < rho := mem_ball.mp z.2
  let eps2 : ℝ := min eps ((rho - dist (z : E) y) / 2)
  have heps2pos : 0 < eps2 := lt_min heps (by linarith)
  have heps2le : eps2 ≤ eps := min_le_left _ _
  have heps2right : eps2 ≤ (rho - dist (z : E) y) / 2 := min_le_right _ _
  have hballV : ball (z : E) eps2 ⊆ V := by
    intro w hw
    rw [mem_ball] at hw ⊢
    calc dist w y ≤ dist w (z : E) + dist (z : E) y := dist_triangle w (z : E) y
      _ < eps2 + dist (z : E) y := by linarith
      _ ≤ (rho - dist (z : E) y) / 2 + dist (z : E) y := by linarith
      _ < rho := by linarith
  have hballpre : ball (z : E) eps2 ⊆ (extChartAt 𝓘(ℝ, E) old).symm ⁻¹' Kt i := by
    intro w hw
    rw [mem_ball] at hw
    have hwV : w ∈ V := hballV (mem_ball.mpr hw)
    have hmem : (⟨w, hwV⟩ : V) ∈ Metric.ball z eps := by
      rw [mem_ball, Subtype.dist_eq]
      exact lt_of_lt_of_le hw heps2le
    have hint : (⟨w, hwV⟩ : V) ∈ interior (f i) := hepsub hmem
    have hfin : (⟨w, hwV⟩ : V) ∈ f i := interior_subset hint
    simpa [f] using hfin
  refine ⟨(z : E), eps2 / 2, 1 / (i.1 + 1 : ℝ), ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro w hw
    have hw' : w ∈ ball (z : E) eps2 := by
      rw [mem_ball]
      have := mem_closedBall.mp hw
      linarith
    exact ball_subset_closedBall (hballV hw')
  · intro x hx
    have hxball : x ∈ ball (z : E) eps2 := by
      rw [mem_ball]
      have := mem_closedBall.mp hx
      linarith
    have hxK : (extChartAt 𝓘(ℝ, E) old).symm x ∈ Kt i := hballpre hxball
    obtain ⟨a, -, b, -, ha, hua, hb, hub⟩ :=
      hcontact i ((extChartAt 𝓘(ℝ, E) old).symm x) hxK
    exact ⟨a, b, ha, hua, hb, hub⟩

/-! ## The C1,1 potential ball core on a chart sub-ball of the calibrated interior -/

/-- **The compact potential ball core exists on a chart sub-ball of the calibrated
interior.**  Combining the uniform reach above with the C1,1 ball-core refinement. -/
theorem exists_ballCoreData_of_chartBallInterior
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {y : E} {rho : ℝ} (hrho : 0 < rho)
    (hyball : closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hinterior : letI : MetricSpace M := F.metricSpace;
      ∀ z ∈ closedBall y rho,
        (extChartAt 𝓘(ℝ, E) old).symm z ∈ OTSelector.Geometry.calibratedInterior u) :
    Nonempty (BallCorePotentialData (F := F) (u := u) old) := by
  obtain ⟨y', rho', delta, hrho', hdelta, hsub, hreach⟩ :=
    exists_chartBall_uniformReach (F := F) (u := u) hcomplete old hu hrho hyball hinterior
  have hy'ball : closedBall y' rho' ⊆ (extChartAt 𝓘(ℝ, E) old).target := hsub.trans hyball
  exact exists_ballCorePotentialData (F := F) (u := u) hF hcomplete old hdelta hu hrho' hy'ball hreach

/-! ## Window chart data from a chart sub-ball of the calibrated interior -/

/-- **The atlas-level field from a chart sub-ball inside the calibrated interior.**
All previously assumed open-neighbourhood extension inputs, the rational level, the
level section, and the uniform chart-ball reach are constructed; the only remaining
geometric hypothesis is that a compact chart ball maps into the calibrated interior. -/
theorem exists_windowChartData_of_chartBallInterior
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {y : E} {rho : ℝ} (hrho : 0 < rho)
    (hyball : closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hinterior : letI : MetricSpace M := F.metricSpace;
      ∀ z ∈ closedBall y rho,
        (extChartAt 𝓘(ℝ, E) old).symm z ∈ OTSelector.Geometry.calibratedInterior u) :
    ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) := by
  obtain ⟨BC⟩ :=
    exists_ballCoreData_of_chartBallInterior (F := F) (u := u) hF hcomplete old hu hrho hyball hinterior
  exact exists_windowChartData_of_ballCoreData (F := F) (u := u) hF hcomplete hu BC

end OTSelector.Reconstruction
