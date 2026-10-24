import OTSelector.Reconstruction.FinslerOriginalChartBallReach
import OTSelector.Reconstruction.FinslerOriginalWindowChartData

/-!
# Chart balls inside the calibrated interior: the exact remaining input

`FinslerOriginalChartBallReach` reduced the construction of `WindowChartData`
from the pre-atlas family to one geometric input: a compact chart ball
`closedBall y rho` in a chart target whose chart image lies in the calibrated
interior (the hypothesis `hinterior`).

This file analyses that input and isolates it exactly.

## What this file proves

* `exists_chartBall_of_mem_interior`: a point in the manifold interior of the
  calibrated interior produces a full chart ball whose chart image lies in the
  calibrated interior.  The proof takes the chart at the point and uses
  continuity of the inverse extended chart together with openness of the chart
  target.
* `exists_windowChartData_of_interior`: hence `WindowChartData` for a window
  family follows from a nonempty manifold interior of the calibrated interior,
  with no further geometric hypothesis.
* `interior_nonempty_of_windowChartData`: conversely, every `WindowChartData`
  forces the calibrated interior to have nonempty manifold interior, because the
  chart datum carries an open chart domain with two-sided calibration partners.
  Combining the two gives the exact characterization
  `windowChartData_iff_interior_nonempty` and, at the level of the chart ball,
  `exists_chartBall_iff_interior_nonempty`.
* `mem_chartInterior_of_mem_core`: the pre-atlas cover maps every compact core
  `X.K i` into the calibrated interior.
* `exists_chartBall_of_core_interior` and
  `exists_windowChartData_of_preAtlasFamily_coreInterior`: if one pre-atlas core
  has nonempty chart interior, the construction closes with no further input.

## Why the literal task cannot be closed from the cover alone

The pre-atlas cover states only
`(⋃ i, (extChartAt (X.old i)).symm '' X.K i) = chartInterior F u`
with each `X.K i` compact: it supplies calibrated-interior *membership* on
compact chart cores, not a single open set inside the calibrated interior.  A
full-dimensional chart ball requires more: by
`exists_chartBall_iff_interior_nonempty` such a ball exists exactly when the
calibrated interior has nonempty manifold interior, and this is an equivalent
form of the target conclusion `windowChartData_iff_interior_nonempty` itself.
So the remaining input is precisely nonempty manifold interior of the calibrated
interior (the local non-branching smooth ray-tube input of the paper), not a
consequence of the compact calibrated-interior cover.
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

/-! ## Self-model chart bookkeeping -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [T2Space M]
  [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- For the self model with corners the extended chart equals the preferred chart
as a function. -/
theorem extChartAt_apply_eq_chartAt {x : M} (z : M) :
    (extChartAt 𝓘(ℝ, E) x) z = (chartAt E x) z := by
  rw [extChartAt_coe]
  simp [modelWithCornersSelf_coe]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [T2Space M]
  [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- For the self model with corners the inverse of the extended chart equals the
inverse of the preferred chart. -/
theorem extChartAt_symm_apply_eq_chartAt {x : M} (z : E) :
    (extChartAt 𝓘(ℝ, E) x).symm z = (chartAt E x).symm z := by
  rw [extChartAt_coe_symm]
  simp [modelWithCornersSelf_coe_symm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [T2Space M]
  [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- For the self model with corners the target of the extended chart equals the
target of the preferred chart. -/
theorem extChartAt_target_eq_chartAt {x : M} :
    (extChartAt 𝓘(ℝ, E) x).target = (chartAt E x).target := by
  rw [extChartAt_target]
  simp [modelWithCornersSelf_coe_symm, modelWithCornersSelf_coe]

/-! ## Chart balls from an interior point of the calibrated interior -/

/-- **A chart ball inside the calibrated interior from an interior point.**  If a
point lies in the manifold interior of the calibrated interior, then some chart
ball in its chart target has all its chart images in the calibrated interior. -/
theorem exists_chartBall_of_mem_interior
    {x : M} (hx : x ∈ interior (chartInterior F u)) :
    ∃ (old : M) (y : E) (rho : ℝ), 0 < rho ∧
      closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      ∀ z ∈ closedBall y rho,
        (extChartAt 𝓘(ℝ, E) old).symm z ∈ chartInterior F u := by
  letI : MetricSpace M := F.metricSpace
  classical
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_interior.mp hx
  have hnhds : W ∈ 𝓝 x := hWopen.mem_nhds hxW
  have hpre : (extChartAt 𝓘(ℝ, E) x).symm ⁻¹' W ∈ 𝓝 ((extChartAt 𝓘(ℝ, E) x) x) :=
    extChartAt_preimage_mem_nhds (I := 𝓘(ℝ, E)) hnhds
  have htgt : (extChartAt 𝓘(ℝ, E) x).target ∈ 𝓝 ((extChartAt 𝓘(ℝ, E) x) x) :=
    (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) x).mem_nhds (mem_extChartAt_target x)
  have hinter : ((extChartAt 𝓘(ℝ, E) x).symm ⁻¹' W ∩ (extChartAt 𝓘(ℝ, E) x).target) ∈
      𝓝 ((extChartAt 𝓘(ℝ, E) x) x) := Filter.inter_mem hpre htgt
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hinter
  refine ⟨x, (extChartAt 𝓘(ℝ, E) x) x, eps / 2, by linarith, ?_, ?_⟩
  · intro z hz
    exact (hball (closedBall_subset_ball (by linarith) hz)).2
  · intro z hz
    have hzW : (extChartAt 𝓘(ℝ, E) x).symm z ∈ W :=
      (hball (closedBall_subset_ball (by linarith) hz)).1
    exact hWsub hzW

/-! ## The atlas-level field from nonempty manifold interior -/

/-- **`WindowChartData` from a nonempty manifold interior of the calibrated
interior.**  The chart ball supplied by `exists_chartBall_of_mem_interior` is
turned into uniform reach and then into the C1,1 ball core and the chart data of
the refined window family. -/
theorem exists_windowChartData_of_interior
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : (interior (chartInterior F u)).Nonempty) :
    ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) := by
  obtain ⟨x, hx⟩ := hx
  obtain ⟨old, y, rho, hrho, hyball, hinterior⟩ :=
    exists_chartBall_of_mem_interior (F := F) (u := u) hx
  refine exists_windowChartData_of_chartBallInterior (F := F) (u := u)
    hF hcomplete old hu hrho hyball ?_
  intro z hz
  exact hinterior z hz

/-! ## The pre-atlas compact cores map into the calibrated interior -/

/-- **Every pre-atlas core point maps into the calibrated interior.**  This is the
pointwise membership supplied by the exact cover equality of the pre-atlas
family. -/
theorem mem_chartInterior_of_mem_core
    (X : PreAtlasC11Family F u) {i : X.ι} {z : E} (hz : z ∈ X.K i) :
    (extChartAt 𝓘(ℝ, E) (X.old i)).symm z ∈ chartInterior F u := by
  rw [← X.cover]
  exact mem_iUnion.mpr ⟨i, mem_image_of_mem _ hz⟩

/-- **A chart ball inside a pre-atlas core with nonempty chart interior.**  If a
core of the pre-atlas family contains a chart ball, that ball is a chart ball
inside the calibrated interior.  Compact cores only supply membership; this
records what an open piece of a core would add. -/
theorem exists_chartBall_of_core_interior
    (X : PreAtlasC11Family F u) {i : X.ι} {x : E} (hx : x ∈ interior (X.K i)) :
    ∃ (y : E) (rho : ℝ), 0 < rho ∧
      closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) (X.old i)).target ∧
      ∀ z ∈ closedBall y rho,
        (extChartAt 𝓘(ℝ, E) (X.old i)).symm z ∈ chartInterior F u := by
  letI : MetricSpace M := F.metricSpace
  classical
  obtain ⟨W, hWsub, hWopen, hxW⟩ := mem_interior.mp hx
  obtain ⟨rho₀, hrho₀, hball⟩ := Metric.isOpen_iff.mp hWopen x hxW
  refine ⟨x, rho₀ / 2, by linarith, ?_, ?_⟩
  · intro z hz
    exact X.K_target i (hWsub (hball (closedBall_subset_ball (by linarith) hz)))
  · intro z hz
    have hzK : z ∈ X.K i :=
      hWsub (hball (closedBall_subset_ball (by linarith) hz))
    exact mem_chartInterior_of_mem_core (F := F) (u := u) X hzK

/-- **`WindowChartData` from a pre-atlas core with nonempty chart interior.**  This
is the strongest unconditional form available from the pre-atlas family alone:
the cover supplies calibrated-interior membership on compact cores, so an open
piece of one core is exactly what turns that membership into a chart ball. -/
theorem exists_windowChartData_of_preAtlasFamily_coreInterior
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (X : PreAtlasC11Family F u)
    (hcore : ∃ (i : X.ι) (x : E), x ∈ interior (X.K i)) :
    ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) := by
  obtain ⟨i, x, hx⟩ := hcore
  obtain ⟨y, rho, hrho, hyball, hinterior⟩ :=
    exists_chartBall_of_core_interior (F := F) (u := u) X hx
  refine exists_windowChartData_of_chartBallInterior (F := F) (u := u)
    hF hcomplete (X.old i) hu hrho hyball ?_
  intro z hz
  exact hinterior z hz

/-! ## The exact characterization of the remaining input -/

/-- **`WindowChartData` forces nonempty manifold interior of the calibrated
interior.**  The chart datum of a window carries an open chart domain on which
two-sided calibration partners at a positive distance exist, so the chart image
of that domain is an open subset of the calibrated interior. -/
theorem interior_nonempty_of_windowChartData
    {P : ℕ → F.CalibratedSeedWindow u} (W : WindowChartData P) :
    (interior (chartInterior F u)).Nonempty := by
  letI : MetricSpace M := F.metricSpace
  classical
  let C : CoreSectionChartData F u := W.chartData 0
  let e : OpenPartialHomeomorph M E := chartAt E C.old
  have he : e = chartAt E C.old := rfl
  have htarget : (extChartAt 𝓘(ℝ, E) C.old).target = (chartAt E C.old).target :=
    extChartAt_target_eq_chartAt (x := C.old)
  have hUball : C.U ⊆ e.target := by
    intro z hz
    rw [he, ← htarget]
    exact C.U_target hz
  have himg : IsOpen (e.symm '' C.U) :=
    e.isOpen_image_symm_of_subset_target C.U_open hUball
  have hx0 : C.σ 0 ∈ C.U := C.σ_mapsTo C.zero_V
  have hne : (e.symm '' C.U).Nonempty :=
    ⟨e.symm (C.σ 0), mem_image_of_mem _ hx0⟩
  have hsymm : ∀ z : E,
      e.symm z = (extChartAt 𝓘(ℝ, E) C.old).symm z := by
    intro z
    rw [he]
    exact (extChartAt_symm_apply_eq_chartAt (x := C.old) z).symm
  have hsub : e.symm '' C.U ⊆ chartInterior F u := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨a, b, ha, hua, hb, hub⟩ := C.partners_U z hz
    rw [hsymm z]
    change (extChartAt 𝓘(ℝ, E) C.old).symm z ∈
      OTSelector.Geometry.calibratedInterior u
    refine ⟨⟨a, ?_, ?_⟩, ⟨b, ?_, ?_⟩⟩
    · exact dist_pos.mp (by rw [ha]; exact C.δ_pos)
    · exact hua.trans ha.symm
    · exact dist_pos.mp (by rw [hb]; exact C.δ_pos)
    · exact hub.trans hb.symm
  exact Set.Nonempty.mono (interior_maximal hsub himg) hne

/-- **Exact characterization at the chart-ball level.**  A chart ball whose chart
image lies in the calibrated interior exists if and only if the calibrated
interior has nonempty manifold interior.  The forward direction takes the chart
image of the open ball; the backward direction is
`exists_chartBall_of_mem_interior`. -/
theorem exists_chartBall_iff_interior_nonempty :
    (∃ (old : M) (y : E) (rho : ℝ), 0 < rho ∧
      closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      ∀ z ∈ closedBall y rho,
        (extChartAt 𝓘(ℝ, E) old).symm z ∈ chartInterior F u) ↔
      (interior (chartInterior F u)).Nonempty := by
  constructor
  · rintro ⟨old, y, rho, hrho, hyball, hinterior⟩
    letI : MetricSpace M := F.metricSpace
    classical
    let e : OpenPartialHomeomorph M E := chartAt E old
    have he : e = chartAt E old := rfl
    have htarget : (extChartAt 𝓘(ℝ, E) old).target = (chartAt E old).target :=
      extChartAt_target_eq_chartAt (x := old)
    have hball : ball y rho ⊆ e.target := by
      intro z hz
      rw [he, ← htarget]
      exact hyball (ball_subset_closedBall hz)
    have himg : IsOpen (e.symm '' ball y rho) :=
      e.isOpen_image_symm_of_subset_target isOpen_ball hball
    have hsymm : ∀ z : E,
        e.symm z = (extChartAt 𝓘(ℝ, E) old).symm z := by
      intro z
      rw [he]
      exact (extChartAt_symm_apply_eq_chartAt (x := old) z).symm
    have hsub : e.symm '' ball y rho ⊆ chartInterior F u := by
      rintro w ⟨z, hz, rfl⟩
      rw [hsymm z]
      exact hinterior z (ball_subset_closedBall hz)
    have hne : (e.symm '' ball y rho).Nonempty :=
      ⟨e.symm y, mem_image_of_mem _ (mem_ball_self hrho)⟩
    exact Set.Nonempty.mono (interior_maximal hsub himg) hne
  · intro hx
    obtain ⟨x, hx⟩ := hx
    exact exists_chartBall_of_mem_interior (F := F) (u := u) hx

/-- **Exact characterization of the atlas-level field.**  `WindowChartData` for
some window family exists if and only if the calibrated interior has nonempty
manifold interior.  Consequently the "unconditional" form of the chart-ball
interior hypothesis is not a consequence of the compact pre-atlas cover: it is
equivalent to the conclusion it is used to prove. -/
theorem windowChartData_iff_interior_nonempty
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    (∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P)) ↔
      (interior (chartInterior F u)).Nonempty := by
  constructor
  · rintro ⟨P, ⟨W⟩⟩
    exact interior_nonempty_of_windowChartData (F := F) (u := u) W
  · intro hx
    exact exists_windowChartData_of_interior (F := F) (u := u) hF hcomplete hu hx

end OTSelector.Reconstruction
