import OTSelector.Geometry.Finsler.CalibratedDistance
import OTSelector.Reconstruction.FinslerOriginalWindowChartData
import OTSelector.Reconstruction.FinslerOriginalRefinementGeometry
import OTSelector.Reconstruction.FinslerOriginalWindowChartAe
import OTSelector.Reconstruction.FinslerOriginalWindowChartUnconditional

/-!
# Interior nonemptiness of the calibrated interior: the calibrated-tube route

The endgame input isolated by |FinslerOriginalAeOpenChartData| and
|FinslerOriginalPopulationOpenChartProducer| is
|(interior (chartInterior F u)).Nonempty|.  This file attacks it and records what
the paper actually supplies.

## What the paper supplies (precise citations)

* main.tex:1063 opens Section "Local geometry of calibrated Finsler ray tubes"
  (label sec:raytube) with a smooth coordinate diffeomorphism X : J x B -> M,
  B open, and a globally 1-Lipschitz phi with phi(X(r,z)) = r and unit radial
  Finsler speed.  main.tex:1076-1078 then states verbatim: "This calibrated tube
  assumption is a local geometric hypothesis; we do not assume that arbitrary
  marginals already supply such tubes."
* main.tex:1173-1185: "the moving ray set is covered, up to volume zero, by
  countably many disjoint ray clusters. Each has an injective locally Lipschitz
  parametrization on a Borel domain with compact transverse base. ... These are
  the conclusions of the cited ray-cluster package, rather than an assumed smooth
  open foliation."
* main.tex:802: "let N = T_phi^circ be the common full-marginal-measure
  interior-ray set."  The paper's T_phi^circ is only a full-marginal-measure
  Borel set.

So the paper never derives nonempty interiority of the calibrated interior from
the marginals: the smooth tube is a local geometric hypothesis, and the rough
ray-cluster package is Borel, not open.  The endgame input is therefore a genuine
geometric hypothesis, and the strongest available route is: from the paper's
tube hypothesis prove the endgame input.

## What this file proves

Section 1 isolates the minimal metric content of "the calibrated interior
contains an open set of chart points": an open nonempty set of chart points each
having two-sided calibration partners at positive distance has its chart image in
the calibrated interior, and hence yields nonempty manifold interior.  This is
the weakest explicit hypothesis form of the task's route (b).

Section 2 states the paper's local calibrated tube in Lean (open nonempty time
interval, label set, smooth unit-speed calibrated radial curves, open tube image)
and proves that its radial curves are isometries (from calibration plus unit
speed, via |isometry_Icc_of_unitSpeed_calibration|).  Every point of the tube
image therefore has actual two-sided partners, and since the tube image is open
and nonempty, the calibrated interior has nonempty manifold interior
(|CalibratedTube.interior_nonempty|).

Section 3 feeds that conclusion into the a.e.-to-exact upgrade: a calibrated tube
produces a nonempty exact chart datum, an a.e. window producer whose full-measure
set is open in every window, and a calibrated level-seed patch for every window.
Combined with the equivalences of |FinslerOriginalPopulationOpenChartProducer|,
the tube hypothesis is exactly the topological content of the endgame, so no
weaker almost-everywhere statement can replace it.
-/
open Set Function Metric Manifold OTSelector.Geometry MeasureTheory
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe uE uM uZ

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## 1. The weakest explicit hypothesis: an open set of calibrated chart points -/

/-- **An open nonempty set of chart points with two-sided calibration partners
has nonempty manifold interior in the calibrated interior.**  No potential,
Euler--Lagrange, section or measure datum is needed: the partners alone put the
open chart image inside the calibrated interior.  This is the weakest explicit
form of the task's route (b): the calibrated interior contains an open chart
domain intersected with the calibration conditions. -/
theorem nonempty_interior_of_open_partners
    {old : M} {O : Set E} (hO : IsOpen O) (hOne : O.Nonempty)
    (hOt : O ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hpartners : letI : MetricSpace M := F.metricSpace;
      ∀ x ∈ O, ∃ a b : M,
        a ≠ (extChartAt 𝓘(ℝ, E) old).symm x ∧
          u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a =
            dist a ((extChartAt 𝓘(ℝ, E) old).symm x) ∧
          b ≠ (extChartAt 𝓘(ℝ, E) old).symm x ∧
            u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) =
              dist ((extChartAt 𝓘(ℝ, E) old).symm x) b) :
    (interior (chartInterior F u)).Nonempty := by
  letI : MetricSpace M := F.metricSpace
  classical
  let e : OpenPartialHomeomorph M E := chartAt E old
  have htarget : (extChartAt 𝓘(ℝ, E) old).target = (chartAt E old).target :=
    extChartAt_target_eq_chartAt
  have hOball : O ⊆ e.target := by
    intro z hz
    show z ∈ (chartAt E old).target
    rw [← htarget]
    exact hOt hz
  have himg : IsOpen (e.symm '' O) := e.isOpen_image_symm_of_subset_target hO hOball
  have hne : (e.symm '' O).Nonempty := by
    obtain ⟨z, hz⟩ := hOne
    exact ⟨e.symm z, mem_image_of_mem _ hz⟩
  have hsymm : ∀ z : E, e.symm z = (extChartAt 𝓘(ℝ, E) old).symm z := by
    intro z
    show (chartAt E old).symm z = (extChartAt 𝓘(ℝ, E) old).symm z
    exact (extChartAt_symm_apply_eq_chartAt (x := old) z).symm
  have hsub : e.symm '' O ⊆ chartInterior F u := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨a, b, ha, hua, hb, hub⟩ := hpartners z hz
    rw [hsymm z]
    change (extChartAt 𝓘(ℝ, E) old).symm z ∈
      OTSelector.Geometry.calibratedInterior u
    exact ⟨⟨a, ha, hua⟩, ⟨b, hb.symm, hub⟩⟩
  exact Set.Nonempty.mono (interior_maximal hsub himg) hne

/-- The endgame input is exactly the existence of an open nonempty subset of the
calibrated interior, i.e. the smallest possible explicit interface for it. -/
theorem nonempty_interior_iff_exists_open_subset :
    (∃ O : Set M, IsOpen O ∧ O.Nonempty ∧ O ⊆ chartInterior F u) ↔
      (interior (chartInterior F u)).Nonempty := by
  constructor
  · rintro ⟨O, hO, hOne, hOsub⟩
    exact Set.Nonempty.mono (interior_maximal hOsub hO) hOne
  · rintro ⟨x, hx⟩
    exact ⟨interior (chartInterior F u), isOpen_interior, ⟨x, hx⟩, interior_subset⟩

/-! ## 2. The paper's local smooth calibrated tube -/

/-- The image of a tube parametrization. -/
def tubeImage {Z : Type uZ} (J : Set ℝ) (base : Set Z) (curve : Z → ℝ → M) : Set M :=
  (fun q : ℝ × Z ↦ curve q.2 q.1) '' (J ×ˢ base)

/-- **The paper's calibrated tube** (main.tex, Section "Local geometry of
calibrated Finsler ray tubes", label sec:raytube): a time interval J, a label set
and a smooth unit-speed curve family whose calibration clock is the time
coordinate, with an open tube image (the paper's smooth coordinate
diffeomorphism). -/
structure CalibratedTube (F : ContinuousFinslerNorm E M) (u : M → ℝ) (Z : Type uZ) where
  /-- The open time interval of the tube. -/
  J : Set ℝ
  J_open : IsOpen J
  J_nonempty : J.Nonempty
  /-- The time interval is convex, so it contains the closed segments it spans. -/
  J_convex : ∀ ⦃r : ℝ⦄, r ∈ J → ∀ ⦃r' : ℝ⦄, r' ∈ J → Icc r r' ⊆ J
  /-- The transverse label set. -/
  base : Set Z
  base_nonempty : base.Nonempty
  /-- The radial calibrated curves. -/
  curve : Z → ℝ → M
  /-- The tube is an open coordinate chart: its image is open. -/
  image_open : IsOpen (tubeImage J base curve)
  /-- The tube curves are C1 (the paper's smooth coordinate diffeomorphism). -/
  curve_contMDiff : ∀ z ∈ base, ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (curve z) univ
  /-- The radial velocity is unit speed. -/
  unit_speed : ∀ z ∈ base, ∀ t : ℝ,
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (curve z) ⟨t, (1 : ℝ)⟩) = 1
  /-- Calibration: the potential equals the time coordinate on the tube. -/
  clock : ∀ z ∈ base, ∀ r ∈ J, u (curve z r) = r

namespace CalibratedTube

variable {Z : Type uZ}

/-- The tube's parametrized image. -/
def image (T : CalibratedTube F u Z) : Set M := tubeImage T.J T.base T.curve

/-- **Calibration plus unit speed make the radial curves isometries.**
On any closed time segment inside the tube interval the radial curve preserves
distances exactly. -/
theorem radial_dist (T : CalibratedTube F u Z)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {z : Z} (hz : z ∈ T.base) {r r' : ℝ} (hr : r ∈ T.J) (hr' : r' ∈ T.J) :
    letI : MetricSpace M := F.metricSpace
    dist (T.curve z r) (T.curve z r') = |r - r'| := by
  letI : MetricSpace M := F.metricSpace
  rcases le_total r r' with hle | hle
  · have hIcc : Icc r r' ⊆ T.J := T.J_convex hr hr'
    have hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (T.curve z) (Icc r r') :=
      (T.curve_contMDiff z hz).mono (subset_univ _)
    have hspeed : ∀ t ∈ Ioo r r',
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (T.curve z) ⟨t, (1 : ℝ)⟩) = 1 :=
      fun t _ => T.unit_speed z hz t
    have hsat : ∀ t ∈ Icc r r', u (T.curve z t) = t + 0 := by
      intro t ht
      rw [T.clock z hz t (hIcc ht)]
      ring
    have hiso := F.isometry_Icc_of_unitSpeed_calibration (u := u) hu hc hspeed hsat
    have hd := hiso.dist_eq (⟨r, left_mem_Icc.mpr hle⟩ : Icc r r')
      ⟨r', right_mem_Icc.mpr hle⟩
    simpa only [Subtype.dist_eq, Real.dist_eq] using hd
  · have hIcc : Icc r' r ⊆ T.J := T.J_convex hr' hr
    have hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (T.curve z) (Icc r' r) :=
      (T.curve_contMDiff z hz).mono (subset_univ _)
    have hspeed : ∀ t ∈ Ioo r' r,
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (T.curve z) ⟨t, (1 : ℝ)⟩) = 1 :=
      fun t _ => T.unit_speed z hz t
    have hsat : ∀ t ∈ Icc r' r, u (T.curve z t) = t + 0 := by
      intro t ht
      rw [T.clock z hz t (hIcc ht)]
      ring
    have hiso := F.isometry_Icc_of_unitSpeed_calibration (u := u) hu hc hspeed hsat
    have hd := hiso.dist_eq (⟨r', left_mem_Icc.mpr hle⟩ : Icc r' r)
      ⟨r, right_mem_Icc.mpr hle⟩
    have hd' : dist (T.curve z r') (T.curve z r) = |r' - r| := by
      simpa only [Subtype.dist_eq, Real.dist_eq] using hd
    rw [dist_comm, abs_sub_comm]
    exact hd'

/-- **Every tube point lies in the calibrated interior**, with actual two-sided
partners at a positive distance. -/
theorem subset_chartInterior (T : CalibratedTube F u Z)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    T.image ⊆ chartInterior F u := by
  letI : MetricSpace M := F.metricSpace
  rintro x ⟨⟨r, z⟩, ⟨hrJ, hzB⟩, rfl⟩
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (T.J_open.mem_nhds hrJ)
  have hq : 0 < ε / 2 := half_pos hε
  have hlo : r - ε / 2 ∈ T.J := hεsub (by
    rw [Metric.mem_ball, Real.dist_eq,
      show r - ε / 2 - r = -(ε / 2) by ring, abs_neg, abs_of_pos hq]
    linarith)
  have hhi : r + ε / 2 ∈ T.J := hεsub (by
    rw [Metric.mem_ball, Real.dist_eq,
      show r + ε / 2 - r = ε / 2 by ring, abs_of_pos hq]
    linarith)
  change T.curve z r ∈ OTSelector.Geometry.calibratedInterior u
  refine ⟨⟨T.curve z (r - ε / 2), ?_, ?_⟩, ⟨T.curve z (r + ε / 2), ?_, ?_⟩⟩
  · intro hcontra
    have h1 : u (T.curve z (r - ε / 2)) = r - ε / 2 := T.clock z hzB (r - ε / 2) hlo
    have h2 : u (T.curve z r) = r := T.clock z hzB r hrJ
    rw [hcontra, h2] at h1
    linarith
  · have h1 : u (T.curve z (r - ε / 2)) = r - ε / 2 := T.clock z hzB (r - ε / 2) hlo
    have h2 : u (T.curve z r) = r := T.clock z hzB r hrJ
    have hd : dist (T.curve z (r - ε / 2)) (T.curve z r) = |r - ε / 2 - r| :=
      T.radial_dist hu hzB hlo hrJ
    rw [h2, h1, hd,
      show r - ε / 2 - r = -(ε / 2) by ring, abs_neg, abs_of_pos hq]
    ring
  · intro hcontra
    have h1 : u (T.curve z (r + ε / 2)) = r + ε / 2 := T.clock z hzB (r + ε / 2) hhi
    have h2 : u (T.curve z r) = r := T.clock z hzB r hrJ
    rw [← hcontra, h2] at h1
    linarith
  · have h1 : u (T.curve z (r + ε / 2)) = r + ε / 2 := T.clock z hzB (r + ε / 2) hhi
    have h2 : u (T.curve z r) = r := T.clock z hzB r hrJ
    have hd : dist (T.curve z r) (T.curve z (r + ε / 2)) = |r - (r + ε / 2)| :=
      T.radial_dist hu hzB hrJ hhi
    rw [h1, h2, hd,
      show r - (r + ε / 2) = -(ε / 2) by ring, abs_neg, abs_of_pos hq]
    ring

/-- **The paper's calibrated tube yields the endgame input.**  The tube image is
open and nonempty, and by the previous theorem it lies in the calibrated
interior. -/
theorem interior_nonempty (T : CalibratedTube F u Z)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    (interior (chartInterior F u)).Nonempty := by
  have hne : T.image.Nonempty := by
    obtain ⟨r, hr⟩ := T.J_nonempty
    obtain ⟨z, hz⟩ := T.base_nonempty
    exact ⟨T.curve z r, (r, z), ⟨hr, hz⟩, rfl⟩
  exact Set.Nonempty.mono (interior_maximal (T.subset_chartInterior hu) T.image_open) hne

end CalibratedTube

/-! ## 3. The endgame assumption implies the a.e.-to-exact upgrade -/

/-- **The endgame input gives a nonempty exact chart datum** (the chart-ball
construction of the exact-atlas lane). -/
theorem nonempty_chartData_of_interior_nonempty
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : (interior (chartInterior F u)).Nonempty) :
    Nonempty (CoreSectionChartData F u) := by
  obtain ⟨P, ⟨W⟩⟩ :=
    exists_windowChartData_of_interior (F := F) (u := u) hF hcomplete hu hx
  exact ⟨W.chartData 0⟩

/-- **The endgame input gives an a.e. window producer whose full-measure set is
open in every window**, so the open-domain transfer applies unconditionally. -/
theorem exists_openGood_windowChartDataAe_of_interior_nonempty
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : (interior (chartInterior F u)).Nonempty) (μ : Measure E) :
    ∃ (P : ℕ → F.CalibratedSeedWindow u)
      (κ : ∀ j, Measure (P j).seed.covector.ker)
      (W : WindowChartDataAe (F := F) (u := u) κ μ),
      (∀ j, IsOpen ((W.chartData j).good)) ∧
        (∀ j, (W.chartData j).σ 0 ∈ (W.chartData j).good) := by
  obtain ⟨P, ⟨W⟩⟩ :=
    exists_windowChartData_of_interior (F := F) (u := u) hF hcomplete hu hx
  refine ⟨P, fun _ => 0, W.toAe (fun _ => 0) μ, ?_, ?_⟩
  · intro j
    show IsOpen (((W.chartData j).toAe μ).good)
    rw [CoreSectionChartData.toAe_good]
    exact (W.chartData j).U_open
  · intro j
    show ((W.chartData j).toAe μ).σ 0 ∈ ((W.chartData j).toAe μ).good
    rw [CoreSectionChartData.toAe_σ, CoreSectionChartData.toAe_good]
    exact (W.chartData j).σ_mapsTo (W.chartData j).zero_V

/-- **The endgame input gives a calibrated level-seed patch for every window**:
the input of the pointwise reconstruction consumers. -/
theorem exists_levelSeedPatches_of_interior_nonempty
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : (interior (chartInterior F u)).Nonempty) :
    ∃ (P : ℕ → F.CalibratedSeedWindow u) (W : WindowChartData P),
      ∀ j, ∃ (A : F.CalibratedLevelSeedPatch u)
          (e : A.covector.ker ≃L[ℝ] (W.chartData j).p.ker),
        A.openLabels = e ⁻¹' (W.chartData j).V ∧
          A.labels = e ⁻¹' ((W.chartData j).V ∩
            (W.chartData j).σ ⁻¹' (W.parentCore j)) ∧
            (∀ w t, A.curve w t =
              (W.chartData j).Γ ((W.chartData j).σ (e w)) t) ∧
              A.level = (W.chartData j).q := by
  obtain ⟨P, ⟨W⟩⟩ :=
    exists_windowChartData_of_interior (F := F) (u := u) hF hcomplete hu hx
  refine ⟨P, W, fun j => ?_⟩
  exact exists_levelSeedPatch_of_chartData (F := F) (u := u) hF hcomplete hu
    (W.chartData j) (W.parentCore_compact j) (W.parentCore_subset j)
    (W.parentCore_center j)

/-! ### The calibrated tube supplies the endgame input -/

/-- **A calibrated tube produces a nonempty exact chart datum.** -/
theorem nonempty_chartData_of_calibratedTube
    {Z : Type uZ} (T : CalibratedTube F u Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    Nonempty (CoreSectionChartData F u) :=
  nonempty_chartData_of_interior_nonempty hF hcomplete hu (T.interior_nonempty hu)

/-- **A calibrated tube produces an open-good a.e. window producer.** -/
theorem exists_openGood_windowChartDataAe_of_calibratedTube
    {Z : Type uZ} (T : CalibratedTube F u Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (μ : Measure E) :
    ∃ (P : ℕ → F.CalibratedSeedWindow u)
      (κ : ∀ j, Measure (P j).seed.covector.ker)
      (W : WindowChartDataAe (F := F) (u := u) κ μ),
      (∀ j, IsOpen ((W.chartData j).good)) ∧
        (∀ j, (W.chartData j).σ 0 ∈ (W.chartData j).good) :=
  exists_openGood_windowChartDataAe_of_interior_nonempty hF hcomplete hu
    (T.interior_nonempty hu) μ

/-- **A calibrated tube produces a calibrated level-seed patch for every
window.** -/
theorem exists_levelSeedPatches_of_calibratedTube
    {Z : Type uZ} (T : CalibratedTube F u Z)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    ∃ (P : ℕ → F.CalibratedSeedWindow u) (W : WindowChartData P),
      ∀ j, ∃ (A : F.CalibratedLevelSeedPatch u)
          (e : A.covector.ker ≃L[ℝ] (W.chartData j).p.ker),
        A.openLabels = e ⁻¹' (W.chartData j).V ∧
          A.labels = e ⁻¹' ((W.chartData j).V ∩
            (W.chartData j).σ ⁻¹' (W.parentCore j)) ∧
            (∀ w t, A.curve w t =
              (W.chartData j).Γ ((W.chartData j).σ (e w)) t) ∧
              A.level = (W.chartData j).q :=
  exists_levelSeedPatches_of_interior_nonempty hF hcomplete hu (T.interior_nonempty hu)

end OTSelector.Reconstruction
