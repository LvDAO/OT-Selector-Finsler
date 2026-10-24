import OTSelector.Reconstruction.FinslerOriginalWindowChartUnconditional
import OTSelector.Geometry.Finsler.Geodesic.ConstantSpeedDistance

/-!
# The paper-side calibrated ray-tube hypothesis and the interiority input

`FinslerOriginalWindowChartUnconditional.lean` proved that the window-chart endgame
`Nonempty (WindowChartData P)` is *equivalent* to nonempty manifold interior of
the calibrated interior `chartInterior F u` (the Borel set `T_phi^o` of the
paper).  This file formalises the paper-side hypothesis that supplies such an
interior and wires it into the endgame.

## What the paper assumes (main.tex)

* Theorem 1.1 (main.tex, lines 90-113) assumes only: connected complete smooth
  reversible strongly convex Finsler manifold of dimension `d >= 6`, smooth
  positive volume, probability measures with nonnegative Lipschitz densities and
  compact disjoint supports; it states explicitly that no
  "raywise interior-support condition is assumed".
* `T_phi^o` is introduced only as a *Borel* set with
  `mu(T_phi^o) = nu(T_phi^o) = 1` (main.tex, lines 350-370); no openness and no
  nonempty interior is asserted.
* Section "Local geometry of calibrated Finsler ray tubes" (main.tex, lines
  1063-1075) states the calibrated tube assumption: a smooth coordinate
  diffeomorphism `X : J x B -> M` with `B` open and
  `phi (X (r,z)) = r`, `Ftilde (r,z;1,0) = 1`.  The paper calls it
  "a local geometric hypothesis; we do not assume that arbitrary marginals
  already supply such tubes."
* Section "Almost-everywhere ray geometry" (main.tex, around line 1136) replaces
  the smooth tube by countably many Assouline ray clusters with *Borel* domains
  and density points; the paper's general argument only uses a.e. rays.

## What this file proves

`CalibratedRayTube` is the paper's calibrated tube hypothesis in the metric form
consumed by the reconstruction: an open nonempty region, a complete ray through
each of its points, unit Finsler radial speed, globally minimizing short
subsegments and the clock identity `u (curve x t) = u x + t`.  These are exactly
the conclusions of the paper's tube computation (Lemma "The Hessian of the actual
length distance"): calibration forces the radial segment to be the global
minimizer, and `phi` increases at unit speed along it.

* `CalibratedRayTube.region_subset_chartInterior`: every point of a calibrated
  tube lies in the calibrated interior.  The distance formula follows from
  `F.dist_eq_mul_abs_sub_of_locally_minimizing` and then symmetric partners at
  half the tube radius are explicit.
* `CalibratedRayTube.interior_nonempty`: the tube yields nonempty manifold
  interior of `chartInterior F u`.
* `exists_chartBall_of_calibratedRayTube`,
  `exists_chartBall_uniformReach_of_calibratedRayTube` and
  `exists_windowChartData_of_calibratedRayTube`: the paper-side hypothesis
  supplies, in order, the earlier chart-ball input, the uniform two-sided reach
  input, and `Nonempty (WindowChartData P)` for a window family.

## Precise mismatch with the paper

The paper does not assume interiority of `T_phi^o`; its general theorem only
assumes the data listed above and then uses a.e. Borel ray clusters.  The
smooth calibrated tube is an explicitly conditional "local geometric hypothesis"
(and the tube data used here are even its metric consequences, not its smooth
diffeomorphism `X`).  Hence this file closes the endgame *conditionally on that
local geometric hypothesis*: the literal hypothesis-free form of the task is not
derivable from the paper's general assumptions, and the remaining gap is exactly
the gap between the paper's a.e. Borel ray-cluster argument and the open chart
domain required by `WindowChartData`.
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

/-! ## The paper-side calibrated ray-tube structure -/

/-- **The calibrated ray-tube hypothesis of the paper** (main.tex, "Local geometry
of calibrated Finsler ray tubes"), in the metric form used by the reconstruction.

The tube covers a nonempty open region.  Through each of its points runs a
complete ray, Euler--Lagrange on all of `ℝ`, with unit Finsler radial speed on a
symmetric interval, globally minimizing short subsegments on that interval, and
the calibration clock `u (curve x t) = u x + t`.  These are the consequences of
the paper's tube data `X (r,z)` with `phi (X (r,z)) = r` and
`Ftilde (r,z;1,0) = 1` proved in the paper's Hessian lemma; the smooth
coordinate parametrisation itself is not consumed by the reconstruction. -/
structure CalibratedRayTube (F : ContinuousFinslerNorm E M) (u : M → ℝ) where
  /-- The open set of points covered by the tube. -/
  region : Set M
  region_open : IsOpen region
  region_nonempty : region.Nonempty
  /-- The radial calibrated curve through a point of the region. -/
  curve : M → ℝ → M
  curve_zero : ∀ x ∈ region, curve x 0 = x
  el : ∀ x ∈ region, F.IsEulerLagrangeOn (curve x) univ
  /-- Radius of the symmetric interval on which the ray is calibrated. -/
  radius : M → ℝ
  radius_pos : ∀ x ∈ region, 0 < radius x
  speed_one : ∀ x ∈ region, ∀ t ∈ Ioo (-(radius x)) (radius x),
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (curve x) ⟨t, (1 : ℝ)⟩) = 1
  locally_minimizing : ∀ x ∈ region, ∀ a b : ℝ, a ≤ b →
    a ∈ Icc (-(radius x)) (radius x) → b ∈ Icc (-(radius x)) (radius x) →
    (letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm;
      F.lengthEDist (curve x a) (curve x b) =
        Manifold.pathELength 𝓘(ℝ, E) (curve x) a b)
  clock : ∀ x ∈ region, ∀ t ∈ Icc (-(radius x)) (radius x),
    u (curve x t) = u x + t

/-! ## Membership in the calibrated interior -/

/-- **Every point of a calibrated ray tube is a calibrated interior point.**  The
unit-speed globally minimizing radial segment gives the distance formula
`dist x (curve x t) = |t|`, and the clock identity then produces two-sided
calibrated partners at distance `radius x / 2`. -/
theorem CalibratedRayTube.region_subset_chartInterior (H : CalibratedRayTube F u) :
    H.region ⊆ chartInterior F u := by
  intro x hx
  letI : MetricSpace M := F.metricSpace
  letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  have hr : 0 < H.radius x := H.radius_pos x hx
  have hdist : ∀ t ∈ Icc (-(H.radius x)) (H.radius x),
      dist x (H.curve x t) = |t| := by
    have hform := F.dist_eq_mul_abs_sub_of_locally_minimizing
      (c := H.curve x) (t₀ := 0) (δ := H.radius x) (s := 1) hr ?_ ?_
    · intro t ht
      have h := hform t (by simpa using ht)
      rw [H.curve_zero x hx] at h
      simpa using h
    · intro t ht
      exact H.speed_one x hx t (by simpa using ht)
    · intro a ha b hb hab
      exact H.locally_minimizing x hx a b hab (by simpa using ha) (by simpa using hb)
  have hhalf : H.radius x / 2 ∈ Icc (-(H.radius x)) (H.radius x) :=
    ⟨by linarith, by linarith⟩
  have hneghalf : -(H.radius x / 2) ∈ Icc (-(H.radius x)) (H.radius x) :=
    ⟨by linarith, by linarith⟩
  have hprev : dist (H.curve x (-(H.radius x / 2))) x = H.radius x / 2 := by
    have h := hdist (-(H.radius x / 2)) hneghalf
    rw [dist_comm, h, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < H.radius x / 2)]
  have hnext : dist x (H.curve x (H.radius x / 2)) = H.radius x / 2 := by
    have h := hdist (H.radius x / 2) hhalf
    rwa [abs_of_pos (by linarith : (0 : ℝ) < H.radius x / 2)] at h
  have hclock_prev : u x - u (H.curve x (-(H.radius x / 2))) = H.radius x / 2 := by
    have h := H.clock x hx (-(H.radius x / 2)) hneghalf
    linarith
  have hclock_next : u (H.curve x (H.radius x / 2)) - u x = H.radius x / 2 := by
    have h := H.clock x hx (H.radius x / 2) hhalf
    linarith
  change x ∈ OTSelector.Geometry.calibratedInterior u
  refine ⟨⟨H.curve x (-(H.radius x / 2)), ?_, ?_⟩,
    ⟨H.curve x (H.radius x / 2), ?_, ?_⟩⟩
  · exact dist_pos.mp (by rw [hprev]; linarith)
  · exact hclock_prev.trans hprev.symm
  · exact dist_pos.mp (by rw [hnext]; linarith)
  · exact hclock_next.trans hnext.symm

/-- **A calibrated ray tube has nonempty manifold interior.** -/
theorem CalibratedRayTube.interior_nonempty (H : CalibratedRayTube F u) :
    (interior (chartInterior F u)).Nonempty := by
  obtain ⟨x, hx⟩ := H.region_nonempty
  exact ⟨x, interior_maximal H.region_subset_chartInterior H.region_open hx⟩

/-! ## The earlier geometric inputs from the paper-side hypothesis -/

/-- **A chart ball inside the calibrated interior from a calibrated ray tube.** -/
theorem exists_chartBall_of_calibratedRayTube (H : CalibratedRayTube F u) :
    ∃ (old : M) (y : E) (rho : ℝ), 0 < rho ∧
      closedBall y rho ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      ∀ z ∈ closedBall y rho,
        (extChartAt 𝓘(ℝ, E) old).symm z ∈ chartInterior F u := by
  obtain ⟨x, hx⟩ := H.interior_nonempty
  exact exists_chartBall_of_mem_interior (F := F) (u := u) hx

/-- **Uniform two-sided reach on a chart ball from a calibrated ray tube.**  This is
the geometric input consumed by the C1,1 ball-core refinement. -/
theorem exists_chartBall_uniformReach_of_calibratedRayTube
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (H : CalibratedRayTube F u) :
    ∃ (old : M) (y' : E) (rho' delta : ℝ), 0 < rho' ∧ 0 < delta ∧
      CalibratedPartners F u old delta (closedBall y' rho') := by
  obtain ⟨old, y, rho, hrho, hyball, hinterior⟩ :=
    exists_chartBall_of_calibratedRayTube (F := F) (u := u) H
  have hrec : (letI : MetricSpace M := F.metricSpace;
      ∀ z ∈ closedBall y rho,
        (extChartAt 𝓘(ℝ, E) old).symm z ∈
          OTSelector.Geometry.calibratedInterior u) := by
    intro z hz
    exact hinterior z hz
  obtain ⟨y', rho', delta, hrho', hdelta, -, hpartners⟩ :=
    exists_chartBall_uniformReach (F := F) (u := u) hcomplete old hu hrho hyball hrec
  exact ⟨old, y', rho', delta, hrho', hdelta, hpartners⟩

/-! ## The unconditional chart-window construction -/

/-- **`WindowChartData` from the paper-side calibrated ray-tube hypothesis.**  No
further geometric input is needed once one calibrated ray tube is available: the
tube gives nonempty manifold interior of the calibrated interior, which is
equivalent to the endgame by `windowChartData_iff_interior_nonempty`. -/
theorem exists_windowChartData_of_calibratedRayTube
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (H : CalibratedRayTube F u) :
    ∃ P : ℕ → F.CalibratedSeedWindow u, Nonempty (WindowChartData P) :=
  exists_windowChartData_of_interior (F := F) (u := u) hF hcomplete hu H.interior_nonempty

end OTSelector.Reconstruction
