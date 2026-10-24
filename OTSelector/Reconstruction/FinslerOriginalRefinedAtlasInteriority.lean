import OTSelector.Reconstruction.FinslerOriginalTileDataPopulationInputs
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedC11
import OTSelector.Reconstruction.FinslerSeedRootPartition
import Mathlib.Order.Disjointed

/-!
# Refined atlas cores and the retention owner selection

The window coverage reduction of the upper pressure lane left two local inputs:
core interiority of the C1,1 presentation (equivalently, a ball of retained labels
around the zero label) and the retention of cube-coordinate roots in the selected
disjoint piece.  This module closes them as far as the producer geometry allows
and isolates the exact remaining construction gap.

## The exact interiority gap

The retained labels of a seed are the label domain intersected with the preimage
of the core.  Hence a metric ball of labels around zero is contained in the labels
**iff** the section image of a metric ball around zero is contained in the core.
This is strictly weaker than metric interiority of the core at the section point
and is exactly the statement needed by the cube coverage; both directions are
proved here.  In particular the interiority input is *equivalent* to the label
ball input, so no further information is lost by passing to the label statement.

## Refined ball cores are admissible

The C1,1 extension machinery of the calibrated window producer accepts an
arbitrary compact chart set.  Running it on a compact chart ball produces C1,1
potential data matching the original potential on a **ball core** around any
prescribed point of the ball (after an arbitrarily small shift off the boundary of
the covering ball).  Thus the atlas can be refined so that its cores are chart
neighborhoods of the section point, which is precisely the interiority needed for
the label ball.

## Retention: the owning window

The retained reference roots are disjointified among the windows: every root is
owned by exactly one window.  Hence the first-ownership selection of the retention
condition is canonical, and retention reduces to the pointwise finite-nonzero
original reference intensity at the retained root, which is the remaining
population-density input.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open Module
open MeasureTheory.Measure
open Metric
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## The exact interiority gap of the label ball -/

/-- **The section image of a small ball lies in the core.**  A ball of retained
labels around the zero label implies that the section image of a ball around zero
is contained in the core.  This is the precise geometric content of the
interiority input. -/
theorem section_image_ball_of_labels_ball
    (A : F.CalibratedLevelSeedPatch u)
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      A.covector A.level A.openLabels A.labels A.curve)
    (h : ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : A.covector.ker) r ⊆ A.labels) :
    ∃ r : ℝ, 0 < r ∧ D.position '' Metric.ball (0 : A.covector.ker) r ⊆ D.core := by
  obtain ⟨r, hr, hsub⟩ := h
  refine ⟨r, hr, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  exact (D.labels_eq ▸ hsub hw).2

/-- **A label ball from the section image.**  Conversely, if the section image of
a small ball around zero lies in the core, then a (possibly smaller) ball of
labels around zero is retained, since the label domain is open and contains
zero. -/
theorem labels_ball_of_section_image_ball
    (A : F.CalibratedLevelSeedPatch u)
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      A.covector A.level A.openLabels A.labels A.curve)
    (himage : ∃ r : ℝ, 0 < r ∧
      D.position '' Metric.ball (0 : A.covector.ker) r ⊆ D.core) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : A.covector.ker) r ⊆ A.labels := by
  obtain ⟨r, hr, hsub⟩ := himage
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp A.openLabels_open 0 D.zero_mem
  refine ⟨min r δ, lt_min hr hδ, ?_⟩
  intro w hw
  rw [mem_ball_zero_iff] at hw
  have hwr : w ∈ Metric.ball (0 : A.covector.ker) r := by
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le hw (min_le_left _ _)
  have hwU : w ∈ A.openLabels := hδU (by
    rw [mem_ball_zero_iff]
    exact lt_of_lt_of_le hw (min_le_right _ _))
  rw [D.labels_eq]
  exact ⟨hwU, hsub ⟨w, hwr, rfl⟩⟩

/-- **The exact interiority gap.**  The label ball input and the section-image-core
input are equivalent: the coverage of the cube by the retained labels is exactly
the statement that the section image of a small ball around zero lies in the
compact core. -/
theorem labels_ball_iff_section_image_ball
    (A : F.CalibratedLevelSeedPatch u)
    (D : OTSelector.Geometry.ContinuousFinslerNorm.C11LevelSeedPresentation F u
      A.covector A.level A.openLabels A.labels A.curve) :
    (∃ r : ℝ, 0 < r ∧ Metric.ball (0 : A.covector.ker) r ⊆ A.labels) ↔
      ∃ r : ℝ, 0 < r ∧ D.position '' Metric.ball (0 : A.covector.ker) r ⊆ D.core :=
  ⟨section_image_ball_of_labels_ball A D, labels_ball_of_section_image_ball A D⟩

/-! ## Refined ball cores are admissible for the C1,1 producer -/

/-- **A compact chart ball carries the C1,1 data on a ball core.**

This is the producer-level refinement behind core interiority.  Running the
calibrated C1,1 cover construction on a compact chart ball, one obtains a smaller
closed *ball* core (a chart-neighbourhood core, hence a core with interior) on
which the C1,1 potential matches the original potential and its derivative and
differentiates it.  Consequently the atlas may be refined so that its cores are
chart balls, and the label ball input of the cube coverage follows. -/
theorem exists_ball_core_C11_data
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {u : M → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hu : let _instRefinedCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {y : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hyball : closedBall y ρ ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hreach : let _instRefinedCoreReach : MetricSpace M := F.metricSpace
      ∀ x ∈ closedBall y ρ, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ) :
    ∃ (y' : E) (σ : ℝ) (G : E → ℝ) (L : ℝ≥0), 0 < σ ∧
      closedBall y' σ ⊆ closedBall y ρ ∧
      ContDiff ℝ 1 G ∧ HasCompactSupport G ∧ LipschitzWith L (fderiv ℝ G) ∧
      EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (closedBall y' σ) ∧
      EqOn (fderiv ℝ G) (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm))
        (closedBall y' σ) ∧
      ∀ x ∈ closedBall y' σ,
        HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x := by
  let _instRefinedCoreMetric : MetricSpace M := F.metricSpace
  obtain ⟨r, hr, J, hcover, hdata⟩ :=
    hF.exists_finite_calibrated_C11_cover hcomplete old
      (isCompact_closedBall y ρ) hyball hδ hu hreach
  obtain ⟨q, hqJ, hyq⟩ := mem_iUnion₂.mp (hcover (mem_closedBall_self hρ.le))
  set R : ℝ := r / 8 with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  set ε : ℝ := min (ρ / 2) (R / 2) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hερ : ε ≤ ρ / 2 := min_le_left _ _
  have hεR₂ : ε ≤ R / 2 := min_le_right _ _
  have hεRlt : ε / R < 1 := by
    rw [div_lt_one hR]; linarith
  have hyqR : dist y q ≤ R := by simpa only [mem_closedBall] using hyq
  let y' : E := y + (ε / R) • (q - y)
  have hεRpos : 0 < ε / R := div_pos hε hR
  have hyy' : ‖y' - y‖ ≤ ε := by
    have h1 : y' - y = (ε / R) • (q - y) := by simp only [y', add_sub_cancel_left]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hεRpos]
    have hqy : ‖q - y‖ ≤ R := by
      rw [← dist_eq_norm, dist_comm]; exact hyqR
    calc ε / R * ‖q - y‖ ≤ ε / R * R :=
          mul_le_mul_of_nonneg_left hqy hεRpos.le
      _ = ε := by field_simp
  have hyq' : ‖y' - q‖ ≤ R - ε := by
    have h1 : y' - q = (1 - ε / R) • (y - q) := by
      simp only [y']
      rw [show y + (ε / R) • (q - y) - q = (y - q) + (ε / R) • (q - y) by abel]
      rw [show q - y = -(y - q) by abel]
      rw [smul_neg, ← sub_eq_add_neg, sub_smul, one_smul]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < 1 - ε / R)]
    have hqy : ‖y - q‖ ≤ R := by rw [← dist_eq_norm]; exact hyqR
    calc (1 - ε / R) * ‖y - q‖ ≤ (1 - ε / R) * R :=
          mul_le_mul_of_nonneg_left hqy (by linarith)
      _ = R - ε := by field_simp
  obtain ⟨hKc, G, L, hG, hsupp, hcontOn, hLip, hEqG, hEqdG, hFDeriv⟩ := hdata q hqJ
  have hsub : closedBall y' (ε / 2) ⊆ closedBall y ρ ∩ closedBall q R := by
    intro z hz
    have hz' : dist z y' ≤ ε / 2 := by simpa only [mem_closedBall] using hz
    have hdyy : dist y' y = ‖y' - y‖ := dist_eq_norm y' y
    have hdyq : dist y' q = ‖y' - q‖ := dist_eq_norm y' q
    constructor
    · rw [mem_closedBall]
      calc dist z y ≤ dist z y' + dist y' y := dist_triangle _ _ _
        _ = dist z y' + ‖y' - y‖ := by rw [hdyy]
        _ ≤ ε / 2 + ε := by linarith [hz', hyy']
        _ ≤ ρ := by linarith [hερ, hρ]
    · rw [mem_closedBall]
      calc dist z q ≤ dist z y' + dist y' q := dist_triangle _ _ _
        _ = dist z y' + ‖y' - q‖ := by rw [hdyq]
        _ ≤ ε / 2 + (R - ε) := by linarith [hz', hyq']
        _ = R - ε / 2 := by ring
        _ ≤ R := by linarith
  refine ⟨y', ε / 2, G, L, by positivity, ?_, hG, hsupp, hLip, ?_, ?_, ?_⟩
  · intro z hz
    exact (hsub hz).1
  · exact hEqG.mono hsub
  · exact hEqdG.mono hsub
  · intro x hx
    exact hFDeriv x (hsub hx)

/-! ## Retention: the unique owning window of a retained root -/

/-- **Every retained root is owned by a window.**  The retained reference roots
are exhausted by their disjointification among the windows, so every retained root
belongs to at least one selected piece. -/
theorem exists_owner_piece (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) {z : Z}
    (hz : z ∈ ⋃ i, populationSeedReferenceRoots (P i).seed a (κ i) lambda) :
    ∃ j, z ∈ populationSeedRootPiece P a κ lambda j := by
  have h : z ∈ ⋃ i, populationSeedRootPiece P a κ lambda i := by
    rw [show (fun i => populationSeedRootPiece P a κ lambda i) =
        (fun i => disjointed
          (fun i => populationSeedReferenceRoots (P i).seed a (κ i) lambda) i) from rfl,
      iUnion_disjointed]
    exact hz
  exact mem_iUnion.mp h

/-- **The owning window is unique.**  Distinct selected pieces are disjoint, so a
retained root cannot be owned by two windows. -/
theorem owner_piece_unique (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) {z : Z}
    {i j : ℕ} (hi : z ∈ populationSeedRootPiece P a κ lambda i)
    (hj : z ∈ populationSeedRootPiece P a κ lambda j) : i = j :=
  populationSeedRootPiece_index_eq_of_mem P a κ lambda hi hj

/-- **First-ownership selection.**  Every retained root has a unique owning window;
this is the canonical selection of the window for a tile, closing the
first-ownership part of the retention condition. -/
theorem existsUnique_owner_piece (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) {z : Z}
    (hz : z ∈ ⋃ i, populationSeedReferenceRoots (P i).seed a (κ i) lambda) :
    ∃! j, z ∈ populationSeedRootPiece P a κ lambda j :=
  have ⟨j, hj⟩ := exists_owner_piece P a κ lambda hz
  ⟨j, hj, fun k hk => owner_piece_unique P a κ lambda hk hj⟩

/-- **Retention structure of an owning window.**  A label of a selected piece has
its original root in the finite-nonzero reference roots of that window and is not
owned by any earlier window. -/
theorem piece_root_and_firstOwner (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z) {j : ℕ} {z : Z}
    (hz : z ∈ populationSeedRootPiece P a κ lambda j) :
    z ∈ populationSeedReferenceRoots (P j).seed a (κ j) lambda ∧
      ∀ i < j, z ∉ populationSeedReferenceRoots (P i).seed a (κ i) lambda := by
  have h' : z ∈ disjointed
      (fun i => populationSeedReferenceRoots (P i).seed a (κ i) lambda) j := hz
  rw [disjointed_eq_inter_compl] at h'
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff] at h'
  exact ⟨h'.1, fun i hi => h'.2 i hi⟩

end OTSelector.Reconstruction
