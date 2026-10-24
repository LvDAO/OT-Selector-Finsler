import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CompletePhaseJetMatching

/-!
# Actual phase jets of retained original level-seed patches

The retained C1,1 presentation identifies the patch's own initial momentum. At a
point where its original extension gradient is differentiable, this gives the
actual initial phase jet. Matching this jet with a complete comparison family
preserves the central curve and all chart-legal joint phase derivatives.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Choose one of the original C1,1 presentations already retained by the patch. -/
def c11Data (S : CalibratedLevelSeedPatch F u) :
    C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve :=
  Classical.choice S.c11_presentation

/-- On the whole open label domain, the actual patch momentum is the retained
extension covector evaluated along its original section. -/
theorem initial_phase_eq (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    {w : S.covector.ker} (hw : w ∈ S.openLabels) :
    F.chartMomentumFamily D.initialChart S.curve (w, 0) =
      (D.position w, fderiv ℝ D.potential (D.position w)) := by
  calc
    F.chartMomentumFamily D.initialChart S.curve (w, 0) =
        F.chartMomentumFamily D.initialChart (fun z ↦ D.ambient (D.position z)) (w, 0) :=
      congrArg (fun Γ ↦ F.chartMomentumFamily D.initialChart Γ (w, 0)) D.curve_eq
    _ = _ := D.ambient_momentum (D.position w) (D.position_domain hw)

/-- The derivative of the original covector along the actual labels supplies the
patch phase derivative. No ambient second derivative or slice density is needed. -/
theorem initial_phase_hasFDerivAt_of_covector (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    {w : S.covector.ker} (hw : w ∈ S.openLabels)
    {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ D.potential (D.position z)) Q w) :
    HasFDerivAt (fun z ↦ F.chartMomentumFamily D.initialChart S.curve (z, 0))
      ((fderiv ℝ D.position w).prod Q) w := by
  have hsc := D.position_contDiff.contDiffAt (S.openLabels_open.mem_nhds hw)
  have hs := (hsc.differentiableAt one_ne_zero).hasFDerivAt
  apply (hs.prodMk hQ).congr_of_eventuallyEq
  filter_upwards [S.openLabels_open.mem_nhds hw] with z hz
  exact S.initial_phase_eq D hz

/-- Differentiating the retained original covector supplies the actual initial
phase derivative of the patch, without any derivative premise on the flow. -/
theorem initial_phase_hasFDerivAt (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    {w : S.covector.ker} (hw : w ∈ S.openLabels)
    {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hH : HasFDerivAt (fderiv ℝ D.potential) H (D.position w)) :
    let R := fderiv ℝ D.position w
    HasFDerivAt (fun z ↦ F.chartMomentumFamily D.initialChart S.curve (z, 0))
      (R.prod (H.comp R)) w := by
  have hsc := D.position_contDiff.contDiffAt (S.openLabels_open.mem_nhds hw)
  have hs := (hsc.differentiableAt one_ne_zero).hasFDerivAt
  exact S.initial_phase_hasFDerivAt_of_covector D hw (hH.comp w hs)

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]

/-- The patch and any complete family matching its actual initial phase jet have
the same central curve and the same ordinary joint phase jet at every legal time.
All original-family initial data come from the retained C1,1 presentation. -/
theorem same_phase_firstJet_of_initial_phase (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {w : S.covector.ker} (hw : w ∈ S.openLabels)
    {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ D.potential (D.position z)) Q w)
    {B : Set S.covector.ker} (hB : IsOpen B) (hwB : w ∈ B)
    (hBsub : B ⊆ S.openLabels) {Γ : S.covector.ker → ℝ → M}
    (hEL : ∀ z ∈ B, F.IsEulerLagrangeOn (Γ z) univ)
    (hsource : ∀ z ∈ B, Γ z 0 ∈ (extChartAt 𝓘(ℝ, E) D.initialChart).source)
    (hjet : HasFDerivAt (fun z ↦ F.chartMomentumFamily D.initialChart Γ (z, 0))
      ((fderiv ℝ D.position w).prod Q) w)
    (hvalue : F.chartMomentumFamily D.initialChart Γ (w, 0) =
      (D.position w, fderiv ℝ D.potential (D.position w))) :
    S.curve w = Γ w ∧ ∀ (terminal : M) (t : ℝ),
      Γ w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
      HasFDerivAt (F.chartMomentumFamily terminal S.curve)
        (fderiv ℝ (F.chartMomentumFamily terminal Γ) (w, t)) (w, t) ∧
      HasFDerivAt (F.chartMomentumFamily terminal Γ)
        (fderiv ℝ (F.chartMomentumFamily terminal Γ) (w, t)) (w, t) := by
  have hSEL (z : S.covector.ker) (hz : z ∈ B) :
      F.IsEulerLagrangeOn (S.curve z) univ := by
    rw [D.curve_eq]
    exact D.ambient_complete (D.position z) (D.position_domain (hBsub hz))
  have hSsource (z : S.covector.ker) (hz : z ∈ B) :
      S.curve z 0 ∈ (extChartAt 𝓘(ℝ, E) D.initialChart).source := by
    have hc : S.curve z 0 = D.ambient (D.position z) 0 :=
      congrFun (congrFun D.curve_eq z) 0
    rw [hc, D.ambient_initial (D.position z) (D.position_domain (hBsub hz))]
    exact (extChartAt 𝓘(ℝ, E) D.initialChart).map_target
      (D.domain_target (D.position_domain (hBsub hz)))
  exact hF.same_firstJet_of_complete_initial_phase hcomplete D.initialChart 0 hB hwB
    hSEL hEL hSsource hsource (S.initial_phase_hasFDerivAt_of_covector D hw hQ) hjet
    ((S.initial_phase_eq D hw).trans hvalue.symm)

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
