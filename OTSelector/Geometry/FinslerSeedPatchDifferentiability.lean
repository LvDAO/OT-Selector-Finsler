import OTSelector.Geometry.FinslerSeedPatchPhaseJet
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Topology.Bases

/-!
# Almost-everywhere actual phase jets on original seed labels

The retained C1 section is locally Lipschitz, and its original extension gradient
is globally Lipschitz. Rademacher therefore differentiates their composition in
the label space itself. A countable open cover assembles the result on the full
open label domain, and restriction gives the same actual jets on the core labels.
-/

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

private theorem ae_differentiableAt_lipschitz_comp_contDiffOn
    {W E V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (m : Measure W) [m.IsAddHaarMeasure]
    {U : Set W} (hU : IsOpen U) {s : W → E} (hs : ContDiffOn ℝ 1 s U)
    {g : E → V} {L : ℝ≥0} (hg : LipschitzWith L g) :
    ∀ᵐ w ∂m.restrict U, DifferentiableAt ℝ (g ∘ s) w := by
  classical
  have hlocal (w : U) : ∃ K : ℝ≥0, ∃ N : Set W,
      N ∈ 𝓝 (w : W) ∧ LipschitzOnWith K s N :=
    (hs.contDiffAt (hU.mem_nhds w.2)).exists_lipschitzOnWith
  choose K N hN hLip using hlocal
  have hae (w : U) : ∀ᵐ z ∂m.restrict (interior (N w)),
      DifferentiableAt ℝ (g ∘ s) z := by
    apply (ae_restrict_iff' isOpen_interior.measurableSet).mpr
    have hcomp := hg.comp_lipschitzOnWith ((hLip w).mono interior_subset)
    filter_upwards [hcomp.ae_differentiableWithinAt_of_mem (μ := m)] with z hz hzN
    exact (hz hzN).differentiableAt (isOpen_interior.mem_nhds hzN)
  obtain ⟨T, hT, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun w : U ↦ interior (N w)) (fun _ ↦ isOpen_interior)
  have hsub : U ⊆ ⋃ w ∈ T, interior (N w) := by
    rw [hcover]
    intro w hw
    exact mem_iUnion.mpr ⟨⟨w, hw⟩, mem_interior_iff_mem_nhds.mpr (hN ⟨w, hw⟩)⟩
  exact ae_restrict_of_ae_restrict_of_subset hsub
    ((ae_restrict_biUnion_iff (fun w ↦ interior (N w)) hT
      (fun z ↦ DifferentiableAt ℝ (g ∘ s) z)).mpr (fun w _ ↦ hae w))

namespace ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual initial covector is differentiable for label Haar almost every
point of the original open label domain. -/
theorem ae_differentiableAt_initial_covector (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict S.openLabels,
      DifferentiableAt ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w :=
  ae_differentiableAt_lipschitz_comp_contDiffOn m S.openLabels_open
    D.position_contDiff D.gradient_lipschitz

/-- Restricting to the original core labels preserves actual covector
differentiability; no ambient almost-everywhere statement is sliced. -/
theorem ae_differentiableAt_initial_covector_labels (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict S.labels,
      DifferentiableAt ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w :=
  ae_restrict_of_ae_restrict_of_subset S.labels_subset
    (S.ae_differentiableAt_initial_covector D m)

/-- The original initial phase has its actual derivative almost everywhere on
the open label domain, with the label derivative of the actual covector. -/
theorem ae_initial_phase_hasFDerivAt (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict S.openLabels,
      HasFDerivAt (fun z ↦ F.chartMomentumFamily D.initialChart S.curve (z, 0))
        ((fderiv ℝ D.position w).prod
          (fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w)) w := by
  filter_upwards [S.ae_differentiableAt_initial_covector D m,
    ae_restrict_mem S.openLabels_open.measurableSet] with w hw hwU
  exact S.initial_phase_hasFDerivAt_of_covector D hwU hw.hasFDerivAt

/-- On the original core labels the same actual initial phase derivative holds
for the restricted label Haar measure. -/
theorem ae_initial_phase_hasFDerivAt_labels (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict S.labels,
      HasFDerivAt (fun z ↦ F.chartMomentumFamily D.initialChart S.curve (z, 0))
        ((fderiv ℝ D.position w).prod
          (fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w)) w :=
  ae_restrict_of_ae_restrict_of_subset S.labels_subset (S.ae_initial_phase_hasFDerivAt D m)

end ContinuousFinslerNorm.CalibratedLevelSeedPatch
end OTSelector.Geometry
