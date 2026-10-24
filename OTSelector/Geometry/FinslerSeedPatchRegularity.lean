import OTSelector.Geometry.FinslerSeedPatchDifferentiability
import OTSelector.Analysis.Calculus.PullbackGradientSymmetry

/-!
# Actual isotropic normal jets of retained level seeds

The original level identity annihilates every section tangent direction. The
retained section is an immersion on its whole open domain. At almost every label,
the actual covector derivative therefore supplies an injective isotropic phase
jet, directly in the original label space.
-/

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The actual potential covector annihilates the section derivative at every
point of its open label domain. -/
theorem initial_covector_comp_position_eq_zero (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    {w : S.covector.ker} (hw : w ∈ S.openLabels) :
    (fderiv ℝ D.potential (D.position w)).comp (fderiv ℝ D.position w) = 0 := by
  have hs := (D.position_contDiff.contDiffAt
    (S.openLabels_open.mem_nhds hw)).differentiableAt one_ne_zero
  have hG := (D.potential_contDiff.differentiable one_ne_zero (D.position w)).hasFDerivAt
  have hd := hG.comp w hs.hasFDerivAt
  have hc : HasFDerivAt (fun _ : S.covector.ker ↦ (S.level : ℝ))
      ((fderiv ℝ D.potential (D.position w)).comp (fderiv ℝ D.position w)) w := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [S.openLabels_open.mem_nhds hw] with z hz
    exact (D.level_eq z hz).symm
  exact hc.unique (hasFDerivAt_const _ w)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Differentiability of the actual pulled-back covector makes the original
phase jet isotropic, with no ambient Hessian assumption. -/
theorem initial_phase_isotropic_of_covector (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    {w : S.covector.ker} (hw : w ∈ S.openLabels)
    {Q : S.covector.ker →L[ℝ] E →L[ℝ] ℝ}
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ D.potential (D.position z)) Q w)
    (ξ η : S.covector.ker) :
    canonicalPhasePairing ((fderiv ℝ D.position w).prod Q ξ)
      ((fderiv ℝ D.position w).prod Q η) = 0 :=
  canonicalPhasePairing_pullbackGradient_eq_zero D.potential_contDiff.contDiffAt
    (D.position_contDiff.contDiffAt (S.openLabels_open.mem_nhds hw)) hQ ξ η

/-- Actual initial jets on the original labels are almost everywhere normal,
injective and isotropic; every derivative appearing here is the actual derivative. -/
theorem ae_initial_phase_regular (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict S.labels,
      let R := fderiv ℝ D.position w
      let Q := fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w
      w ∈ S.labels ∧ Function.Injective R ∧
        (fderiv ℝ D.potential (D.position w)).comp R = 0 ∧
        HasFDerivAt (fun z ↦ fderiv ℝ D.potential (D.position z)) Q w ∧
        HasFDerivAt (fun z ↦ F.chartMomentumFamily D.initialChart S.curve (z, 0))
          (R.prod Q) w ∧
        ∀ ξ η, canonicalPhasePairing (R.prod Q ξ) (R.prod Q η) = 0 := by
  filter_upwards [S.ae_differentiableAt_initial_covector_labels D m,
    ae_restrict_mem S.labels_measurable] with w hQ hw
  have hwU := S.labels_subset hw
  exact ⟨hw, D.position_immersion w hwU,
    S.initial_covector_comp_position_eq_zero D hwU, hQ.hasFDerivAt,
    S.initial_phase_hasFDerivAt_of_covector D hwU hQ.hasFDerivAt,
    S.initial_phase_isotropic_of_covector D hwU hQ.hasFDerivAt⟩

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
