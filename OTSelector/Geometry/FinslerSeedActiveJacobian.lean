import OTSelector.Geometry.FinslerSeedWindowJacobian
import OTSelector.Geometry.Finsler.SeedCalibrationSpan

/-!
# One comparison on the entire active interval of an original seed

A countable intersection of density-one label sets handles every rational window
of the fixed seed. The smooth comparison is chosen once from the original initial
jet, so its central curve and all interior physical Jacobians are shared across
all windows up to arbitrary real calibrated endpoints.
-/

open Set Filter Metric MeasureTheory Manifold
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- One comparison and one full-measure original label set work simultaneously on
the entire active time interval, without changing seed, normalization or initial jet. -/
theorem ae_exists_comparison_active_jacobian (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instActiveSeedLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure S.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict S.labels,
      let R := fderiv ℝ D.position w
      let Q := fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w
      let p := (D.position w, fderiv ℝ D.potential (D.position w))
      w ∈ S.labels ∧
        ∃ C : F.SmoothPhaseJetComparison D.initialChart 0 w p R Q,
          C.labels ⊆ S.openLabels ∧ S.curve w = C.curve w ∧
          (∀ (terminal : M) (t : ℝ),
            S.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
            HasFDerivAt (F.chartMomentumFamily terminal S.curve)
              (fderiv ℝ (F.chartMomentumFamily terminal C.curve) (w, t)) (w, t) ∧
            HasFDerivAt (F.chartMomentumFamily terminal C.curve)
              (fderiv ℝ (F.chartMomentumFamily terminal C.curve) (w, t)) (w, t)) ∧
          ∀ (terminal : M) (t : ℝ), t ∈ interior (S.calibrationTimes w) →
            S.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
            0 < parameterizedJacobian
              (fun q : ℝ × S.covector.ker ↦
                extChartAt 𝓘(ℝ, E) terminal (S.curve q.2 q.1)) S.normalization (t, w) := by
  have hdensity (k : S.RationalWindowIndex) : ∀ᵐ w ∂m,
      w ∈ (S.rationalWindow k).labels →
        Tendsto (fun r ↦ m ((S.rationalWindow k).labels ∩ closedBall w r) /
          m (closedBall w r)) (𝓝[>] 0) (𝓝 1) :=
    (ae_restrict_iff' ((S.rationalWindow k).measurableSet_labels hu)).mp
      (Besicovitch.ae_tendsto_measure_inter_div m (S.rationalWindow k).labels)
  have hdensityAll := ae_all_iff.mpr hdensity
  filter_upwards [S.ae_exists_smoothPhaseJetComparison D hF hcomplete m,
    ae_restrict_of_ae hdensityAll] with w hcomparison hdensity
  obtain ⟨hw, C, hsub, hcurve, hjet⟩ := hcomparison
  refine ⟨hw, C, hsub, hcurve, hjet, ?_⟩
  intro terminal t ht hlegal
  rw [← S.iUnion_rationalWindow_timeDomain hF hu hw] at ht
  obtain ⟨k, hk⟩ := mem_iUnion.mp ht
  let P := S.rationalWindow k
  obtain ⟨h₁, h₂⟩ := hjet terminal t hlegal
  have hline : HasFDerivAt (fun z : S.covector.ker ↦ (z, t))
      ((ContinuousLinearMap.id ℝ S.covector.ker).prod
        (0 : S.covector.ker →L[ℝ] ℝ)) w :=
    (hasFDerivAt_id (𝕜 := ℝ) w).prodMk (hasFDerivAt_const t w)
  have hs₁ := h₁.fst.comp w hline
  have hs₂ := h₂.fst.comp w hline
  have hlabelEq : fderiv ℝ
      (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (S.curve z t)) w =
      fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (C.curve z t)) w :=
    hs₁.fderiv.trans hs₂.fderiv.symm
  have hR : Function.Injective (fderiv ℝ
      (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (S.curve z t)) w) :=
    P.injective_position_derivative_of_density_one D hF hcomplete hu m hk.2.2
      (hdensity k hk.2.2) terminal hk.2.1 hlegal
      hs₁.differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have hcomparisonLegal : C.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source := by
    rwa [← hcurve]
  rw [F.parameterizedJacobian_eq_of_chartMomentum_same_firstJet terminal h₁ h₂]
  exact hF.parameterizedJacobian_pos_of_position_rank terminal
    (C.complete w C.anchor_mem t (mem_univ _)) hcomparisonLegal h₂.fst.differentiableAt
    (hlabelEq ▸ hR) (C.normal terminal t hcomparisonLegal) S.normalization

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
