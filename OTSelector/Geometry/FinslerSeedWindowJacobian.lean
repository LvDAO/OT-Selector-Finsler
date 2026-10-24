import OTSelector.Geometry.FinslerSeedWindowInteriorRank
import OTSelector.Geometry.Finsler.PositionJacobianRank
import OTSelector.Geometry.FinslerPhaseJetJacobianTransfer

/-!
# Positive original Jacobians throughout calibrated windows

The actual retained level seeds, endpoint calibration and label density produce
positive physical Jacobians at every interior time. The complete smooth comparison
uses precisely the same central curve and actual phase jet.
-/

open Set Filter MeasureTheory Manifold
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The same actual comparison and original window have positive physical
Jacobians at every interior time, on one full-measure set of screened labels. -/
theorem ae_exists_comparison_positive_jacobian (P : CalibratedSeedWindow F u)
    (D : C11LevelSeedPresentation F u P.seed.covector P.seed.level
      P.seed.openLabels P.seed.labels P.seed.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedJacobianLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure P.seed.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict P.labels,
      let R := fderiv ℝ D.position w
      let Q := fderiv ℝ (fun z ↦ fderiv ℝ D.potential (D.position z)) w
      let p := (D.position w, fderiv ℝ D.potential (D.position w))
      w ∈ P.labels ∧
        ∃ C : F.SmoothPhaseJetComparison D.initialChart 0 w p R Q,
          C.labels ⊆ P.seed.openLabels ∧ P.seed.curve w = C.curve w ∧
          (∀ (terminal : M) (t : ℝ),
            P.seed.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
            HasFDerivAt (F.chartMomentumFamily terminal P.seed.curve)
              (fderiv ℝ (F.chartMomentumFamily terminal C.curve) (w, t)) (w, t) ∧
            HasFDerivAt (F.chartMomentumFamily terminal C.curve)
              (fderiv ℝ (F.chartMomentumFamily terminal C.curve) (w, t)) (w, t)) ∧
          ∀ (terminal : M) (t : ℝ), t ∈ Ioo (P.left : ℝ) P.right →
            P.seed.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source →
            0 < parameterizedJacobian
              (fun q : ℝ × P.seed.covector.ker ↦
                extChartAt 𝓘(ℝ, E) terminal (P.seed.curve q.2 q.1))
              P.seed.normalization (t, w) := by
  filter_upwards [P.ae_exists_comparison_interior_position_rank D hF hcomplete hu m]
    with w hdata
  obtain ⟨hw, C, hsub, hcurve, hjet, hrank⟩ := hdata
  refine ⟨hw, C, hsub, hcurve, hjet, ?_⟩
  intro terminal t ht hlegal
  obtain ⟨h₁, h₂⟩ := hjet terminal t hlegal
  have hcomparisonLegal : C.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source := by
    rwa [← hcurve]
  have hline : HasFDerivAt (fun z : P.seed.covector.ker ↦ (z, t))
      ((ContinuousLinearMap.id ℝ P.seed.covector.ker).prod
        (0 : P.seed.covector.ker →L[ℝ] ℝ)) w :=
    (hasFDerivAt_id (𝕜 := ℝ) w).prodMk (hasFDerivAt_const t w)
  have hlabelEq : fderiv ℝ
      (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (P.seed.curve z t)) w =
      fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (C.curve z t)) w := by
    have hs₁ := h₁.fst.comp w hline
    have hs₂ := h₂.fst.comp w hline
    exact hs₁.fderiv.trans hs₂.fderiv.symm
  have hcomparisonRank : Function.Injective (fderiv ℝ
      (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (C.curve z t)) w) := by
    rw [← hlabelEq]
    exact hrank terminal t ht hlegal
  rw [F.parameterizedJacobian_eq_of_chartMomentum_same_firstJet terminal h₁ h₂]
  exact hF.parameterizedJacobian_pos_of_position_rank terminal
    (C.complete w C.anchor_mem t (mem_univ _)) hcomparisonLegal h₂.fst.differentiableAt
    hcomparisonRank (C.normal terminal t hcomparisonLegal) P.seed.normalization

/-- Actual readout Jacobians are positive at every allowed interior time for
almost every screened original label. -/
theorem ae_readout_jacobian_pos (P : CalibratedSeedWindow F u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instReadoutJacobianLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (m : Measure P.seed.covector.ker) [m.IsAddHaarMeasure] :
    ∀ᵐ w ∂m.restrict P.labels, ∀ t : ℝ, (t, w) ∈ P.domain →
      0 < parameterizedJacobian P.readout P.seed.normalization (t, w) := by
  filter_upwards [P.ae_exists_comparison_positive_jacobian P.seed.c11Data hF hcomplete hu m]
    with w hdata
  obtain ⟨_, C, _, _, _, hpos⟩ := hdata
  intro t ht
  exact hpos (P.toManifold P.center) t ht.2.1 (P.mapsTo_chart ht.1)

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow
