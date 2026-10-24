import OTSelector.Geometry.FinslerSeedActiveJacobian
import OTSelector.Geometry.FinslerPhaseJetJacobianTransfer

/-!
# One actual Jacobi comparison throughout the original active interval

A single complete comparison of the original seed computes every legal graph
position matrix along the full active interval. Its determinant is nonzero in the
interior as a consequence of the original geometry and label density, independently
of rational window choices and without any supplied rank condition.
-/

open Set Filter Matrix Module MeasureTheory Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch

variable {E M V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [DecidableEq ι]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- One complete comparison has nonsingular actual graph-position matrices at all
active interior times, with arbitrary legal charts and graph choices made afterward. -/
theorem ae_exists_comparison_active_graphPosition_regular
    (S : CalibratedLevelSeedPatch F u)
    (D : C11LevelSeedPresentation F u S.covector S.level S.openLabels S.labels S.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instActiveGraphLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
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
          ∀ (terminal : M) (bW : Basis ι ℝ S.covector.ker) (bV : Basis ι ℝ V)
            (A : E ≃L[ℝ] (ℝ × V))
            (e : OpenPartialHomeomorph (S.covector.ker × ℝ) (S.covector.ker × ℝ)),
            (e : S.covector.ker × ℝ → S.covector.ker × ℝ) =
              curveGraphCoordinateMap
                (A ∘ fun q : S.covector.ker × ℝ ↦
                  extChartAt 𝓘(ℝ, E) terminal (C.curve q.1 q.2)) →
            ∀ t : ℝ, t ∈ interior (S.calibrationTimes w) →
              S.curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source → (w, t) ∈ e.source →
              (fderiv ℝ (A ∘ fun q : S.covector.ker × ℝ ↦
                extChartAt 𝓘(ℝ, E) terminal (C.curve q.1 q.2)) (w, t) (0, 1)).1 ≠ 0 →
              DifferentiableAt ℝ
                (fun z ↦ F.adaptedGraphPhase terminal A
                  (A ∘ fun q : S.covector.ker × ℝ ↦
                    extChartAt 𝓘(ℝ, E) terminal (C.curve q.1 q.2)) e
                  (z, (A (extChartAt 𝓘(ℝ, E) terminal (C.curve w t))).1)) w →
              (vectorFamilyMatrix bV (fun j ↦
                (fderiv ℝ (fun z ↦ F.adaptedGraphPhase terminal A
                  (A ∘ fun q : S.covector.ker × ℝ ↦
                    extChartAt 𝓘(ℝ, E) terminal (C.curve q.1 q.2)) e
                  (z, (A (extChartAt 𝓘(ℝ, E) terminal (S.curve w t))).1)) w (bW j)).1)).det ≠
                0 := by
  filter_upwards [S.ae_exists_comparison_active_jacobian D hF hcomplete hu m]
    with w hdata
  obtain ⟨hw, C, hsub, hcurve, hjet, hpos⟩ := hdata
  refine ⟨hw, C, hsub, hcurve, hjet, ?_⟩
  intro terminal bW bV A e he t ht hlegal hz hv hP
  obtain ⟨h₁, h₂⟩ := hjet terminal t hlegal
  obtain ⟨hγ, hΓ⟩ := F.chartPosition_same_firstJet_of_chartMomentum terminal h₁ h₂
  have hvalue : extChartAt 𝓘(ℝ, E) terminal (S.curve w t) =
      extChartAt 𝓘(ℝ, E) terminal (C.curve w t) := by rw [hcurve]
  have hfactor := (F.parameterizedJacobian_graphPhase_of_same_firstJet terminal
    bW bV A S.normalization hvalue hγ hΓ.differentiableAt he hz hv hP).2
  have hpositive := hpos terminal t ht hlegal
  intro hzero
  rw [hzero, abs_zero, mul_zero, zero_mul] at hfactor
  exact hpositive.ne' hfactor

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedLevelSeedPatch
