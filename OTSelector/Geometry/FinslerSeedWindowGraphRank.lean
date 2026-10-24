import OTSelector.Geometry.FinslerSeedWindowJacobian
import OTSelector.Geometry.CalibratedSeedWindowComparisonJacobian

/-!
# Interior regularity of the actual comparison Jacobi position matrix

The original window's positive physical Jacobian forces the same comparison's
actual graph-position matrix to have nonzero determinant. The almost-everywhere
producer retains one comparison for all interior times and all legal graph choices.
-/

open Set Filter Matrix Module MeasureTheory Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

variable {E M V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [BorelSpace E] in
/-- Positive original volume density excludes a singular actual comparison position
matrix, by the exact physical-to-graph Jacobian identity. -/
theorem comparisonGraphPhase_det_ne_zero_of_positive_jacobian
    (P : F.CalibratedSeedWindow u)
    (bW : Basis ι ℝ P.seed.covector.ker) (bV : Basis ι ℝ V)
    (A : E ≃L[ℝ] (ℝ × V)) {Γ : P.seed.covector.ker → ℝ → M}
    {w : P.seed.covector.ker} {t : ℝ}
    (hcurve : P.seed.curve w = Γ w)
    {D : (P.seed.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily (P.toManifold P.center) P.seed.curve) D (w, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily (P.toManifold P.center) Γ) D (w, t))
    {e : OpenPartialHomeomorph (P.seed.covector.ker × ℝ) (P.seed.covector.ker × ℝ)}
    (he : (e : P.seed.covector.ker × ℝ → P.seed.covector.ker × ℝ) =
      curveGraphCoordinateMap (A ∘ P.comparisonReadout Γ))
    (hz : (w, t) ∈ e.source)
    (hv : (fderiv ℝ (A ∘ P.comparisonReadout Γ) (w, t) (0, 1)).1 ≠ 0)
    (hP : DifferentiableAt ℝ
      (fun z ↦ F.adaptedGraphPhase (P.toManifold P.center) A
        (A ∘ P.comparisonReadout Γ) e (z, (A (P.comparisonReadout Γ (w, t))).1)) w)
    (hpos : 0 < parameterizedJacobian P.readout P.seed.normalization (t, w)) :
    (vectorFamilyMatrix bV (fun j ↦
      (fderiv ℝ (fun z ↦ F.adaptedGraphPhase (P.toManifold P.center) A
        (A ∘ P.comparisonReadout Γ) e (z, (A (P.readout (t, w))).1)) w (bW j)).1)).det ≠ 0 := by
  have hfactor := (P.parameterizedJacobian_comparisonGraphPhase_data bW bV A hcurve
    h₁ h₂ he hz hv hP).2
  intro hzero
  rw [hzero, abs_zero, mul_zero, zero_mul] at hfactor
  exact hpos.ne' hfactor

variable [T2Space M] [PreconnectedSpace M]

/-- Actual screened labels produce one complete comparison whose graph-position
Jacobi matrix is nonsingular throughout the original calibrated interior. -/
theorem ae_exists_comparison_graphPosition_regular (P : F.CalibratedSeedWindow u)
    (D : C11LevelSeedPresentation F u P.seed.covector P.seed.level
      P.seed.openLabels P.seed.labels P.seed.curve)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instGraphRankLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
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
          ∀ (bW : Basis ι ℝ P.seed.covector.ker) (bV : Basis ι ℝ V)
            (A : E ≃L[ℝ] (ℝ × V))
            (e : OpenPartialHomeomorph (P.seed.covector.ker × ℝ) (P.seed.covector.ker × ℝ)),
            (e : P.seed.covector.ker × ℝ → P.seed.covector.ker × ℝ) =
              curveGraphCoordinateMap (A ∘ P.comparisonReadout C.curve) →
            ∀ t : ℝ, t ∈ Ioo (P.left : ℝ) P.right →
              P.seed.curve w t ∈ (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source →
              (w, t) ∈ e.source →
              (fderiv ℝ (A ∘ P.comparisonReadout C.curve) (w, t) (0, 1)).1 ≠ 0 →
              DifferentiableAt ℝ
                (fun z ↦ F.adaptedGraphPhase (P.toManifold P.center) A
                  (A ∘ P.comparisonReadout C.curve) e
                    (z, (A (P.comparisonReadout C.curve (w, t))).1)) w →
              (vectorFamilyMatrix bV (fun j ↦
                (fderiv ℝ (fun z ↦ F.adaptedGraphPhase (P.toManifold P.center) A
                  (A ∘ P.comparisonReadout C.curve) e
                    (z, (A (P.readout (t, w))).1)) w (bW j)).1)).det ≠ 0 := by
  filter_upwards [P.ae_exists_comparison_positive_jacobian D hF hcomplete hu m]
    with w hdata
  obtain ⟨hw, C, hsub, hcurve, hjet, hpos⟩ := hdata
  refine ⟨hw, C, hsub, hcurve, hjet, ?_⟩
  intro bW bV A e he t ht hlegal hz hv hP
  obtain ⟨h₁, h₂⟩ := hjet (P.toManifold P.center) t hlegal
  exact P.comparisonGraphPhase_det_ne_zero_of_positive_jacobian bW bV A hcurve
    h₁ h₂ he hz hv hP (hpos (P.toManifold P.center) t ht hlegal)

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow
