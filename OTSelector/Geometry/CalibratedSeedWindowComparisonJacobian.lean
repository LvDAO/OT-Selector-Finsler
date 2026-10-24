import OTSelector.Geometry.FinslerPhaseJetJacobianTransfer
import OTSelector.Geometry.Finsler.CalibratedSeedWindow

/-!
# Original calibrated-window Jacobians from the smooth comparison

The original window keeps its actual readout, parameter normalization, potential time
and seed label. Matching actual joint phase jets identify its physical Jacobian with
the comparison's true graph Jacobi matrix. Only the comparison uses a graph inverse.
-/

open Set Filter Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow

set_option backward.isDefEq.respectTransparency false

variable {E M V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [DecidableEq ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Read the comparison in the original window's fixed manifold chart, with label first. -/
def comparisonReadout (P : F.CalibratedSeedWindow u)
    (Γ : P.seed.covector.ker → ℝ → M) (q : P.seed.covector.ker × ℝ) : E :=
  extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (Γ q.1 q.2)

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The original window Jacobian equals that of the comparison in the same chart and
normalization when their actual joint phase derivatives agree. -/
theorem parameterizedJacobian_eq_comparison
    (P : F.CalibratedSeedWindow u) {Γ : P.seed.covector.ker → ℝ → M}
    {w : P.seed.covector.ker} {t : ℝ}
    {D : (P.seed.covector.ker × ℝ) →L[ℝ] E × (E →L[ℝ] ℝ)}
    (h₁ : HasFDerivAt (F.chartMomentumFamily (P.toManifold P.center) P.seed.curve) D (w, t))
    (h₂ : HasFDerivAt (F.chartMomentumFamily (P.toManifold P.center) Γ) D (w, t)) :
    parameterizedJacobian P.readout P.seed.normalization (t, w) =
      parameterizedJacobian (fun q : ℝ × P.seed.covector.ker ↦
        P.comparisonReadout Γ (q.2, q.1)) P.seed.normalization (t, w) :=
  F.parameterizedJacobian_eq_of_chartMomentum_same_firstJet
    (P.toManifold P.center) h₁ h₂ P.seed.normalization

omit [BorelSpace E] in
/-- The same original window Jacobian is computed by the comparison's Hamiltonian
position matrix at the original graph time, retaining original speed and normalization. -/
theorem parameterizedJacobian_comparisonGraphPhase_data
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
        (A ∘ P.comparisonReadout Γ) e (z, (A (P.comparisonReadout Γ (w, t))).1)) w) :
    let s := (A (P.readout (t, w))).1
    let c := (fderiv ℝ (A ∘ P.comparisonReadout P.seed.curve) (w, t) (0, 1)).1
    let J := vectorFamilyMatrix bV (fun j ↦
      (fderiv ℝ (fun z ↦ F.adaptedGraphPhase (P.toManifold P.center) A
        (A ∘ P.comparisonReadout Γ) e (z, s)) w (bW j)).1)
    HasDerivAt (fun r ↦ (e.symm (w, r)).2) c⁻¹ s ∧
      parameterizedJacobian P.readout P.seed.normalization (t, w) =
        |c| * |J.det| * |(LinearMap.toMatrix (timeLabelBasis bV) (timeLabelBasis bW)
          (P.seed.normalization.trans A).symm.toLinearEquiv.toLinearMap).det| := by
  obtain ⟨hγ, hΓ⟩ := F.chartPosition_same_firstJet_of_chartMomentum
    (P.toManifold P.center) h₁ h₂
  exact F.parameterizedJacobian_graphPhase_of_same_firstJet (P.toManifold P.center)
    bW bV A P.seed.normalization (by
      change extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (P.seed.curve w t) =
        extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (Γ w t)
      rw [hcurve])
      hγ hΓ.differentiableAt he hz hv hP

end OTSelector.Geometry.ContinuousFinslerNorm.CalibratedSeedWindow
