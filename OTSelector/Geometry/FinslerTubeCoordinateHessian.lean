import OTSelector.Geometry.Finsler.TubeCoordinateBranch
import OTSelector.Geometry.FinslerTubeCoordinateDistanceHessian

/-!
# The original distance Hessian from the constructed genuine tube branch

The original complete family constructs its true endpoint-parameterized minimizing
branch in Y. The actual Jacobi equation and original length momentum identify the
Hessian by the inverse integral of the true pulled-back energy Hessian and its radial
correction. Neither a branch, a coordinate identification, nor a Hessian is supplied.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The original distance Hessian in a genuine calibrated tube is its actual inverse
integral response minus the precise radial term. All branch and differential data are
constructed from the original complete family and its calibrated central curve. -/
theorem tubeCoordinateDistance_hessian_of_calibrated_manifoldTube
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (initial terminal : M)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Λ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Λ q.2 q.1)
    (hhalf : ∀ q ∈ Y.source,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2)
    (t₀ : ℝ)
    (hbound : ∀ x ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 t₀) x v)
        (F.toFun ⟨x, v⟩ : ℝ))
    {a b : ℝ} (hab : a < b) {Γ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {z : E × E} (hz : z ∈ chartEnergyDomain initial) {w : W}
    (hΛ : F.IsEulerLagrangeOn (Λ w) univ)
    (hseed : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ w) ⟨a, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hstay : ∀ t ∈ Icc a b, (t, w) ∈ Y.source)
    (hterminal : Λ w b ∈ (extChartAt 𝓘(ℝ, E) terminal).source)
    (hmin : let _instTubeFinalHessianMinENorm :
        ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Γ z a) (Γ z b) = Manifold.pathELength 𝓘(ℝ, E) (Γ z) a b)
    {u : M → ℝ} (hu : let _instTubeFinalHessianLipMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hsat : let _instTubeFinalHessianSatMetric : MetricSpace M := F.metricSpace
      u (Γ z b) - u (Γ z a) = dist (Γ z a) (Γ z b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Γ z a))
    (h k : (ℝ × W) × (ℝ × W)) :
    let S := F.tubeEndpointCompliance Y (Λ w) a b
    let p := ContinuousLinearMap.fst ℝ ℝ W
    fderiv ℝ (fderiv ℝ (F.tubeCoordinateDistance Y)) ((a, w), (b, w)) h k =
      S.inverse (h.2 - h.1) (k.2 - k.1) -
        p (h.2 - h.1) * p (k.2 - k.1) / (b - a) := by
  let _instTubeFinalHessianProofENorm :
      ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  obtain ⟨e, Q, _, hQ, hq, hQY, _, _, _, hELQ, hGQ, hend, hcentral⟩ :=
    hF.exists_tubeCoordinate_endpointBranch_of_calibrated_manifoldTube hcomplete
      initial terminal hY hi heq hhalf t₀ hbound hab hEL hinit hz hΛ hseed
      hstay hterminal hmin hu hsat hdu
  have hH := hF.tubeCoordinateDistance_hessian_of_calibrated_branch Y hY hi t₀
    heq hhalf hbound hQ hQY hELQ hGQ hab
    (fun q hq ↦ ⟨(hend q hq).1, (hend q hq).2.1⟩)
    (fun q hq ↦ (hend q hq).2.2) hq hcentral hstay h k
  change _ = (F.tubeEndpointCompliance Y (Λ w) a b).inverse
    (h.2 - h.1) (k.2 - k.1) - (h.2 - h.1).1 * (k.2 - k.1).1 / (b - a)
  simpa only [hcentral] using hH

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
