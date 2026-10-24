import OTSelector.Geometry.Finsler.TubeCoordinateCalibratedDistance
import OTSelector.Geometry.Finsler.FlowLocalC2

/-!
# Distance jets along the given calibrated curve

An actual smooth calibrated tube supplies the original distance jet along its central
curve. The auxiliary complete tangent family is constructed at the segment's initial
time internally and identified with that whole central curve. No identification of
parameter families with different initialization times is needed.
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

/-- A calibrated minimizing segment in the given smooth tube has a smooth original
coordinate distance and the intrinsic length-momentum first jet of that same curve.
The complete family at the segment's initial time and its legal phase are constructed
internally, without any supplied endpoint-rank or distance-regularity hypothesis. -/
theorem tubeCoordinateDistance_jet_of_calibrated_curve
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
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
    {a b : ℝ} (hab : a < b) {w : W}
    (hΛ : F.IsEulerLagrangeOn (Λ w) univ)
    (hstay : ∀ t ∈ Icc a b, (t, w) ∈ Y.source)
    (hmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (Λ w a) (Λ w b) = Manifold.pathELength 𝓘(ℝ, E) (Λ w) a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (Λ w b) - u (Λ w a) = dist (Λ w a) (Λ w b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Λ w a)) :
    let qa : ℝ × W := (a, w)
    let qb : ℝ × W := (b, w)
    let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Λ w t) →L[ℝ] ℝ := fun t ↦
      fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Λ w t) ↦
        (F.toFun ⟨Λ w t, v⟩ : ℝ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ w) t 1)
    ContDiffAt ℝ ∞ (F.tubeCoordinateDistance Y) (qa, qb) ∧
      F.tubeCoordinateDistance Y (qa, qb) = b - a ∧
      HasFDerivAt (F.tubeCoordinateDistance Y)
        ((p b).comp (mfderiv 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
          (fun q ↦ Y q.2) (qa, qb)) -
        (p a).comp (mfderiv 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
          (fun q ↦ Y q.1) (qa, qb))) (qa, qb) := by
  obtain ⟨Γ, hEL, hinit, _⟩ := hF.exists_complete_tangentFamily_C2 hcomplete (Λ w a) a
  let z := (extChartAt 𝓘(ℝ, E) (Λ w a) (Λ w a),
    deriv (extChartAt 𝓘(ℝ, E) (Λ w a) ∘ Λ w) a)
  obtain ⟨hz, hsame⟩ := hF.eq_complete_family_of_isEulerLagrangeOn (Λ w a)
    hEL hinit hΛ (mem_extChartAt_source (Λ w a))
  change z ∈ chartEnergyDomain (Λ w a) at hz
  change Γ z = Λ w at hsame
  have hseed : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ w) ⟨a, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨Λ w a, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z := by
    simpa only [hsame] using hinit z hz
  have h := hF.tubeCoordinateDistance_smooth_of_calibrated_manifoldTube
    hcomplete (Λ w a) (Λ w b) hY hi heq hhalf t₀ hbound hab hEL hinit hz hΛ hseed
    hstay (mem_extChartAt_source (Λ w b))
    (by simpa only [hsame] using hmin) hu
    (by simpa only [hsame] using hsat) (by simpa only [hsame] using hdu)
  erw [hsame] at h
  exact h

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
