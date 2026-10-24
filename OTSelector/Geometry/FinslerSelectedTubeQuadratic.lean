import OTSelector.Geometry.FinslerCalibratedTubeDistanceJet
import OTSelector.Geometry.FinslerTubeCoordinateHessian
import OTSelector.Analysis.CubicTaylor

/-!
# Quadratic distance defect in the same selected smooth tube

The actual coordinate-distance jet and Hessian give the fixed-time label coefficient.
The genuine smooth distance supplies a cubic remainder, retaining the given family
and its actual tube endpoint compliance throughout.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}


omit [T2Space M] [PreconnectedSpace M] in
private theorem selected_tube_covector
    (hF : F.IsSmoothStronglyConvex)
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
    {q : ℝ × W} (hq : q ∈ Y.source) :
    (fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Λ q.2 q.1) ↦
      (F.toFun ⟨Λ q.2 q.1, v⟩ : ℝ))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) q.1 1)).comp
        (mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y q) =
      ContinuousLinearMap.fst ℝ ℝ W := by
  have hv := congrArg (fun z : TangentBundle 𝓘(ℝ, E) M ↦ (z.2 : E))
    (tangentMap_tubeCoordinate_timeColumn hY heq hq)
  change mfderiv 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) Y q (1, 0) =
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) q.1 1 at hv
  have hp := F.tubeLength_fiberLegendre_eq hY hi hq (1, 0)
  rw [hv, congrFun heq q] at hp
  rw [← hp]
  exact (hF.tubeCoordinateEnergy_calibrated_identities Y hY hi t₀ heq hhalf hbound hq).1

/-- The given calibrated tube has its actual inverse-compliance quadratic distance
coefficient and one cubic remainder bound for all sufficiently small label displacements. -/
theorem exists_selected_tube_distance_quadratic_remainder
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
    let S := F.tubeEndpointCompliance Y (Λ w) a b
    ∃ r > 0, ∃ C ≥ 0, ∀ α β : W, ‖(α, β)‖ ≤ r →
      ‖(F.lengthEDist (Λ (w + α) a) (Λ (w + β) b)).toReal - (b - a) -
        (1 / 2 : ℝ) * S.inverse (0, β - α) (0, β - α)‖ ≤
          C * ‖(α, β)‖ ^ 3 := by
  obtain ⟨hc, hvalue, hfirst⟩ := hF.tubeCoordinateDistance_jet_of_calibrated_curve
    hcomplete hY hi heq hhalf t₀ hbound hab hΛ hstay hmin hu hsat hdu
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
  have hsecond := hF.tubeCoordinateDistance_hessian_of_calibrated_manifoldTube
    hcomplete (Λ w a) (Λ w b) hY hi heq hhalf t₀ hbound hab hEL hinit hz hΛ hseed
    hstay (mem_extChartAt_source (Λ w b))
    (by simpa only [hsame] using hmin) hu
    (by simpa only [hsame] using hsat) (by simpa only [hsame] using hdu)
  obtain ⟨r, hr, C, hC, hrem⟩ :=
    exists_quadratic_taylor_remainder_bound_of_contDiffAt (hc.of_le (by simp))
  refine ⟨r, hr, C, hC, ?_⟩
  intro α β hsmall
  have hnorm : ‖(((0 : ℝ), α), ((0 : ℝ), β))‖ = ‖(α, β)‖ := by simp [Prod.norm_def]
  have h := hrem ((0, α), (0, β)) (by simpa only [hnorm] using hsmall)
  have hlin : fderiv ℝ (F.tubeCoordinateDistance Y) ((a, w), (b, w))
      ((0, α), (0, β)) = 0 := by
    have ha := hstay a (left_mem_Icc.mpr hab.le)
    have hb := hstay b (right_mem_Icc.mpr hab.le)
    have hYa := (hY.contMDiffAt (Y.open_source.mem_nhds ha)).mdifferentiableAt (by simp)
    have hYb := (hY.contMDiffAt (Y.open_source.mem_nhds hb)).mdifferentiableAt (by simp)
    have hfa : HasFDerivAt (ContinuousLinearMap.fst ℝ (ℝ × W) (ℝ × W))
        (ContinuousLinearMap.fst ℝ (ℝ × W) (ℝ × W)) ((a, w), (b, w)) :=
      ContinuousLinearMap.hasFDerivAt _
    have hfb : HasFDerivAt (ContinuousLinearMap.snd ℝ (ℝ × W) (ℝ × W))
        (ContinuousLinearMap.snd ℝ (ℝ × W) (ℝ × W)) ((a, w), (b, w)) :=
      ContinuousLinearMap.hasFDerivAt _
    have hma := mfderiv_comp ((a, w), (b, w)) hYa hfa.hasMFDerivAt.mdifferentiableAt
    have hmb := mfderiv_comp ((a, w), (b, w)) hYb hfb.hasMFDerivAt.mdifferentiableAt
    rw [mfderiv_eq_fderiv, hfa.fderiv] at hma
    rw [mfderiv_eq_fderiv, hfb.fderiv] at hmb
    have hpa := selected_tube_covector hF hY hi heq hhalf t₀ hbound ha
    have hpb := selected_tube_covector hF hY hi heq hhalf t₀ hbound hb
    rw [hfirst.fderiv]
    erw [hma, hmb]
    simp only [← ContinuousLinearMap.comp_assoc]
    erw [hpb, hpa]
    change (0 : ℝ) - 0 = 0
    exact sub_self 0
  dsimp only at hvalue hsecond
  rw [hvalue, hlin, sub_zero, hsecond, hnorm] at h
  simpa only [tubeCoordinateDistance, heq, Prod.fst_add, Prod.snd_add,
    Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk, ContinuousLinearMap.coe_fst', zero_sub,
    sub_zero, zero_mul, zero_div, add_zero] using h

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
