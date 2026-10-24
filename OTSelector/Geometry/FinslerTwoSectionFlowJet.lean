import OTSelector.Geometry.Finsler.RoughRay.ParameterizedFlowJet

/-!
# Original and polynomial sections in one retained Finsler flow

The original section and the selected polynomial section can be different maps.
Their matching first derivatives suffice to propagate the same phase derivative
through the retained complete flow. The original derivative is restricted to the
preimage of the core under the original section, with no replacement by the
polynomial section or assertion about the measure of either preimage.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Two sections with the same actual first jet propagate through the same inverse
and complete flow. The rough derivative remains within the original section's core. -/
theorem normalized_two_section_flow_firstJet_of_calibrated_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {C : Set E} (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinterior : letI : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm C
        (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {x : E} (hxC : x ∈ C)
    (hdensity : Tendsto
      (fun r ↦ m (C ∩ closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 1))
    (hsecond : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {ρ σ v : W → E} {a : W → ℝ} {w₀ : W}
    (hσ : DifferentiableAt ℝ σ w₀) (hσ₀ : σ w₀ = x)
    (hρ : HasFDerivAt ρ (fderiv ℝ σ w₀) w₀) (hρ₀ : ρ w₀ = x)
    (hv : ContinuousAt v w₀) (ha : DifferentiableAt ℝ a w₀)
    (ha₀ : a w₀ = 1) (hzs : (σ w₀, v w₀) ∈ eL.source)
    (hdata :
      let P := scalarSecondJetPolynomial
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
      ∀ᶠ w in 𝓝 w₀,
        F.chartEnergy old (σ w, v w) = F.chartEnergy old (σ w₀, v w₀) ∧
        fiberLegendre (F.chartEnergy old) (σ w, v w) =
          a w • fderiv ℝ P (σ w))
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hΦ : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z.1) ⟨z.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    (out : M) (t : ℝ)
    (hlegal : Φ (σ w₀, v w₀) t ∈ (extChartAt 𝓘(ℝ, E) out).source) :
    let X := fun w ↦ (ρ w,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (ρ w))
    F.chartMomentumFamily out Φ (eL.symm (X w₀), t) =
      F.chartMomentumFamily out Φ ((σ w₀, v w₀), t) ∧
      HasFDerivAt (fun w ↦ F.chartMomentumFamily out Φ ((σ w, v w), t))
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily out Φ ((σ w, v w), t)) w₀) w₀ ∧
      HasFDerivWithinAt (fun w ↦ F.chartMomentumFamily out Φ (eL.symm (X w), t))
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily out Φ ((σ w, v w), t)) w₀)
        (ρ ⁻¹' C) w₀ := by
  obtain ⟨_, hcentral, hnormal, _, _⟩ :=
    hF.normalized_polynomial_seed_firstJet_of_calibrated_core hcomplete old m hCt hu
      hinterior hG hactual hxC hdensity hsecond heL hsource hInv hσ hσ₀ hv ha ha₀ hzs hdata
  have hsecondρ : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) (ρ w₀) := by
    simpa only [hρ₀] using hsecond
  have hgraph := hρ.prodMk (hsecondρ.comp w₀ hρ)
  have hrough : HasFDerivWithinAt
      (fun w ↦ (ρ w, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (ρ w)))
      ((fderiv ℝ σ w₀).prod ((fderiv ℝ (fderiv ℝ G) x).comp (fderiv ℝ σ w₀)))
      (ρ ⁻¹' C) w₀ := by
    apply hgraph.hasFDerivWithinAt.congr'
    · intro w hw
      exact Prod.ext rfl (hactual (ρ w) hw).fderiv
    · change ρ w₀ ∈ C
      rwa [hρ₀]
  have hseed : (ρ w₀,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (ρ w₀)) =
      parametricLegendre (F.chartEnergy old) (σ w₀, v w₀) := by
    rw [hcentral, hρ₀, (hactual x hxC).fderiv]
  have hι : ∀ᶠ w in 𝓝 w₀, (σ w, v w) ∈ eL.source :=
    (hσ.continuousAt.prodMk hv).eventually (eL.open_source.mem_nhds hzs)
  have hclock : HasFDerivAt (fun _ : W ↦ (0 : ℝ)) (0 : W →L[ℝ] ℝ) w₀ :=
    hasFDerivAt_const (0 : ℝ) w₀
  simpa only [sub_zero] using
    hF.chartSeed_supplied_family_same_firstJet_mixed old hEL hΦ heL hsource hInv
      hrough hnormal hclock.hasFDerivWithinAt hclock hseed rfl hι out t
      (by simpa only [sub_zero] using hlegal)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
