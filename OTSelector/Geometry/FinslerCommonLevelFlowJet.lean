import OTSelector.Analysis.Calculus.CommonLevelSection
import OTSelector.Geometry.FinslerTwoSectionFlowJet

/-!
# Fixed-projection original level sections in the selected Finsler flow

The original C1 level and selected polynomial level use the same fixed projection.
Differentiating their defining identities derives equality of their actual first
jets. These jets propagate through the same supplied inverse and complete flow,
with the original allowed set retained under the original section.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Level and fixed-projection identities derive the matching section derivatives
needed by the actual two-section flow theorem. No derivative equality is an input. -/
theorem normalized_fixedProjection_flow_firstJet_of_calibrated_core
    (hF : F.IsSmoothStronglyConvex)
    (p₀ : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0)
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
    (hp : (fderiv ℝ G x) v₀ ≠ 0)
    {ρ σ v : p₀.ker → E} {a : p₀.ker → ℝ}
    (hσ : DifferentiableAt ℝ σ 0) (hσ₀ : σ 0 = x)
    (hρ : DifferentiableAt ℝ ρ 0) (hρ₀ : ρ 0 = x)
    (hρlevel : ∀ᶠ w in 𝓝 (0 : p₀.ker), G (ρ w) = G x)
    (hσlevel :
      let P := scalarSecondJetPolynomial
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
      ∀ᶠ w in 𝓝 (0 : p₀.ker), P (σ w) = P x)
    (hρprojection :
      let π₀ : E →L[ℝ] p₀.ker :=
        (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
          (covectorSplitting p₀ v₀ hp₀).symm.toContinuousLinearMap
      ∀ᶠ w in 𝓝 (0 : p₀.ker), π₀ (ρ w - x) = w)
    (hσprojection :
      let π₀ : E →L[ℝ] p₀.ker :=
        (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
          (covectorSplitting p₀ v₀ hp₀).symm.toContinuousLinearMap
      ∀ᶠ w in 𝓝 (0 : p₀.ker), π₀ (σ w - x) = w)
    (hv : ContinuousAt v 0) (ha : DifferentiableAt ℝ a 0)
    (ha₀ : a 0 = 1) (hzs : (σ 0, v 0) ∈ eL.source)
    (hdata :
      let P := scalarSecondJetPolynomial
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
      ∀ᶠ w in 𝓝 0,
        F.chartEnergy old (σ w, v w) = F.chartEnergy old (σ 0, v 0) ∧
        fiberLegendre (F.chartEnergy old) (σ w, v w) =
          a w • fderiv ℝ P (σ w))
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hΦ : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun z ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z.1) ⟨z.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    (out : M) (t : ℝ)
    (hlegal : Φ (σ 0, v 0) t ∈ (extChartAt 𝓘(ℝ, E) out).source) :
    let X := fun w ↦ (ρ w,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (ρ w))
    F.chartMomentumFamily out Φ (eL.symm (X 0), t) =
      F.chartMomentumFamily out Φ ((σ 0, v 0), t) ∧
      HasFDerivAt (fun w ↦ F.chartMomentumFamily out Φ ((σ w, v w), t))
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily out Φ ((σ w, v w), t)) 0) 0 ∧
      HasFDerivWithinAt (fun w ↦ F.chartMomentumFamily out Φ (eL.symm (X w), t))
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily out Φ ((σ w, v w), t)) 0)
        (ρ ⁻¹' C) 0 := by
  have hGx : HasFDerivAt G (fderiv ℝ G x) x :=
    (hG.differentiable one_ne_zero x).hasFDerivAt
  have hP := hasFDerivAt_scalarSecondJetPolynomial_center
    (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  have hρjet := hasFDerivAt_levelSection_of_fixedProjection p₀ v₀ hp₀
    hGx hp hρ hρ₀ hρlevel hρprojection
  have hσjet := hasFDerivAt_levelSection_of_fixedProjection p₀ v₀ hp₀
    hP hp hσ hσ₀ hσlevel hσprojection
  have hmatch : HasFDerivAt ρ (fderiv ℝ σ 0) 0 := by
    rw [hσjet.fderiv]
    exact hρjet
  exact hF.normalized_two_section_flow_firstJet_of_calibrated_core hcomplete old m hCt hu
    hinterior hG hactual hxC hdensity hsecond heL hsource hInv hσ hσ₀ hmatch hρ₀ hv ha
    ha₀ hzs hdata hEL hΦ out t hlegal

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
