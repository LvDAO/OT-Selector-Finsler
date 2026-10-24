import OTSelector.Geometry.Finsler.ParameterizedFlowJet
import OTSelector.Geometry.Finsler.ParameterizedFlow
import OTSelector.Geometry.FinslerParameterizedSeedJet
import OTSelector.Analysis.Calculus.FlowJetMatching
import OTSelector.Analysis.Calculus.MixedFlowJetMatching

/-!
# Geometry.Finsler.ParameterizedFlowJet

* **Conditions:** A supplied all-slit smooth complete family, one supplied inverse branch and matched ordinary/within-set seed and clock first jets at the point.
* **Objects:** Equal actual chart-momentum values and equal mixed ordinary/within-set composite derivatives for those same data.
* **Proof detail:** Apply the chain rule to the actual smooth position–momentum evaluation map, retaining matched phase seeds and clock corrections on the original core.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): Foundation-only exact split: only the two generic supplied-family first-jet helpers are covered. The normalized-polynomial calibrated-core paper adapter is excluded.
-/

/-!
# Mixed first jets in the supplied complete smooth family

Matched phase seeds are passed through the same supplied inverse Legendre branch
and the same supplied all-slit family. The normal composite retains its ordinary
derivative; the original composite has that derivative within the original core.
The generic helpers take seed and clock first jets as inputs. The calibrated-core
consumer derives the seed jets from the selected normalized polynomial and uses
constant clocks. None of these results selects a second family or proves a uniform
distance remainder.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}





section CalibratedCore

variable [MeasurableSpace E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]

/-- Original calibrated-core data give matching first jets after propagation in the
same supplied all-slit family. The seed-jet matching is derived by the normalized
polynomial seed theorem, not assumed. The normal derivative is an ordinary ambient
derivative and the original derivative is taken on the unchanged preimage core. -/
theorem normalized_polynomial_flow_firstJet_of_calibrated_core
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
    {σ v : W → E} {a : W → ℝ} {w₀ : W}
    (hσ : DifferentiableAt ℝ σ w₀) (hσ₀ : σ w₀ = x)
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
    let X := fun w ↦ (σ w,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (σ w))
    F.chartMomentumFamily out Φ (eL.symm (X w₀), t) =
      F.chartMomentumFamily out Φ ((σ w₀, v w₀), t) ∧
      HasFDerivAt (fun w ↦ F.chartMomentumFamily out Φ ((σ w, v w), t))
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily out Φ ((σ w, v w), t)) w₀) w₀ ∧
      HasFDerivWithinAt (fun w ↦ F.chartMomentumFamily out Φ (eL.symm (X w), t))
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily out Φ ((σ w, v w), t)) w₀)
        (σ ⁻¹' C) w₀ := by
  obtain ⟨_, hcentral, hnormal, _, hrough⟩ :=
    hF.normalized_polynomial_seed_firstJet_of_calibrated_core hcomplete old m hCt hu
      hinterior hG hactual hxC hdensity hsecond heL hsource hInv hσ hσ₀ hv ha ha₀ hzs hdata
  have hseed : (σ w₀,
      fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (σ w₀)) =
      parametricLegendre (F.chartEnergy old) (σ w₀, v w₀) := by
    rw [hcentral, hσ₀, (hactual x hxC).fderiv]
  have hι : ∀ᶠ w in 𝓝 w₀, (σ w, v w) ∈ eL.source :=
    (hσ.continuousAt.prodMk hv).eventually (eL.open_source.mem_nhds hzs)
  have hclock : HasFDerivAt (fun _ : W ↦ (0 : ℝ)) (0 : W →L[ℝ] ℝ) w₀ :=
    hasFDerivAt_const (0 : ℝ) w₀
  simpa only [sub_zero] using
    hF.chartSeed_supplied_family_same_firstJet_mixed old hEL hΦ heL hsource hInv
      hrough hnormal hclock.hasFDerivWithinAt hclock hseed rfl hι out t
      (by simpa only [sub_zero] using hlegal)

end CalibratedCore

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
