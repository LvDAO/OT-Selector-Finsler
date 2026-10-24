import OTSelector.Geometry.Finsler.Calibration.PhaseIsometry
import OTSelector.Geometry.Finsler.CalibratedTranslation
import OTSelector.Geometry.Finsler.TangentReadout

/-!
# Geometry.Finsler.Calibration.PhaseIsometry

* **Conditions:** A specified all-slit complete family and genuine inverse Legendre branch; the original potential differential at a point has two calibrated partners at a positive common distance.
* **Objects:** Unit original chart speed, exact original potential clock and isometry of the same prescribed curve on the closed trimmed interval.
* **Proof detail:** Read the actual inverse Legendre initial state, use calibrated uniqueness through the point and extend the partner segment identities to its closed endpoints.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): A same-family calibrated phase identification; neither a second complete flow nor independently normalized covector is chosen.
-/

/-!
# Original calibrated phase speed and potential clock

The same prescribed complete curve and inverse Legendre branch retain the original
potential differential. Its two calibrated partners force unit chart speed and the
exact original potential clock throughout the closed trimmed time interval.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}



/-- The original potential covector and two calibrated partners force unit chart
speed and its true clock on the same supplied complete curve and inverse branch. -/
theorem calibrated_phase_data_of_original_covector (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : let _instPhaseDataLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old) {x : E}
    (hq : (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x) ∈ e.target)
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) old).symm x))
    {δ : ℝ} (hδ : 0 < δ) {a b : M}
    (ha : let _instPhaseDataPre : MetricSpace M := F.metricSpace
      dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ)
    (hb : let _instPhaseDataPost : MetricSpace M := F.metricSpace
      dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ) :
    let z := e.symm (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x)
    (F.chartLength old z : ℝ) = 1 ∧
      ∀ t ∈ Icc (-δ) δ,
        u (Phi z t) = u ((extChartAt 𝓘(ℝ, E) old).symm x) + t := by
  have hdata := hF.calibrated_phase_isometry_data_of_original_covector
    hcomplete old hu hEL hinit he hsub hq hdu hδ ha hb
  exact ⟨hdata.1, hdata.2.1⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
