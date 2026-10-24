import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedTranslation
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.TangentReadout
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedPhaseData.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedPhaseData`; the selected original proof blocks follow. -/
section

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

/-- The original potential covector gives unit chart speed, the exact clock, and
an isometry on the whole closed calibrated interval of the same complete curve. -/
theorem calibrated_phase_isometry_data_of_original_covector (hF : F.IsSmoothStronglyConvex)
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
    let _instPhaseIsometryResult : MetricSpace M := F.metricSpace
    let z := e.symm (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x)
    (F.chartLength old z : ℝ) = 1 ∧
      (∀ t ∈ Icc (-δ) δ,
        u (Phi z t) = u ((extChartAt 𝓘(ℝ, E) old).symm x) + t) ∧
      Isometry (fun t : Icc (-δ) δ ↦ Phi z t) := by
  let _instPhaseDataMetric : MetricSpace M := F.metricSpace
  let q := (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x)
  let z := e.symm q
  have hz : z ∈ chartEnergyDomain old := hsub (e.map_target hq)
  have hphase : parametricLegendre (F.chartEnergy old) z = q := by
    rw [← he]
    exact e.right_inv hq
  have hbase : z.1 = x := congrArg Prod.fst hphase
  have hx : x ∈ (extChartAt 𝓘(ℝ, E) old).target := hbase ▸ hz.1
  have hposition : Phi z 0 = (extChartAt 𝓘(ℝ, E) old).symm x := by
    have h := congrArg (fun v : TangentBundle 𝓘(ℝ, E) M ↦ v.1) (hinit z hz)
    rw [tangentChart_symm_eq old hz.1 z.2] at h
    simpa only [hbase, tangentMap_proj] using h
  have hmomentum : F.chartMomentumFamily old (fun _ : E ↦ Phi z) (x, 0) = q :=
    (hF.chartMomentum_of_tangent_eq (hEL z hz 0 (mem_univ 0)) old hz
      (hinit z hz)).trans hphase
  obtain ⟨hunit, _, _, hclock, hiso, _⟩ :=
    hF.calibrated_translation_of_chartMomentum hcomplete old hu
      (Γ := fun _ : E ↦ Phi z) hx (hEL z hz) hposition hmomentum hdu hδ ha hb
  refine ⟨?_, hclock, hiso⟩
  have h := hunit 0
  rw [hinit z hz] at h
  change F.chartLength old z = 1 at h
  exact_mod_cast h



end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
