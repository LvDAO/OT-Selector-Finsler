import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MetricPotentialEikonal
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.C11EikonalSeed

* **Conditions:** A compact original calibrated C1,1 core and a coordinate law absolutely continuous to Haar.
* **Objects:** Actual extension Hessian and density-one rough eikonal data on a constructed original Legendre branch almost everywhere.
* **Proof detail:** Use actual interior unit covectors, density and Rademacher; shrink the same branch near each good point and retain its energy 1/2 identity on the core.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap47.pdf#page=22): Theorem 472D, pp. 22–23 (Besicovitch Density Theorem).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11EikonalSeed.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11EikonalSeed`; the selected original proof blocks follow. -/
section

/-!
# Actual rough eikonal seed data on calibrated C1,1 cores

Original calibrated interior points supply genuine unit-energy Legendre covectors.
Density and Rademacher then give the actual extension Hessian almost everywhere.
At each such point a constructed Legendre branch carries the actual energy graph
on a density-one part of the same core. These are the direct inputs to the smooth
normalized jet and complete potential-level family constructions.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry

private theorem eikonalSeed_density_one_inter_open
    {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E]
    (m : Measure E) {K V : Set E} {x : E}
    (hx : Tendsto (fun r ↦ m (K ∩ closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 1)) (hV : IsOpen V) (hxV : x ∈ V) :
    Tendsto (fun r ↦ m ((K ∩ V) ∩ closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 1) := by
  apply hx.congr'
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
  have hr : ∀ᶠ r : ℝ in 𝓝[>] 0, r < ε := nhdsWithin_le_nhds (gt_mem_nhds hε)
  filter_upwards [hr] with r hr
  have hclosed : closedBall x r ⊆ V := by
    intro y hy
    exact hball ((mem_closedBall.mp hy).trans_lt hr)
  have heq : (K ∩ V) ∩ closedBall x r = K ∩ closedBall x r := by
    ext y
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, hclosed h.2⟩, h.2⟩⟩
  rw [heq]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Every actual calibrated C1,1 core has, almost everywhere for any original law
absolutely continuous with respect to Haar measure, its actual derivative jet and
one constructed smooth Legendre branch on which the original energy graph equals
one half on a density-one subset. No unit covector, branch, density or Hessian is supplied. -/
theorem ae_complete_eikonal_seed_data_of_calibrated_C11_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {m ν : Measure E} [IsAddHaarMeasure m] (hν : ν ≪ m)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instEikonalSeedLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hinterior : let _instEikonalSeedInterior : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm K (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hactual : ∀ x ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x) :
    ∀ᵐ x ∂ν.restrict K,
      x ∈ K ∧
      Tendsto (fun r ↦ m (K ∩ closedBall x r) / m (closedBall x r))
        (𝓝[>] 0) (𝓝 1) ∧
      HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x ∧
      HasFDerivWithinAt (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm))
        (fderiv ℝ (fderiv ℝ G) x) K x ∧
      ∃ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))) (V : Set E),
        (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
          parametricLegendre (F.chartEnergy old) ∧
        e.source ⊆ chartEnergyDomain old ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
        IsOpen V ∧ x ∈ V ∧ (∀ y ∈ V, (y, fderiv ℝ G y) ∈ e.target) ∧
        Tendsto (fun r ↦ m ((K ∩ V) ∩ closedBall x r) / m (closedBall x r))
          (𝓝[>] 0) (𝓝 1) ∧
        ∀ y ∈ K ∩ V,
          localHamiltonian (F.chartEnergy old) e (y, fderiv ℝ G y) = (1 / 2 : ℝ) := by
  let _instEikonalSeedMetric : MetricSpace M := F.metricSpace
  have hd : ∀ x ∈ K, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) old).symm x) :=
    fun x hx ↦ hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu (hinterior hx)
  have hunit := hF.chart_unit_legendre_on_of_calibrated_endpoints hcomplete old hKt hu hd
    (fun x hx ↦ (hinterior hx).2)
  have hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K :=
    fun x hx ↦ (hactual x hx).fderiv.symm
  have hdG : ∀ᵐ x ∂ν.restrict K, DifferentiableAt ℝ (fderiv ℝ G) x :=
    ae_restrict_of_ae (hν.ae_le hLip.ae_differentiableAt)
  filter_upwards [ae_density_one_of_absolutelyContinuous hν K, hdG,
    ae_restrict_mem hK.measurableSet] with x hx hsecond hxK
  obtain ⟨v, hv, hvp, _⟩ := hunit x hxK
  obtain ⟨e, he, _, htarget, hsub, _, heG, _, _⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse old hv
  have hp : (x, fderiv ℝ G x) ∈ e.target := by
    rw [hmatch hxK, ← hvp]
    exact htarget
  let V : Set E := (fun y ↦ (y, fderiv ℝ G y)) ⁻¹' e.target
  have hV : IsOpen V :=
    e.open_target.preimage (continuous_id.prodMk (hG.continuous_fderiv one_ne_zero))
  have hxV : x ∈ V := hp
  refine ⟨hxK, hx, hsecond.hasFDerivAt,
    hsecond.hasFDerivAt.hasFDerivWithinAt.congr' hmatch.symm hxK,
    e, V, he, hsub, heG, hV, hxV, (fun _ hy ↦ hy),
    eikonalSeed_density_one_inter_open m hx hV hxV, ?_⟩
  intro y hy
  obtain ⟨w, hw, hwp, hwe⟩ := hunit y hy.1
  have hyt : (y, fderiv ℝ G y) ∈ e.target := hy.2
  have hinverse : e.symm (y, fderiv ℝ G y) = (y, w) := by
    apply hF.injOn_parametricLegendre_chartEnergy old (hsub (e.map_target hyt)) hw
    calc
      parametricLegendre (F.chartEnergy old) (e.symm (y, fderiv ℝ G y)) =
          (y, fderiv ℝ G y) := by simpa only [he] using e.right_inv hyt
      _ = parametricLegendre (F.chartEnergy old) (y, w) := by
        simp only [parametricLegendre, hwp, hmatch hy.1]
  rw [hF.localHamiltonian_chartEnergy_eq old he hsub hyt, hinverse]
  exact hwe

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
