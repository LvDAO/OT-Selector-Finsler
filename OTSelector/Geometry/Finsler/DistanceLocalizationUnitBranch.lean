import Mathlib.Analysis.Calculus.ImplicitContDiff
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCovector
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CovectorNormalization
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceLocalizationUnitBranch.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceLocalizationUnitBranch`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.DistanceLocalizationUnitBranch

* **Conditions:** An actual contact core with calibrated partners and original C1,1 covector data near a specified point.
* **Objects:** A genuine local inverse branch on which the existing core states already have energy 1/2 and the positive normalization acts as the identity.
* **Proof detail:** Choose the original local Legendre inverse, shrink the covector neighborhood and use calibrated unit energy on the unchanged core.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.

Source relation (derived): The equality is proved only on the core; it does not require arbitrary nearby covectors to be unit energy.
-/

/-! # Unit normalization branches from original calibrated cores -/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The actual calibrated core produces a legal normalization branch near each
of its points. Normalization fixes every original core state on this same branch. -/
theorem exists_original_unit_covector_branch_on_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {K : Set E} (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _inst : MetricSpace M := F.metricSpace
      ∀ y ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    {x : E} (hx : x ∈ K) :
    fderiv ℝ G x ≠ 0 ∧
      ∃ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))) (V : Set E),
        (e : E × E → E × (E →L[ℝ] ℝ)) = parametricLegendre (F.chartEnergy old) ∧
        e.source ⊆ chartEnergyDomain old ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
        IsOpen V ∧ x ∈ V ∧ (∀ y ∈ V, (y, fderiv ℝ G y) ∈ e.target) ∧
        ∀ y ∈ K ∩ V,
          F.covectorNormalization old e (1 / 2) (y, fderiv ℝ G y) =
            e.symm (y, fderiv ℝ G y) := by
  let : MetricSpace M := F.metricSpace
  have hd (y : E) (hy : y ∈ K) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) old).symm y) := by
    obtain ⟨a, b, hax, ha, hxb, hb⟩ := hpartners y hy
    apply hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
    exact ⟨⟨a, dist_pos.mp (hax.symm ▸ hδ), ha.trans hax.symm⟩,
      ⟨b, dist_pos.mp (hxb.symm ▸ hδ), hb.trans hxb.symm⟩⟩
  have hforward (y : E) (hy : y ∈ K) : ∃ b : M,
      (extChartAt 𝓘(ℝ, E) old).symm y ≠ b ∧
      u b - u ((extChartAt 𝓘(ℝ, E) old).symm y) =
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) b := by
    obtain ⟨a, b, _, _, hxb, hb⟩ := hpartners y hy
    exact ⟨b, dist_pos.mp (hxb.symm ▸ hδ), hb.trans hxb.symm⟩
  have hunit := hF.chart_unit_legendre_on_of_calibrated_endpoints hcomplete old hKt hu hd hforward
  obtain ⟨v, hv, hvp, hve⟩ := hunit x hx
  have hp : fderiv ℝ G x ≠ 0 := by
    intro hz
    have hh := hF.chartEnergy_euler old hv
    rw [hvp, ← hmatch hx, hz, _root_.zero_apply] at hh
    linarith [F.chartEnergy_pos old hv]
  obtain ⟨e, he, _, ht, hsource, _, hInv, _, _⟩ :=
    hF.exists_smooth_chartLegendre_local_inverse old hv
  let V := (fun y ↦ (y, fderiv ℝ G y)) ⁻¹' e.target
  have hV : IsOpen V := e.open_target.preimage
    (continuous_id.prodMk (hG.continuous_fderiv one_ne_zero))
  have hxV : x ∈ V := by
    change (x, fderiv ℝ G x) ∈ e.target
    rw [hmatch hx, ← hvp]
    exact ht
  refine ⟨hp, e, V, he, hsource, hInv, hV, hxV, (fun _ hy ↦ hy), ?_⟩
  intro y hy
  obtain ⟨w, hw, hwp, hwe⟩ := hunit y hy.1
  have hyt : (y, fderiv ℝ G y) ∈ e.target := hy.2
  have hinv : e.symm (y, fderiv ℝ G y) = (y, w) := by
    apply hF.injOn_parametricLegendre_chartEnergy old (hsource (e.map_target hyt)) hw
    calc
      parametricLegendre (F.chartEnergy old) (e.symm (y, fderiv ℝ G y)) =
          (y, fderiv ℝ G y) := by simpa only [he] using e.right_inv hyt
      _ = parametricLegendre (F.chartEnergy old) (y, w) := by
        simp only [parametricLegendre, hwp, hmatch hy.1]
  exact (hF.covectorNormalization_spec old he hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)).2.2 (y, fderiv ℝ G y) hyt |>.2.2.2.2
      (by rw [hinv]; exact hwe)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
