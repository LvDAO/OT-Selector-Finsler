import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedDistance
import OTSelector.Geometry.Finsler.CalibratedMinimizerUnique
import OTSelector.Geometry.Finsler.CalibratedVelocity
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.LipschitzDifferential
import OTSelector.Geometry.Finsler.ManifoldTubeCalibration

/-!
# Geometry.Finsler.CalibratedCovector

* **Conditions:** A global potential Lipschitz for the original distance and differentiable at a calibrated initial point.
* **Objects:** Its actual intrinsic energy Legendre covector at a constructed unit tangent, with identical chart covector and half-energy state.
* **Proof detail:** Construct the genuine complete minimizing segment, differentiate original calibration at its initial point, use the norm support bound and transfer the true tangent/covector through any legal chart.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedCovector.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedCovector`; the selected original proof blocks follow. -/
section

/-!
# Actual unit Legendre covectors from calibrated original-distance endpoints

A global potential Lipschitz for the original Finsler distance and differentiable at a
calibrated initial point has the actual energy Legendre covector of a unit tangent.
The tangent is constructed from the original complete minimizing curve. The resulting
identity transfers to any original chart legal at that point.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- Saturation of an original-length bound at a unit tangent identifies the covector
with the actual differential of the original fiber energy. -/
theorem fiberEnergy_fderiv_eq_of_unit_calibration (hF : F.IsSmoothStronglyConvex)
    (x : M) (p : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)
    {v : TangentSpace 𝓘(ℝ, E) x} (hv : F.toFun ⟨x, v⟩ = 1)
    (hbound : ∀ w : TangentSpace 𝓘(ℝ, E) x, p w ≤ (F.toFun ⟨x, w⟩ : ℝ))
    (hsat : p v = 1) : fderiv ℝ (F.fiberEnergy x) v = p := by
  let _instCalibratedCovectorFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let _instCalibratedCovectorFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedSpace ℝ E)
  have hv0 : v ≠ 0 := by
    intro heq
    have hz : F.toFun ⟨x, v⟩ = 0 := heq ▸ F.map_zero x
    exact zero_ne_one (hz.symm.trans hv)
  have hd : DifferentiableAt ℝ (F.fiberEnergy x) v :=
    hF.differentiableAt_fiberEnergyModel x hv0
  exact fderiv_half_sq_eq_of_unit_calibration p (fun _ ↦ rfl) hd
    (by exact_mod_cast hv) hbound hsat

/-- The intrinsic unit Legendre identity transfers to any legal original chart,
producing its actual coordinate covector and half energy. -/
theorem exists_chart_unit_covector_of_intrinsic (hF : F.IsSmoothStronglyConvex)
    (old : M) {x : M} (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {u : M → ℝ} (hu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (v : TangentSpace 𝓘(ℝ, E) x) (hunit : (F.toFun ⟨x, v⟩ : ℝ) = 1)
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x = fderiv ℝ (F.fiberEnergy x) v) :
    ∃ w : E, (extChartAt 𝓘(ℝ, E) old x, w) ∈ chartEnergyDomain old ∧
      fiberLegendre (F.chartEnergy old) (extChartAt 𝓘(ℝ, E) old x, w) =
        fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (extChartAt 𝓘(ℝ, E) old x) ∧
      F.chartEnergy old (extChartAt 𝓘(ℝ, E) old x, w) = (1 / 2 : ℝ) := by
  let instCalibratedChartFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let instCalibratedChartFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedSpace ℝ E)
  let e := extChartAt 𝓘(ℝ, E) old
  let D : TangentSpace 𝓘(ℝ, E) x →L[ℝ] E := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x
  have hD : Function.Bijective D := (isInvertible_mfderiv_extChartAt hx).bijective
  have hv : v ≠ 0 := by
    intro hzero
    simp [hzero] at hunit
  have hz : (e x, D v) ∈ chartEnergyDomain old :=
    ⟨e.map_source hx, fun hzero ↦ hv (hD.injective (hzero.trans D.map_zero.symm))⟩
  refine ⟨D v, hz, ?_, ?_⟩
  · have hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) := by
      simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
        mdifferentiableWithinAt_extChartAt_symm (e.map_source hx)
    have hu' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (e.symm (e x)) := by
      rwa [e.left_inv hx]
    have hinv : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x)).comp D =
        ContinuousLinearMap.id ℝ _ := by
      simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
        mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx
    have hchain : (fderiv ℝ (u ∘ e.symm) (e x)).comp D =
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
      rw [← mfderiv_eq_fderiv, mfderiv_comp (e x) hu' hi,
        ContinuousLinearMap.comp_assoc, hinv, ContinuousLinearMap.comp_id, e.left_inv hx]
    have hm := hF.chartEnergy_fderiv_comp_mfderiv old hx v hz
    ext w
    obtain ⟨η, rfl⟩ := hD.surjective w
    exact congrArg (fun A ↦ A η) (hm.trans (hp.symm.trans hchain.symm))
  · have he : F.chartLength old (e x, D v) = F.toFun ⟨x, v⟩ :=
      F.chartLength_mfderiv_extChartAt old hx v
    rw [F.chartEnergy_eq_chartLength_sq, he, hunit]
    norm_num

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]

/-- A calibrated isometric interval identifies the actual initial covector with the
original energy Legendre differential at its unit initial tangent. -/
theorem mfderiv_eq_fiberEnergy_of_calibrated_interval (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : let _instCalibratedCovectorIntervalLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hiso : let _instCalibratedCovectorIntervalIso : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t))
    (hsat : u (c b) - u (c a) = b - a)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a)
    (hunit : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩) = 1)
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a) =
      fderiv ℝ (F.fiberEnergy (c a)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a 1) := by
  apply (hF.fiberEnergy_fderiv_eq_of_unit_calibration (c a) _ hunit ?_ ?_).symm
  · intro w
    have hb := hF.abs_mfderiv_le_finsler_of_lipschitz hu hd w
    exact (le_abs_self _).trans (by simpa only [NNReal.coe_one, one_mul] using! hb)
  · exact hF.mfderiv_initial_eq_one_of_calibrated_interval hu hab hiso hsat hc hd

/-- Distinct original-distance calibrated endpoints construct a unit tangent whose
actual energy Legendre covector is the actual differential of the original potential. -/
theorem exists_unit_legendre_of_calibrated_endpoints (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instCalibratedCovectorEndpointLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x y : M} (hxy : x ≠ y)
    (hsat : let _instCalibratedCovectorEndpointSat : MetricSpace M := F.metricSpace
      u y - u x = dist x y)
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    ∃ v : TangentSpace 𝓘(ℝ, E) x, F.toFun ⟨x, v⟩ = 1 ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x = fderiv ℝ (F.fiberEnergy x) v ∧
      F.fiberEnergy x v = (1 / 2 : ℝ) := by
  let _instCalibratedCovectorEndpointMetric : MetricSpace M := F.metricSpace
  let _instCalibratedCovectorEndpointENorm :
      ∀ z : M, ENorm (TangentSpace 𝓘(ℝ, E) z) := F.enorm
  obtain ⟨g, ⟨hg0, hgy, _, hgsmooth, hgspeed, hgiso, _⟩, _⟩ :=
    hF.existsUnique_complete_calibrated_minimizer hcomplete hu hxy hsat hd
  have hdg : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g 0) := by rwa [hg0]
  have hsatg : u (g (dist x y)) - u (g 0) = dist x y - 0 := by
    simpa only [hgy, hg0, sub_zero] using hsat
  have heq := hF.mfderiv_eq_fiberEnergy_of_calibrated_interval hu (dist_pos.mpr hxy)
    hgiso hsatg (hgsmooth.mdifferentiable (by simp) 0) (hgspeed 0) hdg
  have hex : ∃ v : TangentSpace 𝓘(ℝ, E) (g 0), F.toFun ⟨g 0, v⟩ = 1 ∧
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (g 0) = fderiv ℝ (F.fiberEnergy (g 0)) v ∧
      F.fiberEnergy (g 0) v = (1 / 2 : ℝ) := by
    refine ⟨mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g 0 1, hgspeed 0, heq, ?_⟩
    change (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) g ⟨0, (1 : ℝ)⟩) : ℝ) ^ 2 / 2 = _
    rw [hgspeed 0]
    norm_num
  exact hg0 ▸ hex

/-- Calibrated original-distance endpoints produce the actual unit-energy Legendre
covector in every legal original chart, with no unit-covector input. -/
theorem exists_chart_unit_legendre_of_calibrated_endpoints (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {x y : M} (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {u : M → ℝ} (hu : let _instCalibratedCovectorChartLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hxy : x ≠ y)
    (hsat : let _instCalibratedCovectorChartSat : MetricSpace M := F.metricSpace
      u y - u x = dist x y)
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    ∃ v : E, (extChartAt 𝓘(ℝ, E) old x, v) ∈ chartEnergyDomain old ∧
      fiberLegendre (F.chartEnergy old) (extChartAt 𝓘(ℝ, E) old x, v) =
        fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (extChartAt 𝓘(ℝ, E) old x) ∧
      F.chartEnergy old (extChartAt 𝓘(ℝ, E) old x, v) = (1 / 2 : ℝ) := by
  obtain ⟨v, hv, hp, _⟩ :=
    hF.exists_unit_legendre_of_calibrated_endpoints hcomplete hu hxy hsat hd
  exact hF.exists_chart_unit_covector_of_intrinsic old hx hd v (by exact_mod_cast hv) hp

/-- On an arbitrary set of chart points with genuine nontrivial calibrated partners,
the actual original covectors satisfy the unit-energy input of the eikonal jet theorem. -/
theorem chart_unit_legendre_on_of_calibrated_endpoints (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {K : Set E} (hK : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instCalibratedCovectorSetLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (hd : ∀ z ∈ K, MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) old).symm z))
    (hpartner : ∀ z ∈ K, ∃ y : M,
      (extChartAt 𝓘(ℝ, E) old).symm z ≠ y ∧
      let _instCalibratedCovectorSetSat : MetricSpace M := F.metricSpace
      u y - u ((extChartAt 𝓘(ℝ, E) old).symm z) =
        dist ((extChartAt 𝓘(ℝ, E) old).symm z) y) :
    ∀ z ∈ K, ∃ v : E, (z, v) ∈ chartEnergyDomain old ∧
      fiberLegendre (F.chartEnergy old) (z, v) =
        fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) z ∧
      F.chartEnergy old (z, v) = (1 / 2 : ℝ) := by
  intro z hz
  obtain ⟨y, hzy, hsat⟩ := hpartner z hz
  have he := hF.exists_chart_unit_legendre_of_calibrated_endpoints hcomplete old
    ((extChartAt 𝓘(ℝ, E) old).map_target (hK hz)) hu hzy hsat (hd z hz)
  simpa only [(extChartAt 𝓘(ℝ, E) old).right_inv (hK hz)] using he

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
