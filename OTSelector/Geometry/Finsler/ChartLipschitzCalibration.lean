import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Calibration.ChartCurve
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.LipschitzDifferential

/-!
# Geometry.Finsler.ChartLipschitzCalibration

* **Conditions:** The original globally Lipschitz potential equals a supplied affine expression in an actual open chart tube.
* **Objects:** The actual chart covector is bounded by K times the original Finsler length, and calibrates when K=1.
* **Proof detail:** Test differentiability on actual coordinate curves and apply the original metric differential Lipschitz bound.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The local differential bound is derived from the original global metric condition, not an independent geometric oracle.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerChartLipschitzCalibration.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerChartLipschitzCalibration`; the selected original proof blocks follow. -/
section

/-!
# Original Lipschitz calibration in actual chart coordinates

An affine expression for the original global Lipschitz potential in a genuine chart
implies its original Finsler covector bound there. The bound is obtained by testing
actual coordinate curves, rather than assumed as independent local geometry.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- A genuine affine chart expression of the original Lipschitz potential gives its
covector bound against the original chart length, in every velocity direction. -/
theorem abs_chart_covector_le_chartLength (hF : F.IsSmoothStronglyConvex)
    (old : M) {u : M → ℝ} {K : ℝ≥0}
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith K u)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    {y : E} (hy : y ∈ U) (v : E) :
    |p v| ≤ (K : ℝ) * (F.chartLength old (y, v) : ℝ) := by
  let γ : ℝ → E := fun t ↦ y + t • v
  let c : ℝ → M := (extChartAt 𝓘(ℝ, E) old).symm ∘ γ
  have hγ : HasDerivAt γ v 0 := by
    simpa only [γ, Pi.add_apply, id_eq, one_smul, zero_add] using!
      (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hγ0 : γ 0 = y := by simp [γ]
  have htarget : γ 0 ∈ (extChartAt 𝓘(ℝ, E) old).target := hγ0 ▸ hsub hy
  have hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) old).symm (γ 0) := by
    simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm htarget
  have hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 :=
    hi.comp 0 hγ.differentiableAt.mdifferentiableAt
  have hnear : (u ∘ c) =ᶠ[𝓝 0] (fun t ↦ p (γ t) + C) := by
    filter_upwards [hγ.continuousAt.preimage_mem_nhds (hγ0 ▸ hU.mem_nhds hy)] with t ht
    exact heq (γ t) ht
  have hd : HasDerivAt (u ∘ c) (p v) 0 :=
    ((p.hasFDerivAt.comp_hasDerivAt 0 hγ).add_const C).congr_of_eventuallyEq hnear
  have hb := hF.abs_deriv_comp_le_speed_of_lipschitz hu hc hd.differentiableAt
  rw [hd.deriv] at hb
  have hs := F.toFun_chartCurve_velocity old htarget hγ
  change F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩) = _ at hs
  rw [hs, hγ0] at hb
  exact hb

/-- A unit Lipschitz chart calibration supplies the one-sided original length bound
used by the calibrated energy and endpoint nondegeneracy theorems. -/
theorem chart_covector_le_chartLength (hF : F.IsSmoothStronglyConvex)
    (old : M) {u : M → ℝ}
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    {y : E} (hy : y ∈ U) (v : E) : p v ≤ (F.chartLength old (y, v) : ℝ) := by
  have hb := hF.abs_chart_covector_le_chartLength old hu hU hsub p heq hy v
  exact (le_abs_self (p v)).trans (by simpa only [NNReal.coe_one, one_mul] using hb)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
