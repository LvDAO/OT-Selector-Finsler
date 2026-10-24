import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Complete
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.MetricDifferential

/-!
# Geometry.Finsler.LipschitzDifferential

* **Conditions:** A real potential Lipschitz for the original Finsler distance, with actual differentiability at the tested point/curve.
* **Objects:** Bounds on its actual curve derivative and on every tangent differential by K times original Finsler norm.
* **Proof detail:** Apply the metric differential to difference quotients; realize arbitrary nonzero tangent vectors by genuine local Euler–Lagrange curves.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Completeness and a separately supplied differential calibration bound are unnecessary.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLipschitzDifferential.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLipschitzDifferential`; the selected original proof blocks follow. -/
section

/-!
# Differential bounds from the original Finsler Lipschitz condition

The actual metric differential bounds derivatives of a Lipschitz real potential along
any differentiable manifold curve. Realizing a prescribed tangent by the original local
Euler--Lagrange curve gives the bound on every tangent vector, without a completeness
or separately supplied differential-bound assumption.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- Original metric Lipschitz continuity bounds the actual derivative along a curve
by its original Finsler speed. -/
theorem abs_deriv_comp_le_speed_of_lipschitz (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} {K : ℝ≥0}
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith K u)
    {c : ℝ → M} {t₀ : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀)
    (hd : DifferentiableAt ℝ (u ∘ c) t₀) :
    |deriv (u ∘ c) t₀| ≤
      (K : ℝ) * (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩) : ℝ) := by
  let : MetricSpace M := F.metricSpace
  have hl := hd.hasDerivAt.tendsto_slope.norm
  rw [Real.norm_eq_abs] at hl
  have hr := (hF.tendsto_dist_div_abs_sub_of_mdifferentiableAt hc).const_mul (K : ℝ)
  apply le_of_tendsto_of_tendsto' hl hr
  intro t
  rw [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs,
    ← div_eq_inv_mul]
  have hb := hu.dist_le_mul (c t) (c t₀)
  rw [Real.dist_eq, dist_comm (c t) (c t₀)] at hb
  simpa only [Function.comp_apply, mul_div_assoc] using
    div_le_div_of_nonneg_right hb (abs_nonneg (t - t₀))

set_option backward.isDefEq.respectTransparency false in
/-- The true manifold differential obeys the same bound on the actual curve tangent. -/
theorem abs_mfderiv_curve_le_speed_of_lipschitz (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} {K : ℝ≥0}
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith K u)
    {c : ℝ → M} {t₀ : ℝ}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀)
    (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t₀)) :
    abs (α := ℝ) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t₀)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀ 1)) ≤
      (K : ℝ) * (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩) : ℝ) := by
  have hcomp : DifferentiableAt ℝ (u ∘ c) t₀ :=
    (mdifferentiableAt_iff_differentiableAt.mp (hd.comp t₀ hc))
  have heq : deriv (u ∘ c) t₀ =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c t₀)
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t₀ 1) := by
    have he := mfderiv_comp_apply t₀ hd hc (1 : ℝ)
    rw [mfderiv_eq_fderiv] at he
    exact he
  rw [← heq]
  exact hF.abs_deriv_comp_le_speed_of_lipschitz hu hc hcomp

set_option backward.isDefEq.respectTransparency false in
/-- A potential Lipschitz for the original length metric has the corresponding dual
Finsler bound at every differentiability point and every actual tangent vector. -/
theorem abs_mfderiv_le_finsler_of_lipschitz (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} {K : ℝ≥0}
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith K u)
    {x : M} (hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    abs (α := ℝ) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x v) ≤ (K : ℝ) * (F.toFun ⟨x, v⟩ : ℝ) := by
  by_cases hv : v = 0
  · subst v
    simp [F.map_zero]
  obtain ⟨ε, hε, c, hc₀, htan, hEL⟩ :=
    hF.exists_local_eulerLagrange_of_tangent x hv 0
  have h0 : (0 : ℝ) ∈ Ioo (0 - ε) (0 + ε) := by constructor <;> linarith
  have hc := (hF.contMDiffAt_of_isEulerLagrangeAt (hEL 0 h0)).mdifferentiableAt (by simp)
  have hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c 0) := by rwa [hc₀]
  have hbound := hF.abs_mfderiv_curve_le_speed_of_lipschitz hu hc hdu
  have hm := congrArg (fun z : TangentBundle 𝓘(ℝ, E) M ↦
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u z.1 z.2) htan
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c 0)
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c 0 1) = _ at hm
  rw [hm, htan] at hbound
  exact hbound

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
