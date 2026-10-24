import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedConstantSpeed
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.LipschitzDifferential

/-!
# Geometry.Finsler.PotentialCurveLipschitz

* **Conditions:** The actual nonzero inverse energy-Legendre tangent of a differentiable original 1-Lipschitz potential, along a complete actual curve.
* **Objects:** Original initial speed at most one and a global one-Lipschitz bound for that curve.
* **Proof detail:** Apply Euler radial identity to the actual differential norm bound, then propagate energy/speed and integrate original length.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): Unit speed and metric completeness are not needed for this upper-speed argument.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerPotentialCurveLipschitz.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerPotentialCurveLipschitz`; the selected original proof blocks follow. -/
section

/-!
# Original potential-covector curves are globally one-Lipschitz

Euler homogeneity and the actual differential bound for an original one-Lipschitz
potential bound its nonzero inverse energy-Legendre tangent by one. Original energy
conservation and the derivative-integral length bound propagate this bound along
any complete Euler--Lagrange curve with that actual initial tangent. No unit-speed
or metric-completeness assumption is needed.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- A nonzero tangent whose original energy covector is the actual differential of
an original one-Lipschitz potential has original Finsler length at most one. -/
theorem fiber_speed_le_one_of_potential_covector (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : let _instPotentialSpeedLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x : M} (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    {v : TangentSpace 𝓘(ℝ, E) x} (hv : v ≠ 0)
    (hp : fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    F.toFun ⟨x, v⟩ ≤ 1 := by
  let _instPotentialSpeedFiberNorm : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedAddCommGroup E)
  let _instPotentialSpeedFiberSpace : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
    inferInstanceAs (NormedSpace ℝ E)
  have he : fderiv ℝ (F.fiberEnergy x) v v = 2 * F.fiberEnergy x v :=
    hF.fiberEnergy_euler x hv
  have hb := hF.abs_mfderiv_le_finsler_of_lipschitz hu hdu v
  rw [← hp] at hb
  simp only [NNReal.coe_one, one_mul] at hb
  have hb' := (le_abs_self (fderiv ℝ (F.fiberEnergy x) v v)).trans hb
  have hsq : (F.toFun ⟨x, v⟩ : ℝ) ^ 2 ≤ (F.toFun ⟨x, v⟩ : ℝ) := by
    change _ = 2 * ((F.toFun ⟨x, v⟩ : ℝ) ^ 2 / 2) at he
    nlinarith
  have hle : (F.toFun ⟨x, v⟩ : ℝ) ≤ 1 := by
    nlinarith [sq_nonneg ((F.toFun ⟨x, v⟩ : ℝ) - 1)]
  exact_mod_cast hle

/-- A complete original Euler--Lagrange curve initialized by the actual energy
covector of an original one-Lipschitz potential is globally one-Lipschitz for the
same original length distance, without a supplied unit-speed condition. -/
theorem lipschitzWith_of_complete_potential_covector (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : let _instPotentialCurveLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {x : M} (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x)
    {c : ℝ → M} (hc : F.IsEulerLagrangeOn c univ)
    {v : TangentSpace 𝓘(ℝ, E) x} (hv : v ≠ 0)
    (hinit : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨0, (1 : ℝ)⟩ = ⟨x, v⟩)
    (hp : fderiv ℝ (F.fiberEnergy x) v = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x) :
    let _instPotentialCurveOutput : MetricSpace M := F.metricSpace
    LipschitzWith 1 c := by
  let _instPotentialCurveProof : MetricSpace M := F.metricSpace
  have hl := hF.lipschitzWith_of_isEulerLagrangeOn_univ hc 0
  rw [hinit] at hl
  exact hl.weaken (hF.fiber_speed_le_one_of_potential_covector hu hdu hv hp)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
