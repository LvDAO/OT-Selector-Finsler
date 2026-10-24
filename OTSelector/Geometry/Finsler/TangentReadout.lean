import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.ODE.Basic
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Geodesic.Proofs.MaximalExtension
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Manifold.TangentChartCurve
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTangentReadout.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTangentReadout`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.TangentReadout

* **Conditions:** An intrinsic Euler–Lagrange germ and a legal manifold chart; a specified actual tangent value for the readout consequences.
* **Objects:** Exact actual coordinate position/velocity and original position–momentum readout.
* **Proof detail:** Apply the manifold chart chain rule and inverse-chart cancellation to the actual tangent identity, then compose with the original fiber Legendre map.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Reading actual initial tangents in Finsler coordinates

Intrinsic Euler--Lagrange regularity identifies the true tangent chart with the actual
position and time derivative. Prescribing the initial tangent therefore prescribes the
original position-momentum state, without a separate coordinate compatibility assumption.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

/-- The actual tangent chart reads precisely the position and actual time derivative. -/
theorem chartTangent_of_isEulerLagrangeAt (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M))
      (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) =
        ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) ∧
    ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) ∈
      chartEnergyDomain old := by
  obtain ⟨J, hJ, ht, hm, hy, hphase, _⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt hc old hx
  have heq : c =ᶠ[𝓝 t] (extChartAt 𝓘(ℝ, E) old).symm ∘
      (extChartAt 𝓘(ℝ, E) old ∘ c) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact ((extChartAt 𝓘(ℝ, E) old).left_inv (hm hs)).symm
  have hp := tangentMap_chart_symm_curve old (hphase t ht).1
    (((hy.contDiffAt (hJ.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt)
  refine ⟨?_, hphase t ht⟩
  rw [(tangentCurve_eq_of_eventuallyEq heq).trans hp, (extChartAt _ _).right_inv]
  rw [tangentChart_target]
  exact ⟨(hphase t ht).1, mem_univ _⟩

/-- An actual prescribed initial tangent gives the literal original chart phase. -/
theorem chartPhase_of_tangent_eq (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (old : M)
    {z : E × E} (hz : z ∈ chartEnergyDomain old)
    (hi : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) :
    ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) = z := by
  have hb : c t = (extChartAt 𝓘(ℝ, E) old).symm z.1 := by
    have h := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) hi
    rw [tangentChart_symm_eq old hz.1 z.2] at h
    exact h
  have hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    rw [hb]
    exact (extChartAt 𝓘(ℝ, E) old).map_target hz.1
  rw [← (hF.chartTangent_of_isEulerLagrangeAt hc old hx).1, hi,
    (extChartAt _ _).right_inv]
  rw [tangentChart_target]
  exact ⟨hz.1, mem_univ _⟩

/-- The momentum of a prescribed actual tangent is its original fiber Legendre image. -/
theorem chartMomentum_of_tangent_eq (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (old : M)
    {z : E × E} (hz : z ∈ chartEnergyDomain old)
    (hi : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) :
    eulerLagrangePhaseLift (F.chartEnergy old) (extChartAt 𝓘(ℝ, E) old ∘ c) t =
      parametricLegendre (F.chartEnergy old) z := by
  exact congrArg (parametricLegendre (F.chartEnergy old))
    (hF.chartPhase_of_tangent_eq hc old hz hi)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
