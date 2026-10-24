import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Calibration.ChartCurve
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeEnergy

/-!
## Lemma skeleton

* **Conditions:** An intrinsic nonzero-velocity Euler–Lagrange curve for a smooth strongly convex Finsler structure; connectedness of the time set for one global speed value.
* **Objects:** The actual tangent speed, its equality with chart length, its local constancy and positivity.
* **Proof detail:** Identify genuine tangent speed in a chart; transport chart energy conservation; propagate local constancy across a preconnected time set.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf

**Relationship to the sources:** Derived invariant form of the constant-speed part of the geodesic characterization. The chart/germ identities are calculus adapters, not separate named textbook statements.
-/

/-!
# Original speed along intrinsic Finsler Euler--Lagrange curves

Local agreement of actual manifold curves preserves their tangent speed. In a genuine
chart the speed is the original chart length, so actual local energy conservation can
be transported to the manifold without selecting one chart for the whole time interval.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- Locally equal actual manifold curves have the same original tangent speed. -/
theorem speed_eq_of_eventuallyEq (F : ContinuousFinslerNorm E M)
    {c d : ℝ → M} {t : ℝ} (h : c =ᶠ[𝓝 t] d) :
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) =
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩) := by
  congr 1
  apply TotalSpace.ext h.self_of_nhds
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d t := h.mfderiv_eq
  exact heq_of_eq (congrArg (fun A : ℝ →L[ℝ] E ↦ A 1) hd)

/-- Genuine coordinates identify the actual manifold speed with the original chart length. -/
theorem speed_eq_chartLength (F : ContinuousFinslerNorm E M) (old : M)
    {c : ℝ → M} {U : Set ℝ} {t : ℝ} (hU : IsOpen U) (ht : t ∈ U)
    (hmap : MapsTo c U (extChartAt 𝓘(ℝ, E) old).source)
    (hx : DifferentiableAt ℝ (extChartAt 𝓘(ℝ, E) old ∘ c) t) :
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) =
      F.chartLength old ((extChartAt 𝓘(ℝ, E) old ∘ c) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) := by
  have heq : c =ᶠ[𝓝 t]
      ((extChartAt 𝓘(ℝ, E) old).symm ∘ (extChartAt 𝓘(ℝ, E) old ∘ c)) := by
    filter_upwards [hU.mem_nhds ht] with u hu
    exact ((extChartAt 𝓘(ℝ, E) old).left_inv (hmap hu)).symm
  rw [F.speed_eq_of_eventuallyEq heq]
  exact F.toFun_chartCurve_velocity old
    ((extChartAt 𝓘(ℝ, E) old).map_source (hmap ht)) hx.hasDerivAt

namespace IsSmoothStronglyConvex

/-- Every intrinsic actual Euler--Lagrange germ has locally constant original speed. -/
theorem eventually_speed_eq_of_isEulerLagrangeAt (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) :
    ∀ᶠ s in 𝓝 t,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨s, (1 : ℝ)⟩) =
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) := by
  obtain ⟨old, U, hU, ht, hmap, hx, hphase, hEL⟩ := hc
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ht)
  have hcoord (u : ℝ) (hu : u ∈ U) :=
    F.speed_eq_chartLength old hU hu hmap
      ((hx.contDiffAt (hU.mem_nhds hu)).differentiableAt (by norm_num))
  filter_upwards [Metric.ball_mem_nhds t hε] with s hs
  rw [hcoord s (hsub hs), hcoord t ht]
  exact hF.chartLength_eq_of_eulerLagrange old Metric.isOpen_ball
    (convex_ball t ε).isPreconnected (hx.mono hsub)
    (fun u hu ↦ hphase u (hsub hu)) (fun u hu ↦ hEL u (hsub hu))
    hs (Metric.mem_ball_self hε)

/-- Original speed is locally constant on every set carrying the intrinsic local equation. -/
theorem isLocallyConstant_speed_of_isEulerLagrangeOn (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {I : Set ℝ} (hc : F.IsEulerLagrangeOn c I) :
    IsLocallyConstant (fun t : I ↦
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨(t : ℝ), (1 : ℝ)⟩)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro t
  exact continuous_subtype_val.continuousAt.tendsto.eventually
    (hF.eventually_speed_eq_of_isEulerLagrangeAt (hc t t.property))

/-- On a connected time domain, a curve may change charts arbitrarily and still has
one constant original Finsler speed, derived from its actual local equation. -/
theorem speed_eq_of_isEulerLagrangeOn (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {I : Set ℝ} (hc : F.IsEulerLagrangeOn c I)
    (hconn : IsPreconnected I) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨s, (1 : ℝ)⟩) =
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) := by
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hconn
  exact (hF.isLocallyConstant_speed_of_isEulerLagrangeOn hc).apply_eq_of_preconnectedSpace
    ⟨s, hs⟩ ⟨t, ht⟩

end IsSmoothStronglyConvex

/-- The intrinsic slit equation gives strictly positive actual Finsler speed. -/
theorem speed_pos_of_isEulerLagrangeAt (F : ContinuousFinslerNorm E M)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) :
    0 < F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) := by
  obtain ⟨old, U, hU, ht, hmap, hx, hphase, _⟩ := hc
  rw [F.speed_eq_chartLength old hU ht hmap
    ((hx.contDiffAt (hU.mem_nhds ht)).differentiableAt (by norm_num))]
  exact F.chartLength_pos old (hphase t ht)

end OTSelector.Geometry.ContinuousFinslerNorm
