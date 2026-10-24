import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.UniformSpace.Cauchy
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Geodesic.LocalMinimizing
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Geodesic.Proofs.MaximalExtension
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthMetric

/-!
## Lemma skeleton

* **Conditions:** A finite-dimensional smooth strongly convex reversible Finsler structure and a prescribed nonzero actual tangent. Global results additionally assume a Hausdorff preconnected manifold complete for its own length metric.
* **Objects:** Local and unique global intrinsic Euler–Lagrange curves with prescribed tangent, smoothness, constant original speed and locally minimizing subsegments.
* **Proof detail:** Start a genuine local solution, derive local minimality, extend through every finite endpoint, glue compatible intervals, and apply connected-domain uniqueness. Package the consequences for the same actual curve.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* J. C. Álvarez Paiva; A. C. Thompson, *Volumes on Normed and Finsler Spaces, MSRI Publications 50 (2004)*, Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.
  https://library.slmath.org/books/Book50/files/02AT.pdf#page=22
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 (Picard–Lindelöf) and Lemma 2.3 (regularity), p. 38.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, Lemma 2.14 and Corollary 2.15, pp. 52–53, including the explicit left-endpoint version.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=63

**Relationship to the sources:** Synthesis of local geodesic/spray theory and maximal ODE continuation. Local minimality is derived, and the global conclusion is completeness of a prescribed geodesic rather than global minimization of every long segment.
-/

/-!
# Complete intrinsic Finsler Euler--Lagrange curves with prescribed tangent

Actual local Finsler solutions start from any prescribed nonzero manifold tangent.
The intrinsic equation makes every such germ locally minimizing for the original
Finsler length distance. These local properties combine with complete-metric
continuation and uniqueness to give a unique solution for all real times.
-/

open Set Filter Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- Any prescribed nonzero actual manifold tangent initiates an intrinsic local
Euler--Lagrange solution. The initial vector is in the genuine tangent fiber. -/
theorem exists_local_eulerLagrange_of_tangent (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {v : TangentSpace 𝓘(ℝ, E) x₀} (hv : v ≠ 0) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ c : ℝ → M,
      c t₀ = x₀ ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
        (⟨x₀, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∧
      F.IsEulerLagrangeOn c (Ioo (t₀ - ε) (t₀ + ε)) := by
  let w := (tangentFiberModelEquiv x₀).symm v
  have hw : w ≠ 0 := by
    intro h
    apply hv
    calc
      v = tangentFiberModelEquiv x₀ w :=
        ((tangentFiberModelEquiv x₀).apply_symm_apply v).symm
      _ = 0 := by rw [h, _root_.map_zero]
  obtain ⟨ε, hε, c, hc₀, hv₀, _, _, x, hcx, hx, hEL⟩ :=
    hF.exists_localEulerLagrange x₀ hw t₀
  refine ⟨ε, hε, c, hc₀, ?_, ?_⟩
  · simpa only [w, ContinuousLinearEquiv.apply_symm_apply] using hv₀
  · rw [hcx]
    exact F.isEulerLagrangeOn_chart_symm x₀ isOpen_Ioo (hx.of_le (by simp))
      (fun t ht ↦ (hEL t ht).1) (fun t ht ↦ (hEL t ht).2)

/-- Every intrinsic nonzero-velocity Euler--Lagrange germ minimizes the original
Finsler distance on each sufficiently short ordered subsegment around its time. -/
theorem locally_minimizing_of_isEulerLagrangeAt [T2Space M]
    (hF : F.IsSmoothStronglyConvex) {c : ℝ → M} {t₀ : ℝ}
    (hc : F.IsEulerLagrangeAt c t₀) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    ∃ δ > (0 : ℝ),
      ∀ s ∈ Icc (t₀ - δ) (t₀ + δ), ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), s ≤ t →
        F.lengthEDist (c s) (c t) = Manifold.pathELength 𝓘(ℝ, E) c s t := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  obtain ⟨old, U, hU, ht₀, hmap, hx, hphase, hEL⟩ := hc
  obtain ⟨δ, hδ, hsub, hmin⟩ :=
    hF.chartEulerLagrange_locally_minimizing old hU ht₀ hx hphase hEL
  let d := (extChartAt 𝓘(ℝ, E) old).symm ∘ (extChartAt 𝓘(ℝ, E) old ∘ c)
  have heq : EqOn c d U := by
    intro t ht
    exact ((extChartAt 𝓘(ℝ, E) old).left_inv (hmap ht)).symm
  refine ⟨δ, hδ, ?_⟩
  intro s hs t ht hst
  have hlength := Manifold.pathELength_congr (I := 𝓘(ℝ, E))
    (γ := c) (γ' := d) (a := s) (b := t)
    (fun u hu ↦ heq (hsub ((Icc_subset_Icc hs.1 ht.2) hu)))
  rw [hlength, heq (hsub hs), heq (hsub ht)]
  exact hmin s hs t ht hst

variable [T2Space M] [PreconnectedSpace M]

/-- On a manifold complete for the original Finsler length metric, each prescribed
nonzero actual tangent determines exactly one intrinsic Euler--Lagrange curve on all
real times. -/
theorem exists_unique_global_eulerLagrange (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (x₀ : M) {v : TangentSpace 𝓘(ℝ, E) x₀} (hv : v ≠ 0) (t₀ : ℝ) :
    ∃! c : ℝ → M, F.IsEulerLagrangeOn c univ ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
        (⟨x₀, v⟩ : TangentBundle 𝓘(ℝ, E) M) := by
  obtain ⟨ε, hε, c₀, _, hv₀, hc₀⟩ := hF.exists_local_eulerLagrange_of_tangent x₀ hv t₀
  obtain ⟨c, hc, hvc, _⟩ := hF.exists_global_eulerLagrange_of_local hcomplete hε hc₀
  have hstart := hvc.trans hv₀
  refine ⟨c, ⟨hc, hstart⟩, ?_⟩
  rintro d ⟨hd, hvd⟩
  funext t
  exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ
    hd hc (mem_univ t₀) (hvd.trans hstart.symm) (mem_univ t)

/-- The unique complete Euler--Lagrange curve has its prescribed actual tangent,
is smooth with constant original speed, and minimizes the original length distance
on every sufficiently short subsegment around each time. -/
theorem exists_complete_eulerLagrange (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (x₀ : M) {v : TangentSpace 𝓘(ℝ, E) x₀} (hv : v ≠ 0) (t₀ : ℝ) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    ∃ c : ℝ → M,
      c t₀ = x₀ ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
        (⟨x₀, v⟩ : TangentBundle 𝓘(ℝ, E) M) ∧
      F.IsEulerLagrangeOn c univ ∧
      ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c ∧
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) =
        F.toFun ⟨x₀, v⟩) ∧
      (∀ u : ℝ, ∃ δ > (0 : ℝ),
        ∀ s ∈ Icc (u - δ) (u + δ), ∀ t ∈ Icc (u - δ) (u + δ), s ≤ t →
          F.lengthEDist (c s) (c t) = Manifold.pathELength 𝓘(ℝ, E) c s t) ∧
      ∀ d : ℝ → M, F.IsEulerLagrangeOn d univ →
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t₀, (1 : ℝ)⟩ =
          (⟨x₀, v⟩ : TangentBundle 𝓘(ℝ, E) M) → d = c := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  obtain ⟨c, ⟨hc, hstart⟩, hunique⟩ :=
    hF.exists_unique_global_eulerLagrange hcomplete x₀ hv t₀
  refine ⟨c, congrArg (fun z : TangentBundle 𝓘(ℝ, E) M ↦ z.1) hstart, hstart,
    hc, contMDiffOn_univ.mp (hF.contMDiffOn_of_isEulerLagrangeOn hc), ?_, ?_, ?_⟩
  · intro t
    exact (hF.speed_eq_of_isEulerLagrangeOn hc isPreconnected_univ
      (mem_univ t) (mem_univ t₀)).trans (congrArg F.toFun hstart)
  · intro u
    exact hF.locally_minimizing_of_isEulerLagrangeAt (hc u (mem_univ u))
  · intro d hd hdv
    exact hunique d ⟨hd, hdv⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
