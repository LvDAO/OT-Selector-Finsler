import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Extend
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
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.UniformSpace.Cauchy
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.Continuation
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Compatible interval gluing and global geodesic extension

Main declarations: exists_eulerLagrangeOn_of_interval_cover; exists_global_eulerLagrange_of_local.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.Gluing`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Locally unique intrinsic Finsler solutions on intervals all containing the same initial time, with equal actual initial tangent; an open target time set covered by those intervals.
* **Objects:** One actual manifold-valued solution on the union, preserving the initial tangent.
* **Proof detail:** Connected-interval uniqueness makes chosen local representatives agree on every overlap. Choose a representative at each time and use local agreement to verify the equation and tangent.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11

**Relationship to the sources:** Intrinsic implementation of the overlap-gluing construction preceding the maximal-solution theorem.
-/

/-!
# Gluing compatible intrinsic Finsler solutions on interval covers

Each interval in the cover contains the same initial time and carries a genuine
solution with the same actual initial tangent. Connected-interval uniqueness makes
the locally chosen values agree on every overlap. Their union therefore satisfies
the actual local equation and preserves the original initial tangent.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Actual tangent velocities are unchanged when two manifold curves agree near the time. -/
theorem tangentCurve_eq_of_eventuallyEq {c d : ℝ → M} {t : ℝ}
    (h : c =ᶠ[𝓝 t] d) :
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨t, (1 : ℝ)⟩ := by
  refine TotalSpace.ext h.eq_of_nhds ?_
  rw [tangentMap, h.eq_of_nhds, tangentMap, h.mfderiv_eq]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E] [T2Space M]
  {F : ContinuousFinslerNorm E M}

/-- Genuine solutions on an interval cover with one common actual initial tangent glue
to an intrinsic solution on the whole open covered set. Compatibility is derived. -/
theorem exists_eulerLagrangeOn_of_interval_cover (hF : F.IsSmoothStronglyConvex)
    {I : Set ℝ} (hI : IsOpen I) {t₀ : ℝ} (ht₀ : t₀ ∈ I)
    (v : TangentBundle 𝓘(ℝ, E) M)
    (hcover : ∀ t ∈ I, ∃ a b : ℝ, ∃ c : ℝ → M,
      t₀ ∈ Ioo a b ∧ t ∈ Ioo a b ∧ F.IsEulerLagrangeOn c (Ioo a b) ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ = v) :
    ∃ c : ℝ → M, F.IsEulerLagrangeOn c I ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ = v := by
  classical
  choose a b γ hcenter htime hγ hvelocity using fun t : I ↦ hcover t t.property
  let c : ℝ → M := fun t ↦ if ht : t ∈ I then γ ⟨t, ht⟩ t else v.1
  have heq (u : I) : c =ᶠ[𝓝 (u : ℝ)] γ u := by
    filter_upwards [hI.mem_nhds u.property, isOpen_Ioo.mem_nhds (htime u)]
      with t htI htu
    dsimp only [c]
    rw [dite_eq_left htI]
    let w : I := ⟨t, htI⟩
    exact hF.eqOn_of_isEulerLagrangeOn (isOpen_Ioo.inter isOpen_Ioo)
      ((convex_Ioo (a w) (b w)).inter (convex_Ioo (a u) (b u))).isPreconnected
      ((hγ w).mono inter_subset_left) ((hγ u).mono inter_subset_right)
      ⟨hcenter w, hcenter u⟩ ((hvelocity w).trans (hvelocity u).symm)
      ⟨htime w, htu⟩
  refine ⟨c, ?_, ?_⟩
  · intro t ht
    exact (hγ ⟨t, ht⟩ t (htime ⟨t, ht⟩)).congr (heq ⟨t, ht⟩).symm
  · exact (tangentCurve_eq_of_eventuallyEq (heq ⟨t₀, ht₀⟩)).trans (hvelocity ⟨t₀, ht₀⟩)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.Global`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** A complete original length metric on a finite-dimensional Hausdorff preconnected smooth strongly convex Finsler manifold; one actual local nonzero-velocity solution.
* **Objects:** A global intrinsic Euler–Lagrange curve agreeing with the given local germ and initial tangent.
* **Proof detail:** Take the supremum of symmetric existence radii. Glue at a finite supremum and extend through both endpoints to contradict maximality; unbounded radii cover the real line.

## Mathematical sources

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, Lemma 2.14 and Corollary 2.15, pp. 52–53, including the explicit left-endpoint version.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=63
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11

**Relationship to the sources:** Manifold synthesis of unique maximal-solution construction with the locally proved complete-Finsler continuation criterion.
-/

/-!
# Global continuation of actual Finsler Euler--Lagrange solutions

Consider all symmetric time intervals carrying a solution with the given actual initial
tangent. If their radii were bounded, interval gluing would construct a solution up to
the supremum radius. Original metric completeness extends this actual limiting solution
past both endpoints, contradicting the bound. Unbounded radii then cover the entire real
line, and the same gluing theorem gives one global solution preserving the original germ.
-/

open Set Filter Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Completeness of the original Finsler distance continues every genuine local solution
to all real times, preserving its actual initial tangent and its entire original interval. -/
theorem exists_global_eulerLagrange_of_local (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {c₀ : ℝ → M} {t₀ r₀ : ℝ} (hr₀ : 0 < r₀)
    (hc₀ : F.IsEulerLagrangeOn c₀ (Ioo (t₀ - r₀) (t₀ + r₀))) :
    ∃ c : ℝ → M, F.IsEulerLagrangeOn c univ ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c₀ ⟨t₀, (1 : ℝ)⟩ ∧
      EqOn c c₀ (Ioo (t₀ - r₀) (t₀ + r₀)) := by
  let v := tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c₀ ⟨t₀, (1 : ℝ)⟩
  let S : Set ℝ := {r | 0 < r ∧ ∃ c : ℝ → M,
    F.IsEulerLagrangeOn c (Ioo (t₀ - r) (t₀ + r)) ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ = v}
  have hr₀S : r₀ ∈ S := ⟨hr₀, c₀, hc₀, rfl⟩
  have hSne : S.Nonempty := ⟨r₀, hr₀S⟩
  have hunbounded : ¬ BddAbove S := by
    intro hbound
    have hR : 0 < sSup S := lt_of_lt_of_le hr₀ (le_csSup hbound hr₀S)
    have htR : t₀ ∈ Ioo (t₀ - sSup S) (t₀ + sSup S) := ⟨by linarith, by linarith⟩
    obtain ⟨c, hc, hv⟩ := hF.exists_eulerLagrangeOn_of_interval_cover isOpen_Ioo htR v (by
      intro t ht
      have habs : |t - t₀| < sSup S := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup hSne habs
      obtain ⟨hrpos, γ, hγ, hγv⟩ := hr
      refine ⟨t₀ - r, t₀ + r, γ, ⟨by linarith, by linarith⟩, ?_, hγ, hγv⟩
      exact ⟨by linarith [(abs_lt.mp htr).1], by linarith [(abs_lt.mp htr).2]⟩)
    obtain ⟨δr, hδr, cr, hreq, hcr⟩ :=
      hF.exists_eulerLagrange_extension_right hcomplete (by linarith : t₀ - sSup S < t₀ + sSup S) hc
    obtain ⟨δl, hδl, cl, hleq, hcl⟩ :=
      hF.exists_eulerLagrange_extension_left hcomplete
        (by linarith : t₀ - sSup S < t₀ + sSup S + δr) hcr
    let δ := min δl δr
    have hδ : 0 < δ := lt_min hδl hδr
    have hvext : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) cl ⟨t₀, (1 : ℝ)⟩ = v := by
      have htl : t₀ ∈ Ioo (t₀ - sSup S) (t₀ + sSup S + δr) :=
        ⟨by linarith, by linarith⟩
      exact (tangentCurve_eq_of_eventuallyEq
        (hleq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds htl))).trans
          ((tangentCurve_eq_of_eventuallyEq
            (hreq.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds htR))).trans hv)
    have hbigger : sSup S + δ ∈ S := by
      refine ⟨by positivity, cl, hcl.mono ?_, hvext⟩
      intro t ht
      have hδl' : δ ≤ δl := min_le_left _ _
      have hδr' : δ ≤ δr := min_le_right _ _
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have := le_csSup hbound hbigger
    linarith
  obtain ⟨c, hc, hv⟩ := hF.exists_eulerLagrangeOn_of_interval_cover
    isOpen_univ (mem_univ t₀) v (by
      intro t _
      obtain ⟨r, hr, htr⟩ := not_bddAbove_iff.mp hunbounded |t - t₀|
      obtain ⟨hrpos, γ, hγ, hγv⟩ := hr
      refine ⟨t₀ - r, t₀ + r, γ, ⟨by linarith, by linarith⟩, ?_, hγ, hγv⟩
      exact ⟨by linarith [(abs_lt.mp htr).1], by linarith [(abs_lt.mp htr).2]⟩)
  refine ⟨c, hc, hv, ?_⟩
  exact hF.eqOn_of_isEulerLagrangeOn isOpen_Ioo isPreconnected_Ioo
    (hc.mono (subset_univ _)) hc₀ ⟨by linarith, by linarith⟩ hv

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
