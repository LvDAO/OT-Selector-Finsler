import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import OTSelector.Geometry.Finsler.ApproximateMidpoint
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Topology.MetricSpace.LengthMetricProper
import OTSelector.Topology.MetricSpace.MetricGeodesic

/-!
## Lemma skeleton

* **Conditions:** A continuous reversible Finsler norm on a finite-dimensional C1 Hausdorff preconnected manifold, complete for its genuine length metric.
* **Objects:** Properness of the same metric and an isometric interval joining any two points.
* **Proof detail:** Derive approximate splitting from the length infimum and local compactness from finite-dimensional charts. Apply generic metric properness and metric geodesic construction.

## Mathematical sources

* Anton Petrunin, *Lectures on metric geometry*, Lecture 1, Section L, Theorem 1.30 (Hopf–Rinow), Exercise 1.31 and proof, pp. 18–19.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18
* Anton Petrunin, *Lectures on metric geometry*, Lecture 1, Section L, Proposition 1.29 and its preceding compact approximate-midpoint argument, p. 18; Section I, p. 13, defines a geodesic as an isometric interval.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 4, p. 313: the length integral, induced distance and minimizing curves.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11

**Relationship to the sources:** Metric Hopf–Rinow and proper-length-space geodesic existence specialized to the constructed Finsler metric. Smoothness and differential geodesic identification are outside these statements.
-/

/-!
# Metric Hopf--Rinow for the original Finsler length distance

Completeness of the original length metric implies compactness of its closed balls.
Every pair of points is then joined by an isometric interval of length equal to their
original distance. Both approximate splitting and local compactness are derived from
the given finite-dimensional manifold and continuous Finsler norm.

These are metric minimizing segments. Their smoothness, Euler--Lagrange equations and
global continuation of a prescribed geodesic are separate geometric steps.
-/

open Set Metric Manifold
open scoped ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  (F : ContinuousFinslerNorm E M)

/-- The actual length metric satisfies the generic approximate splitting property. -/
theorem lengthMetric_approximateSplit : @MetricApproximateSplit M F.metricSpace := by
  let : MetricSpace M := F.metricSpace
  intro x y r hr hrd ε hε
  exact F.exists_lengthMetric_approximate_split x y hr hrd hε

/-- Completeness of the original length metric implies compactness of every closed ball. -/
theorem properSpace_of_complete (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) :
    @ProperSpace M F.metricSpace.toPseudoMetricSpace := by
  let : MetricSpace M := F.metricSpace
  let : CompleteSpace M := hcomplete
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  exact F.lengthMetric_approximateSplit.properSpace

/-- Any two points are joined by an isometric interval for the complete original length metric. -/
theorem exists_lengthMetric_isometric_interval
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (x y : M) :
    letI : MetricSpace M := F.metricSpace
    ∃ γ : Icc (0 : ℝ) (dist x y) → M, Isometry γ ∧
      γ ⟨0, ⟨le_rfl, dist_nonneg⟩⟩ = x ∧
      γ ⟨dist x y, ⟨dist_nonneg, le_rfl⟩⟩ = y := by
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  exact exists_isometric_interval_of_approximate_split F.lengthMetric_approximateSplit x y

end OTSelector.Geometry.ContinuousFinslerNorm
