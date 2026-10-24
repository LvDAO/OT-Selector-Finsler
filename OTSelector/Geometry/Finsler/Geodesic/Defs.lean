import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic

/-!
## Mathematical sources

Conditions: the stated smooth manifold and continuous Finsler norm.
Objects: chartwise nonzero-velocity Euler–Lagrange predicates.
Proof detail: literal definitions; existence, covariance, minimality and completeness are later theorems.

- Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*: Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives. https://www.jirka.org/ra/realanal2.pdf
- Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*: Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation. https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
- Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*: Section 2.2, Theorem 2.2 (Picard–Lindelöf) and Lemma 2.3 (regularity), p. 38. https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49

Source relation: local chart encoding; no local distance minimality is built into the predicates.
-/



/-!
# Intrinsic Euler--Lagrange geodesic predicates

`IsEulerLagrangeAt` and `IsEulerLagrangeOn` express the original chartwise
nonzero-velocity equation. Local minimality and global completeness are proved
in the later `Basic`, `LocalMinimizing` and `Complete` modules.

The definitions below are extracted verbatim from `Geodesic.Basic`; its
mathematical-source documentation is retained there.
-/

open Set Filter Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ContinuousFinslerNorm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual curve is a nonzero-velocity Euler--Lagrange solution near a time,
in one genuine atlas chart containing the local curve. -/
def IsEulerLagrangeAt (F : ContinuousFinslerNorm E M) (c : ℝ → M) (t : ℝ) : Prop :=
  ∃ old : M, ∃ U : Set ℝ, IsOpen U ∧ t ∈ U ∧
    MapsTo c U (extChartAt 𝓘(ℝ, E) old).source ∧
    ContDiffOn ℝ 2 (extChartAt 𝓘(ℝ, E) old ∘ c) U ∧
    (∀ s ∈ U, ((extChartAt 𝓘(ℝ, E) old ∘ c) s,
      deriv (extChartAt 𝓘(ℝ, E) old ∘ c) s) ∈ chartEnergyDomain old) ∧
    ∀ s ∈ U, HasDerivAt
      (fun r ↦ fiberLegendre (F.chartEnergy old)
        ((extChartAt 𝓘(ℝ, E) old ∘ c) r, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) r))
      (baseEnergyDifferential (F.chartEnergy old)
        ((extChartAt 𝓘(ℝ, E) old ∘ c) s, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) s)) s

/-- The actual curve satisfies the local slit Euler--Lagrange equation at every
time of the specified set. At boundary times this asks for a two-sided local solution. -/
def IsEulerLagrangeOn (F : ContinuousFinslerNorm E M) (c : ℝ → M) (I : Set ℝ) : Prop :=
  ∀ t ∈ I, F.IsEulerLagrangeAt c t

end ContinuousFinslerNorm

end OTSelector.Geometry
