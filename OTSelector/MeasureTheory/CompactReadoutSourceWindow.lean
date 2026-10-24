import LeanLevy.RandomMeasure.PoissonRandomMeasure
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option
import LeanPool.Vlasov.OT.Coupling
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Matrix.MeasurableSpace
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.StrongLaw
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Topology.MetricSpace.HausdorffDimension
import OTSelector.MeasureTheory.LocalFiniteMeasureCountableTests
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneCompactReadoutSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneCompactReadoutSupport`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.CompactReadoutSourceWindow

## Lemma skeleton

* **Conditions:** A compactly supported edge or joint macro-edge test in the finite-dimensional spatial carrier.
* **Objects:** One [0,1] compact edge cutoff and a bounded open finite-volume source window carrying the actual supports.
* **Proof detail:** Project the compact support, construct a compact cutoff equal to one there and enclose its source projection in a bounded open ball.

## Mathematical sources

- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=143): Section 1.10.1, Lemma 1.10.1, pp. 134–135, and Exercise 1.10.6, p. 136.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22): Theorem 263A, pp. 22–24: linear change of variables and absolute determinant.

Source relation (composition): Explicit support/window construction; no global finite plan mass or projection properness is required.
-/

/-!
# Actual compact readouts have finite open source windows

A joint macro and edge test supplies one compact edge cutoff. Both tests fit
inside an automatically chosen bounded open source window of finite volume.
-/
open Set Function MeasureTheory TopologicalSpace
open scoped Topology ENNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {ι : Type*} [Fintype ι]
local notation "V" => (ι → ℝ)
local notation "Point" => (V × ℝ)
local notation "Edge" => (Point × Point)

/-- Compact edge tests supply their own finite source window. -/
theorem exists_finite_open_source_window_of_compact_readout (χ : C_c(Edge, ℝ)) :
    ∃ U : Set V, IsOpen U ∧ volume U ≠ ⊤ ∧
      tsupport χ ⊆ {e : Edge | e.1.1 ∈ U} := by
  have hc : IsCompact ((fun e : Edge ↦ e.1.1) '' tsupport χ) :=
    χ.hasCompactSupport.image continuous_fst.fst
  obtain ⟨R, hR⟩ := hc.isBounded.subset_ball (0 : V)
  refine ⟨Metric.ball 0 R, Metric.isOpen_ball, measure_ball_lt_top.ne, ?_⟩
  intro e he
  exact hR ⟨e, he, rfl⟩

/-- A joint test produces one scalar edge cutoff and one finite source window,
independently of the macro coordinate at which its edge slice is evaluated. -/
theorem exists_compact_edge_cutoff_and_source_window (G : C_c(V × Edge, ℝ)) :
    ∃ χ : C_c(Edge, ℝ),
      EqOn χ 1 (Prod.snd '' tsupport G) ∧ (∀ e, χ e ∈ Icc 0 1) ∧
      ∃ U : Set V, IsOpen U ∧ volume U ≠ ⊤ ∧
        tsupport χ ⊆ {e : Edge | e.1.1 ∈ U} ∧
        tsupport G ⊆ {p : V × Edge | p.2.1.1 ∈ U} := by
  obtain ⟨χ, hχone, hχbounds⟩ := LocalFiniteMeasure.exists_compact_cutoff
    (G.hasCompactSupport.image continuous_snd)
  obtain ⟨U, hU, hUf, hχU⟩ := exists_finite_open_source_window_of_compact_readout χ
  refine ⟨χ, hχone, hχbounds, U, hU, hUf, hχU, ?_⟩
  intro p hp
  have he : p.2 ∈ tsupport χ := subset_tsupport χ (by
    change χ p.2 ≠ 0
    rw [hχone ⟨p, hp, rfl⟩]
    exact one_ne_zero)
  exact hχU he

end OTSelector.Reconstruction

end
end
