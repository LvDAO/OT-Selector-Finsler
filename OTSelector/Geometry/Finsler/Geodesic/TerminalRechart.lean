import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Calibration.ChartCurve
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Geodesic.Proofs.Continuation
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeEnergy
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTerminalRechart.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTerminalRechart`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.TerminalRechart

* **Conditions:** A finite-dimensional smooth strongly convex Finsler manifold with complete original length metric, and a C2 nonzero-velocity chart Euler–Lagrange solution on an open finite interval.
* **Objects:** A terminal position endpoint, continuous closed-interval extension, and compact terminal coordinate trace in the endpoint chart.
* **Proof detail:** Energy conservation bounds speed, metric completeness supplies the position limit, and chart covariance transfers the interior differential equation near that endpoint.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Kenneth R. Davidson; Allan P. Donsig, Real Analysis and Applications: Theory in Practice — Supplementary Material](https://www.math.uwaterloo.ca/~krdavids/RAA/RAAsupp.pdf#page=65): Section 9.B, Extension Theorem 9.B.4, p. 63.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=63): Section 2.6, Lemma 2.14 and Corollary 2.15, pp. 52–53, including the explicit left-endpoint version.

Source relation (derived): Combines constant-speed Finsler dynamics with complete-space extension; this module concludes position confinement and recharting, before velocity continuation.
-/

/-!
# Recharting an actual Euler--Lagrange curve near a finite endpoint

An actual C2 slit Euler--Lagrange solution has constant original Finsler speed.
Completeness of the original length metric therefore supplies a finite position endpoint
and a compact terminal coordinate trace in the chart centered there. Smoothness and the
actual Euler--Lagrange equation pass to that fixed endpoint chart through the genuine
atlas transition. Every confinement and speed estimate is derived from the input solution.

The conclusion concerns the recharted interior solution. Convergence or continuation of
its velocity is not asserted here.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ E]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Actual energy conservation and completeness give a fixed endpoint chart with compact
position range, preserving smoothness, nonzero velocity and the true Euler--Lagrange equation. -/
theorem exists_terminal_rechart_eulerLagrange (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {x : ℝ → E} {a b : ℝ} (hab : a < b)
    (hx : ContDiffOn ℝ 2 x (Ioo a b))
    (hphase : ∀ t ∈ Ioo a b, (x t, deriv x t) ∈ chartEnergyDomain old)
    (hEL : ∀ t ∈ Ioo a b, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy old) (x s, deriv x s))
      (baseEnergyDifferential (F.chartEnergy old) (x t, deriv x t)) t) :
    ∃ cbar : ℝ → M, ContinuousOn cbar (Icc a b) ∧
      EqOn cbar ((extChartAt 𝓘(ℝ, E) old).symm ∘ x) (Ioo a b) ∧
      ∃ b₀ ∈ Ioo a b, ∃ K : Set E,
        let new := cbar b
        let η := chartTransition new old ∘ x
        IsCompact K ∧ K ⊆ (extChartAt 𝓘(ℝ, E) new).target ∧
        ContDiffOn ℝ ∞ η (Ioo b₀ b) ∧
        (∀ t ∈ Ioo b₀ b, (η t, deriv η t) ∈ chartEnergyDomain new) ∧
        (∀ t ∈ Ioo b₀ b, HasDerivAt
          (fun s ↦ fiberLegendre (F.chartEnergy new) (η s, deriv η s))
          (baseEnergyDifferential (F.chartEnergy new) (η t, deriv η t)) t) ∧
        MapsTo η (Ioo b₀ b) K ∧
        EqOn ((extChartAt 𝓘(ℝ, E) new).symm ∘ η)
          ((extChartAt 𝓘(ℝ, E) old).symm ∘ x) (Ioo b₀ b) := by
  let c := (extChartAt 𝓘(ℝ, E) old).symm ∘ x
  have hxSmooth := hF.contDiffOn_chartEulerLagrange_of_contDiffOn_two old
    isOpen_Ioo hx hphase hEL
  have hcSmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c (Ioo a b) :=
    (contMDiffOn_extChartAt_symm old).comp hxSmooth.contMDiffOn
      (fun t ht ↦ (hphase t ht).1)
  let t₀ := (a + b) / 2
  have ht₀ : t₀ ∈ Ioo a b := ⟨by dsimp [t₀]; linarith, by dsimp [t₀]; linarith⟩
  let C := F.chartLength old (x t₀, deriv x t₀)
  have hspeed : ∀ t ∈ Ioo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) ≤ C := by
    intro t ht
    have hxt := (hxSmooth.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
    have hvelocity := F.toFun_chartCurve_velocity old (hphase t ht).1 hxt.hasDerivAt
    change F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = _ at hvelocity
    rw [hvelocity]
    exact (hF.chartLength_eq_of_eulerLagrange old isOpen_Ioo isPreconnected_Ioo
      hx hphase hEL ht ht₀).le
  obtain ⟨cbar, hcbar, heq, b₀, hb₀, K, hK, hKsub, hsource, _, hKmap⟩ :=
    F.exists_endpoint_chart_compact_of_speed_le hcomplete hab
      (hcSmooth.of_le (by simp)) hspeed
  let new := cbar b
  let η := chartTransition new old ∘ x
  have hsmall : Ioo b₀ b ⊆ Ioo a b := Ioo_subset_Ioo hb₀.1.le le_rfl
  have hmap : MapsTo x (Ioo b₀ b) (chartTransitionDomain new old) := by
    intro t ht
    refine ⟨(hphase t (hsmall ht)).1, ?_⟩
    change c t ∈ (extChartAt 𝓘(ℝ, E) new).source
    rw [← heq (hsmall ht)]
    exact hsource ⟨ht.1.le, ht.2.le⟩
  have hη : ContDiffOn ℝ ∞ η (Ioo b₀ b) :=
    (contDiffOn_chartTransition new old).comp (hxSmooth.mono hsmall) hmap
  have hslit : ∀ t ∈ Ioo b₀ b,
      (x t, deriv x t) ∈ chartTransitionDomain new old ×ˢ {w : E | w ≠ 0} :=
    fun t ht ↦ ⟨hmap ht, (hphase t (hsmall ht)).2⟩
  have hηEL := (hF.chartEulerLagrange_iff_chartTransition new old isOpen_Ioo
    (hx.mono hsmall) hslit).mp (fun t ht ↦ hEL t (hsmall ht))
  refine ⟨cbar, hcbar, heq, b₀, hb₀, K, hK, hKsub, hη, ?_, hηEL, ?_, ?_⟩
  · intro t ht
    have hdx := ((hxSmooth.mono hsmall).contDiffAt
      (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
    have hdφ := ((contDiffOn_chartTransition new old).contDiffAt
      ((isOpen_chartTransitionDomain new old).mem_nhds (hmap ht))).differentiableAt
        (by simp)
    change (η t, deriv (chartTransition new old ∘ x) t) ∈ chartEnergyDomain new
    rw [(hdφ.hasFDerivAt.comp_hasDerivAt t hdx.hasDerivAt).deriv]
    exact mapsTo_chartTransition_energyDomain new old (hslit t ht)
  · intro t ht
    change η t ∈ K
    have hcoord : η t = extChartAt 𝓘(ℝ, E) new (cbar t) := by
      change extChartAt 𝓘(ℝ, E) new (c t) = _
      rw [heq (hsmall ht)]
    rw [hcoord]
    exact hKmap ⟨ht.1.le, ht.2.le⟩
  · intro t ht
    exact chart_symm_chartTransition new old (hmap ht)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
