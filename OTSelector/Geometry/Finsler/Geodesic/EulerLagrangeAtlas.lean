import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerEulerLagrangeAtlas.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerEulerLagrangeAtlas`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.EulerLagrangeAtlas

* **Conditions:** A continuous curve through an open neighborhood for the topological helper; smooth strongly convex Finsler energy and a prescribed nonzero tangent for the geometric theorem.
* **Objects:** A smaller symmetric time interval and a genuine constant-speed Euler–Lagrange curve valid in each chart through the initial point.
* **Proof detail:** Shrink by continuity, construct the local Hamiltonian curve, and transfer the actual Euler–Lagrange identity through smooth chart transitions.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49): Section 2.2, Theorem 2.2 (Picard–Lindelöf) and Lemma 2.3 (regularity), p. 38.

Source relation (derived): The local spray existence principle is classical; the quantified per-chart neighborhood and actual tangent-bundle covariance are proved as intrinsic adapters.
-/

/-!
# Local Finsler Euler--Lagrange curves in every chart at the initial point

A genuine local curve constructed from the smooth strongly convex Finsler energy
satisfies the actual Euler--Lagrange equation in every chart containing its initial
point, after shrinking the time interval for that chart. Continuity supplies the
actual overlap condition; neither chart membership nor coordinate covariance is
assumed. The prescribed genuine initial velocity, smoothness and constant Finsler
speed of the constructed curve are retained.
-/

open Set Filter Bundle
open scoped Manifold Topology ContDiff

namespace OTSelector.Geometry

/-- A continuous curve remains in an open neighborhood on a smaller symmetric interval. -/
theorem exists_pos_le_mapsTo_Ioo_of_continuousAt
    {X : Type*} [TopologicalSpace X]
    {x : ℝ → X} {t₀ ε : ℝ} {U : Set X}
    (hc : ContinuousAt x t₀) (hU : IsOpen U) (hx : x t₀ ∈ U) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
      MapsTo x (Ioo (t₀ - δ) (t₀ + δ)) U ∧
      Ioo (t₀ - δ) (t₀ + δ) ⊆ Ioo (t₀ - ε) (t₀ + ε) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hc.preimage_mem_nhds (hU.mem_nhds hx))
  refine ⟨min r ε, lt_min hr hε, min_le_right _ _, ?_, ?_⟩
  · intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq]
    have hdist : |t - t₀| < min r ε := by
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    exact lt_of_lt_of_le hdist (min_le_left _ _)
  · intro t ht
    have hle : min r ε ≤ ε := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- A prescribed nonzero tangent vector initiates a genuine smooth constant-speed
curve satisfying the original Euler--Lagrange equation in every chart containing
its initial point. The positive time radius may depend on the chosen chart. -/
theorem exists_localEulerLagrange_all_charts [FiniteDimensional ℝ E]
    {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {v : E} (hv : v ≠ 0) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ c : ℝ → M,
      c t₀ = x₀ ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩ =
        (⟨x₀, tangentFiberModelEquiv x₀ v⟩ : TangentBundle 𝓘(ℝ, E) M) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c (Ioo (t₀ - ε) (t₀ + ε)) ∧
      (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) =
          F.toFun ⟨x₀, tangentFiberModelEquiv x₀ v⟩) ∧
      (∃ x : ℝ → E, c = (extChartAt 𝓘(ℝ, E) x₀).symm ∘ x ∧
        ContDiffOn ℝ ∞ x (Ioo (t₀ - ε) (t₀ + ε)) ∧
        ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
          (x t, deriv x t) ∈ ContinuousFinslerNorm.chartEnergyDomain x₀ ∧
          HasDerivAt (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
            (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t) ∧
      ∀ old : M, x₀ ∈ (extChartAt 𝓘(ℝ, E) old).source →
        ∃ δ > (0 : ℝ), δ ≤ ε ∧
          ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ, E) old ∘ c)
            (Ioo (t₀ - δ) (t₀ + δ)) ∧
          ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
            ((extChartAt 𝓘(ℝ, E) old ∘ c) t,
              deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) ∈
                ContinuousFinslerNorm.chartEnergyDomain old ∧
            HasDerivAt
              (fun s ↦ fiberLegendre (F.chartEnergy old)
                ((extChartAt 𝓘(ℝ, E) old ∘ c) s,
                  deriv (extChartAt 𝓘(ℝ, E) old ∘ c) s))
              (baseEnergyDifferential (F.chartEnergy old)
                ((extChartAt 𝓘(ℝ, E) old ∘ c) t,
                  deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t)) t := by
  obtain ⟨ε, hε, c, hc₀, hv₀, hc, hspeed, x, hcx, hx, hEL⟩ :=
    hF.exists_localEulerLagrange x₀ hv t₀
  refine ⟨ε, hε, c, hc₀, hv₀, hc, hspeed, ⟨x, hcx, hx, hEL⟩, ?_⟩
  intro old hold
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have hx₀ : x t₀ ∈ chartTransitionDomain old x₀ := by
    refine ⟨(hEL t₀ ht₀).1.1, ?_⟩
    have hpoint : (extChartAt 𝓘(ℝ, E) x₀).symm (x t₀) = x₀ :=
      (congrFun hcx t₀).symm.trans hc₀
    change (extChartAt 𝓘(ℝ, E) x₀).symm (x t₀) ∈ (extChartAt 𝓘(ℝ, E) old).source
    rwa [hpoint]
  have hxcont := (hx.contDiffAt (isOpen_Ioo.mem_nhds ht₀)).continuousAt
  obtain ⟨δ, hδ, hδε, hmap, hsub⟩ := exists_pos_le_mapsTo_Ioo_of_continuousAt hxcont
    (isOpen_chartTransitionDomain old x₀) hx₀ hε
  have hphase : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
      (x t, deriv x t) ∈ chartTransitionDomain old x₀ ×ˢ {w : E | w ≠ 0} :=
    fun t ht ↦ ⟨hmap ht, (hEL t (hsub ht)).1.2⟩
  have heq : extChartAt 𝓘(ℝ, E) old ∘ c = chartTransition old x₀ ∘ x := by
    rw [hcx]
    rfl
  have hxsmall := hx.mono hsub
  have htransition := (contDiffOn_chartTransition old x₀).comp hxsmall hmap
  have hcov := (hF.chartEulerLagrange_iff_chartTransition old x₀ isOpen_Ioo
    (hxsmall.of_le (by simp)) hphase).mp (fun t ht ↦ (hEL t (hsub ht)).2)
  refine ⟨δ, hδ, hδε, heq.symm ▸ htransition, ?_⟩
  intro t ht
  rw [heq]
  refine ⟨?_, hcov t ht⟩
  have hdx := (hxsmall.contDiffAt (isOpen_Ioo.mem_nhds ht)).differentiableAt (by simp)
  have hdφ := ((contDiffOn_chartTransition old x₀).contDiffAt
    ((isOpen_chartTransitionDomain old x₀).mem_nhds (hmap ht))).differentiableAt (by simp)
  rw [(hdφ.hasFDerivAt.comp_hasDerivAt t hdx.hasDerivAt).deriv]
  exact mapsTo_chartTransition_energyDomain old x₀ (hphase t ht)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
