import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompleteHamiltonianFamily.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompleteHamiltonianFamily`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CompleteHamiltonianFamily

* **Conditions:** A jointly C2 actual intrinsic tangent family and a legal chart; the complete family is constructed from the complete Finsler metric.
* **Objects:** Actual chart momentum coordinates, their joint C2 regularity and the original Hamiltonian equation on every legal inverse branch.
* **Proof detail:** Read position/velocity through the tangent chart, compose with the original Legendre map and use its injectivity to identify inverse branch velocity.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Actual Hamiltonian coordinates of complete Finsler families

Read the actual position and time derivative of an intrinsic family in any legal chart,
then apply the original fiber Legendre map. Joint C2 regularity of the total tangent
gives joint C2 regularity of this actual momentum family. Its original Hamiltonian ODE
follows from intrinsic Euler--Lagrange, with inverse-branch compatibility derived by
nonlinear Legendre injectivity. Completeness constructs the input family on all times.
-/

open Set Filter Function Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

namespace ContinuousFinslerNorm

/-- The chart position and actual energy momentum of an intrinsic parameter family. -/
def chartMomentumFamily (F : ContinuousFinslerNorm E M) (old : M)
    (Γ : W → ℝ → M) (q : W × ℝ) : E × (E →L[ℝ] ℝ) :=
  eulerLagrangePhaseLift (F.chartEnergy old) (extChartAt 𝓘(ℝ, E) old ∘ Γ q.1) q.2

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

/-- The actual chart momentum family is jointly C2 wherever the intrinsic tangent
family is jointly C2 and its positions lie in that chart. -/
theorem contDiffOn_chartMomentumFamily (hF : F.IsSmoothStronglyConvex) (old : M)
    {Γ : W → ℝ → M} {D : Set (W × ℝ)}
    (hEL : ∀ q ∈ D, F.IsEulerLagrangeAt (Γ q.1) q.2)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) D)
    (hmap : ∀ q ∈ D, Γ q.1 q.2 ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    ContDiffOn ℝ 2 (F.chartMomentumFamily old Γ) D := by
  have hphase := hF.contDiffOn_chartPhase_of_tangentFamily_C2 old hEL hG hmap
  have hL : ContDiffOn ℝ 2 (parametricLegendre (F.chartEnergy old))
      (chartEnergyDomain old) := by
    intro z hz
    exact ((contDiffAt_parametricLegendre ((hF.contDiffOn_chartEnergy old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds hz))).of_le (by simp)).contDiffWithinAt
  apply hL.comp hphase
  intro q hq
  obtain ⟨I, _, ht, _, _, hm, _⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt (hEL q hq) old (hmap q hq)
  exact hm q.2 ht

/-- Intrinsic Euler--Lagrange yields the original Hamiltonian equation for the actual
momentum curve in every admissible inverse target. The inverse velocity is identified. -/
theorem hasDerivAt_chartMomentum (hF : F.IsSmoothStronglyConvex) (old : M)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old)
    (hp : eulerLagrangePhaseLift (F.chartEnergy old)
      (extChartAt 𝓘(ℝ, E) old ∘ c) t ∈ e.target) :
    HasDerivAt (eulerLagrangePhaseLift (F.chartEnergy old) (extChartAt 𝓘(ℝ, E) old ∘ c))
      (localHamiltonianVectorField (F.chartEnergy old) e
        (eulerLagrangePhaseLift (F.chartEnergy old) (extChartAt 𝓘(ℝ, E) old ∘ c) t)) t := by
  obtain ⟨I, hI, ht, _, hy, hphase, hEL⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt hc old hx
  let z := ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t)
  have hi : e.symm (parametricLegendre (F.chartEnergy old) z) = z := by
    apply hF.injOn_parametricLegendre_chartEnergy old (hsub (e.map_target hp)) (hphase t ht)
    have hright := e.right_inv hp
    rw [he] at hright
    exact hright
  have hs : z ∈ e.source := hi ▸ e.map_target hp
  exact hasDerivAt_eulerLagrangePhaseLift he
    ((hy.contDiffAt (hI.mem_nhds ht)).differentiableAt (by simp)) hs (hEL t ht)

/-- Complete original Finsler geometry constructs one family with jointly C2 actual
momenta and genuine Hamiltonian dynamics in every admissible coordinate neighborhood. -/
theorem exists_complete_chartMomentumFamily_C2 [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (t₀ : ℝ) :
    ∃ Γ : (E × E) → ℝ → M,
      (∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ) ∧
      (∀ z ∈ chartEnergyDomain initial,
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨t₀, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) ∧
      ∀ (old : M) (D : Set ((E × E) × ℝ)), D ⊆ chartEnergyDomain initial ×ˢ univ →
        (∀ q ∈ D, Γ q.1 q.2 ∈ (extChartAt 𝓘(ℝ, E) old).source) →
        ContDiffOn ℝ 2 (F.chartMomentumFamily old Γ) D ∧
        ∀ (e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))),
          (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old) →
          e.source ⊆ chartEnergyDomain old → ∀ q ∈ D,
          F.chartMomentumFamily old Γ q ∈ e.target →
          HasDerivAt (fun s ↦ F.chartMomentumFamily old Γ (q.1, s))
            (localHamiltonianVectorField (F.chartEnergy old) e
              (F.chartMomentumFamily old Γ q)) q.2 := by
  obtain ⟨Γ, hEL, hi, hG⟩ := hF.exists_complete_tangentFamily_C2 hcomplete initial t₀
  refine ⟨Γ, hEL, hi, ?_⟩
  intro old D hD hm
  have hELD (q : (E × E) × ℝ) (hq : q ∈ D) : F.IsEulerLagrangeAt (Γ q.1) q.2 :=
    hEL q.1 (hD hq).1 q.2 (mem_univ _)
  refine ⟨hF.contDiffOn_chartMomentumFamily old hELD (hG.mono hD) hm, ?_⟩
  intro e he hs q hq hp
  exact hF.hasDerivAt_chartMomentum old (hELD q hq) (hm q hq) he hs hp

end IsSmoothStronglyConvex
end ContinuousFinslerNorm
end OTSelector.Geometry

end
end
