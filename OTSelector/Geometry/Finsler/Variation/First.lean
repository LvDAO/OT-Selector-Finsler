import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Calculus.VariationDerivatives
import OTSelector.Analysis.CompactParameterIntegral
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Variation.Lagrangian
import OTSelector.Geometry.Manifold.TangentChartCurve

/-!
## Lemma skeleton

* **Conditions:** A C2 variation with compact time trace inside one nonzero smooth energy chart; fixed endpoints only for the zero derivative corollaries.
* **Objects:** Derivative of the manifold quadratic energy action, boundary momentum term and interior Euler–Lagrange residual.
* **Proof detail:** Identify the action with the chart action, differentiate under the compact integral, integrate the covector term by parts, and cancel the residual/endpoints when assumed.

## Mathematical sources

* D. Bao; S.-S. Chern; Z. Shen, *An Introduction to Riemann-Finsler Geometry (Springer 2000)*, Section 5.1, pp. 111–118, first variation of arc length.
  https://link.springer.com/chapter/10.1007/978-1-4612-1268-3_5
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 8.3, pp. 238–240, equations (8.33)–(8.36) (action and Euler–Lagrange), (8.39)–(8.43) (Legendre transform and Hamilton equations), (8.47) (energy conservation).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters).
  https://www.jirka.org/ra/html/sec_diffunderint.html
* D. H. Fremlin, *Measure Theory, Volume 2*, Section 225E (absolutely continuous functions as indefinite integrals), 225F (integration by parts).
  https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29

**Relationship to the sources:** The directly checked variational formula is Teschl’s general action calculation. BCS is a section-level Finsler arc-length pointer; this energy-action statement has an explicit interior residual and is not quoted as the identical BCS theorem.
-/

/-!
# First variation of the genuine Finsler energy action

The action integrates the original energy of the actual tangent velocity of a manifold
curve. For variations reconstructed through a chart, its local identification with the
coordinate Lagrangian action follows from the actual tangent-map identity. A common
admissible parameter neighborhood is derived from the compact central trace. The general
first-variation formula then gives the endpoint momentum pairing and the Euler--Lagrange
residual for this original action. Actual fixed endpoint slices imply stationary action
when the reference curve satisfies the genuine coordinate Euler--Lagrange equation.

A C2 variation is supplied. The conclusion is stationarity, without a minimization claim.
-/

open Set Filter Bundle MeasureTheory
open scoped Manifold Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

namespace ContinuousFinslerNorm

/-- Integrate the original Finsler energy of the genuine tangent velocity of a curve. -/
def curveEnergyAction (F : ContinuousFinslerNorm E M) (c : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩)

set_option backward.isDefEq.respectTransparency false in
/-- The actual energy action of a curve reconstructed in a chart equals its coordinate action. -/
theorem curveEnergyAction_chart_eq (F : ContinuousFinslerNorm E M) (x₀ : M)
    {x : ℝ → E} {a b : ℝ}
    (hbase : ∀ t ∈ uIcc a b, x t ∈ (extChartAt 𝓘(ℝ, E) x₀).target)
    (hx : ∀ t ∈ uIcc a b, DifferentiableAt ℝ x t) :
    F.curveEnergyAction ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ x) a b =
      ∫ t in a..b, F.chartEnergy x₀ (x t, deriv x t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact congrArg F.energy
    (tangentMap_chart_symm_curve x₀ (hbase t ht) (hx t ht).hasDerivAt)

/-- The actual action and the coordinate energy integral agree near the central parameter.
Only central base-chart membership is supplied; a common nearby strip is derived. -/
theorem curveEnergyAction_chartVariation_eventuallyEq
    (F : ContinuousFinslerNorm E M) (x₀ : M)
    {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hσ : ContDiffOn ℝ 1 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hbase : ∀ t ∈ Icc a b, σ (s₀, t) ∈ (extChartAt 𝓘(ℝ, E) x₀).target) :
    (fun s ↦ F.curveEnergyAction
      ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ (fun t ↦ σ (s, t))) a b) =ᶠ[𝓝 s₀]
      (fun s ↦ ∫ t in a..b,
        F.chartEnergy x₀ (σ (s, t), deriv (fun u ↦ σ (s, u)) t)) := by
  let O := D ∩ σ ⁻¹' (extChartAt 𝓘(ℝ, E) x₀).target
  have hO : IsOpen O := hσ.continuousOn.isOpen_inter_preimage hD
    (isOpen_extChartAt_target x₀)
  obtain ⟨r, hr, hstrip⟩ := exists_pos_compact_parameter_strip hO
    (fun t ht ↦ ⟨htrace t ht, hbase t ht⟩)
  have hS : Icc (s₀ - r) (s₀ + r) ∈ 𝓝 s₀ :=
    Icc_mem_nhds (by linarith) (by linarith)
  filter_upwards [hS] with s hs
  apply F.curveEnergyAction_chart_eq x₀
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact (hstrip (show (s, t) ∈ Icc (s₀ - r) (s₀ + r) ×ˢ Icc a b from ⟨hs, ht⟩)).2
  · intro t ht
    rw [uIcc_of_le hab] at ht
    have hz : (s, t) ∈ D := (hstrip ⟨hs, ht⟩).1
    exact ((hσ.contDiffAt (hD.mem_nhds hz)).differentiableAt_one).comp t
      ((differentiableAt_const (c := s)).prodMk (differentiableAt_id (𝕜 := ℝ)))

/-- A compact central trace in the slit chart domain identifies the genuine action
with the actual coordinate Lagrangian action on a parameter neighborhood. -/
theorem curveEnergyAction_lagrangianAction_eventuallyEq
    (F : ContinuousFinslerNorm E M) (x₀ : M)
    {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ Icc a b,
      variationPhase σ (s₀, t) ∈ chartEnergyDomain x₀) :
    (fun s ↦ F.curveEnergyAction
      ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ (fun t ↦ σ (s, t))) a b) =ᶠ[𝓝 s₀]
      lagrangianAction (F.chartEnergy x₀) σ a b := by
  exact F.curveEnergyAction_chartVariation_eventuallyEq x₀ hD
    (hσ.of_le (by norm_num)) hab htrace (fun t ht ↦ (hphase t ht).1)

namespace IsSmoothStronglyConvex

/-- First variation of the original Finsler energy of actual manifold velocities.
The coordinate action identification and a common admissible parameter neighborhood
are derived from the genuine chart and the compact central trace. -/
theorem hasDerivAt_curveEnergyAction_firstVariation
    {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ Icc a b,
      variationPhase σ (s₀, t) ∈ chartEnergyDomain x₀) :
    HasDerivAt
      (fun s ↦ F.curveEnergyAction
        ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ (fun t ↦ σ (s, t))) a b)
      (fiberLegendre (F.chartEnergy x₀) (variationPhase σ (s₀, b))
          (variationField σ s₀ b) -
        fiberLegendre (F.chartEnergy x₀) (variationPhase σ (s₀, a))
          (variationField σ s₀ a) +
        ∫ t in a..b,
          (baseEnergyDifferential (F.chartEnergy x₀) (variationPhase σ (s₀, t)) -
            deriv (fun u ↦ fiberLegendre (F.chartEnergy x₀) (variationPhase σ (s₀, u))) t)
              (variationField σ s₀ t)) s₀ := by
  have h := hasDerivAt_lagrangianAction_firstVariation (isOpen_chartEnergyDomain x₀)
    ((hF.contDiffOn_chartEnergy x₀).of_le (by simp)) hD hσ hab htrace hphase
  exact h.congr_of_eventuallyEq
    (F.curveEnergyAction_lagrangianAction_eventuallyEq x₀ hD hσ hab htrace hphase)

/-- Fixed-endpoint variations of a genuine Finsler Euler--Lagrange curve have
stationary original energy action. Endpoint variation fields vanish by differentiation
of the actual constant endpoint slices, rather than by an extra field assumption. -/
theorem hasDerivAt_curveEnergyAction_zero_of_eulerLagrange
    {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ Icc a b,
      variationPhase σ (s₀, t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ t ∈ Icc a b, HasDerivAt
      (fun u ↦ fiberLegendre (F.chartEnergy x₀) (variationPhase σ (s₀, u)))
      (baseEnergyDifferential (F.chartEnergy x₀) (variationPhase σ (s₀, t))) t)
    (hfixed_a : (fun s ↦ σ (s, a)) =ᶠ[𝓝 s₀] (fun _ ↦ σ (s₀, a)))
    (hfixed_b : (fun s ↦ σ (s, b)) =ᶠ[𝓝 s₀] (fun _ ↦ σ (s₀, b))) :
    HasDerivAt
      (fun s ↦ F.curveEnergyAction
        ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ (fun t ↦ σ (s, t))) a b) 0 s₀ := by
  have h := hasDerivAt_lagrangianAction_zero_of_eulerLagrange (isOpen_chartEnergyDomain x₀)
    ((hF.contDiffOn_chartEnergy x₀).of_le (by simp)) hD hσ hab htrace hphase hEL
    hfixed_a hfixed_b
  exact h.congr_of_eventuallyEq
    (F.curveEnergyAction_lagrangianAction_eventuallyEq x₀ hD hσ hab htrace hphase)

/-- Keeping the reconstructed manifold endpoints fixed also gives stationary action.
Local chart membership converts these actual endpoint equalities to coordinate equalities. -/
theorem hasDerivAt_curveEnergyAction_zero_of_fixed_manifold_endpoints
    {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex) (x₀ : M)
    {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ Icc a b,
      variationPhase σ (s₀, t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ t ∈ Icc a b, HasDerivAt
      (fun u ↦ fiberLegendre (F.chartEnergy x₀) (variationPhase σ (s₀, u)))
      (baseEnergyDifferential (F.chartEnergy x₀) (variationPhase σ (s₀, t))) t)
    (hfixed_a : (fun s ↦ (extChartAt 𝓘(ℝ, E) x₀).symm (σ (s, a))) =ᶠ[𝓝 s₀]
      (fun _ ↦ (extChartAt 𝓘(ℝ, E) x₀).symm (σ (s₀, a))))
    (hfixed_b : (fun s ↦ (extChartAt 𝓘(ℝ, E) x₀).symm (σ (s, b))) =ᶠ[𝓝 s₀]
      (fun _ ↦ (extChartAt 𝓘(ℝ, E) x₀).symm (σ (s₀, b)))) :
    HasDerivAt
      (fun s ↦ F.curveEnergyAction
        ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ (fun t ↦ σ (s, t))) a b) 0 s₀ := by
  have hfixed (t : ℝ) (ht : t ∈ Icc a b)
      (hm : (fun s ↦ (extChartAt 𝓘(ℝ, E) x₀).symm (σ (s, t))) =ᶠ[𝓝 s₀]
        (fun _ ↦ (extChartAt 𝓘(ℝ, E) x₀).symm (σ (s₀, t)))) :
      (fun s ↦ σ (s, t)) =ᶠ[𝓝 s₀] (fun _ ↦ σ (s₀, t)) := by
    have hi : ContinuousAt (fun s : ℝ ↦ (s, t)) s₀ :=
      continuousAt_id.prodMk continuousAt_const
    have hc : ContinuousAt (fun s ↦ σ (s, t)) s₀ :=
      (hσ.contDiffAt (hD.mem_nhds (htrace t ht))).continuousAt.comp
        (f := fun s : ℝ ↦ (s, t)) hi
    have hbase : σ (s₀, t) ∈ (extChartAt 𝓘(ℝ, E) x₀).target := (hphase t ht).1
    have hn := hc.preimage_mem_nhds ((isOpen_extChartAt_target x₀).mem_nhds hbase)
    filter_upwards [hm, hn] with s hs hsbase
    have heq := congrArg (extChartAt 𝓘(ℝ, E) x₀) hs
    simpa only [(extChartAt 𝓘(ℝ, E) x₀).right_inv hsbase,
      (extChartAt 𝓘(ℝ, E) x₀).right_inv hbase] using heq
  exact hF.hasDerivAt_curveEnergyAction_zero_of_eulerLagrange x₀ hD hσ hab htrace hphase hEL
    (hfixed a ⟨le_rfl, hab⟩ hfixed_a) (hfixed b ⟨hab, le_rfl⟩ hfixed_b)

end IsSmoothStronglyConvex

end ContinuousFinslerNorm
end OTSelector.Geometry
