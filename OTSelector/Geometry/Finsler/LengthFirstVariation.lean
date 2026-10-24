import OTSelector.Analysis.Calculus.VariationDerivatives
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthAction
import OTSelector.Geometry.Finsler.LengthEulerLagrange
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.Variation.Lagrangian
import OTSelector.Geometry.Manifold.TangentChartCurve

/-!
# Geometry.Finsler.LengthFirstVariation

* **Conditions:** A C2 chart variation with nonzero central velocity; actual energy Euler–Lagrange on an open connected interval for the endpoint-only formula.
* **Objects:** The derivative of original path length as endpoint momenta plus the true length Euler–Lagrange residual.
* **Proof detail:** Identify the original action, differentiate under its compact slit bound, integrate by parts and remove the residual using derived constant-speed length dynamics.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): Concerns the specified path family; no identification with a global distance branch is asserted.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLengthFirstVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLengthFirstVariation`; the selected original proof blocks follow. -/
section

/-!
# First variation of the original Finsler path length

The action is the original manifold path length, with exactly the given Finsler norm.
A C2 chart variation whose central velocity is nonzero has a first length derivative
consisting of actual endpoint pairings and the length Euler--Lagrange residual.
The energy Euler--Lagrange equation on an open connected time domain removes that
residual, with no prescribed unit speed or length equation.

Endpoint fields are derivatives of the same reconstructed manifold variation. These
formulas concern path length; they make no identification with a distance branch.
-/

open Set Filter MeasureTheory Manifold Bundle
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual parameter tangent of the reconstructed manifold variation is the inverse
of its tangent chart applied to the ordinary variation field. -/
theorem tangentMap_chartVariation_parameter (x₀ : M)
    {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hσ : ContDiffOn ℝ 1 σ D) {s₀ t : ℝ} (hz : (s₀, t) ∈ D)
    (hbase : σ (s₀, t) ∈ (extChartAt 𝓘(ℝ, E) x₀).target) :
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ (fun s ↦ σ (s, t))) ⟨s₀, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨x₀, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
          (σ (s₀, t), variationField σ s₀ t) := by
  have hd := (hσ.contDiffAt (hD.mem_nhds hz)).differentiableAt one_ne_zero
  have hs : HasDerivAt (fun s ↦ σ (s, t)) (variationField σ s₀ t) s₀ :=
    (hd.comp s₀ (differentiableAt_id.prodMk (differentiableAt_const t))).hasDerivAt
  exact tangentMap_chart_symm_curve x₀ hbase hs

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- First variation of the original manifold path length, with the actual endpoint
fields and the length Euler--Lagrange residual. Only the central trace must be slit. -/
theorem hasDerivAt_pathELength_firstVariation (x₀ : M)
    {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    (htrace : ∀ t ∈ Icc a b, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ Icc a b,
      variationPhase σ (s₀, t) ∈ chartEnergyDomain x₀) :
    letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
    HasDerivAt
      (fun s ↦ (Manifold.pathELength 𝓘(ℝ, E)
        ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ (fun t ↦ σ (s, t))) a b).toReal)
      (fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ))
          (variationPhase σ (s₀, b)) (variationField σ s₀ b) -
        fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ))
          (variationPhase σ (s₀, a)) (variationField σ s₀ a) +
        ∫ t in a..b,
          (baseEnergyDifferential (fun z ↦ (F.chartLength x₀ z : ℝ))
              (variationPhase σ (s₀, t)) -
            deriv (fun u ↦ fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ))
              (variationPhase σ (s₀, u))) t) (variationField σ s₀ t)) s₀ := by
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  have h := hasDerivAt_lagrangianAction_firstVariation (isOpen_chartEnergyDomain x₀)
    ((hF.contDiffOn_chartLength x₀).of_le (by simp)) hD hσ hab htrace hphase
  exact h.congr_of_eventuallyEq
    (F.pathELength_chartVariation_eventuallyEq x₀ hD (hσ.of_le (by norm_num)) hab
      htrace (fun t ht ↦ (hphase t ht).1))

/-- Along an actual slit energy Euler--Lagrange curve, the derivative of original
path length consists of its two actual endpoint pairings. Constancy of the original
speed and the length equation follow from energy dynamics on the connected time domain. -/
theorem hasDerivAt_pathELength_endpoint_of_chartEnergy (x₀ : M)
    {σ : ℝ × ℝ → E} {D : Set (ℝ × ℝ)} (hD : IsOpen D)
    (hσ : ContDiffOn ℝ 2 σ D) {s₀ a b : ℝ} (hab : a ≤ b)
    {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I) (hsegment : Icc a b ⊆ I)
    (htrace : ∀ t ∈ I, (s₀, t) ∈ D)
    (hphase : ∀ t ∈ I, variationPhase σ (s₀, t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ t ∈ I, HasDerivAt
      (fun u ↦ fiberLegendre (F.chartEnergy x₀) (variationPhase σ (s₀, u)))
      (baseEnergyDifferential (F.chartEnergy x₀) (variationPhase σ (s₀, t))) t) :
    letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
    HasDerivAt
      (fun s ↦ (Manifold.pathELength 𝓘(ℝ, E)
        ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ (fun t ↦ σ (s, t))) a b).toReal)
      (fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ))
          (variationPhase σ (s₀, b)) (variationField σ s₀ b) -
        fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ))
          (variationPhase σ (s₀, a)) (variationField σ s₀ a)) s₀ := by
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  have hx : ContDiffOn ℝ 2 (fun t ↦ σ (s₀, t)) I :=
    hσ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht ↦ htrace t ht)
  have hlengthEL := hF.chartLength_eulerLagrange_of_chartEnergy x₀ hI hconn hx hphase hEL
  have hzero : (∫ t in a..b,
      (baseEnergyDifferential (fun z ↦ (F.chartLength x₀ z : ℝ))
          (variationPhase σ (s₀, t)) -
        deriv (fun u ↦ fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ))
          (variationPhase σ (s₀, u))) t) (variationField σ s₀ t)) = 0 := by
    calc
      _ = ∫ _ in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        dsimp only [variationPhase, variationVelocity]
        rw [(hlengthEL t (hsegment ((uIcc_of_le hab) ▸ ht))).deriv]
        simp
      _ = 0 := by simp
  apply (hF.hasDerivAt_pathELength_firstVariation x₀ hD hσ hab
    (fun t ht ↦ htrace t (hsegment ht)) (fun t ht ↦ hphase t (hsegment ht))).congr_deriv
  rw [hzero, add_zero]

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
