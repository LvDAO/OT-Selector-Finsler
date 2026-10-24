import OTSelector.Analysis.Calculus.Variational.EulerLagrangeReparam
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthEulerLagrange
import OTSelector.Geometry.Finsler.LengthHomogeneity
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerLengthReparam.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerLengthReparam`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.LengthReparam

* **Conditions:** An actual energy Euler–Lagrange curve and a differentiable positive change of time taking values in its open solution interval.
* **Objects:** The original length Euler–Lagrange equation after actual time reparameterization.
* **Proof detail:** First derive the length equation from constant energy, then use degree-zero length momentum and degree-one base differential with the chain rule.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Actual Finsler length equations under positive changes of time

An original energy Euler--Lagrange curve has constant positive speed and satisfies
the true length equation. The actual length homogeneity identities then preserve
this equation under any positive differentiable change of time. No length equation
or homogeneity of independently prescribed differential data is assumed.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}
  (hF : F.IsSmoothStronglyConvex)
include hF

/-- Original energy equations imply actual length equations after a positive local time change. -/
theorem chartLength_eulerLagrange_reparam (x₀ : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hx : ContDiffOn ℝ 2 x I)
    (hphase : ∀ s ∈ I, (x s, deriv x s) ∈ ContinuousFinslerNorm.chartEnergyDomain x₀)
    (hEL : ∀ s ∈ I, HasDerivAt
      (fun r ↦ fiberLegendre (F.chartEnergy x₀) (x r, deriv x r))
      (baseEnergyDifferential (F.chartEnergy x₀) (x s, deriv x s)) s)
    {τ : ℝ → ℝ} {t : ℝ}
    (hτ : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ τ s ∧ 0 < deriv τ s ∧ τ s ∈ I) :
    HasDerivAt
      (fun s ↦ fiberLegendre (fun z ↦ (F.chartLength x₀ z : ℝ))
        ((x ∘ τ) s, deriv (x ∘ τ) s))
      (baseEnergyDifferential (fun z ↦ (F.chartLength x₀ z : ℝ))
        ((x ∘ τ) t, deriv (x ∘ τ) t)) t := by
  have ht := hτ.self_of_nhds
  apply hasDerivAt_eulerLagrange_reparam
    (O := ContinuousFinslerNorm.chartEnergyDomain x₀)
    (fun z hz a ha ↦ hF.chartLength_fiberLegendre_pos_smul x₀ hz ha)
    (fun z hz a ha ↦ hF.chartLength_baseDifferential_pos_smul x₀ hz ha) _
    (hF.chartLength_eulerLagrange_of_chartEnergy x₀ hI hconn hx hphase hEL (τ t) ht.2.2)
  filter_upwards [hτ] with s hs
  exact ⟨(hx.contDiffAt (hI.mem_nhds hs.2.2)).differentiableAt (by norm_num),
    hs.1, hs.2.1, hphase _ hs.2.2⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
