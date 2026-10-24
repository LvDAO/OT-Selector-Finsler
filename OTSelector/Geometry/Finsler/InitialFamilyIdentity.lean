import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.EndpointMinimizerStability
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LegendreInjectivity

/-!
# Geometry.Finsler.InitialFamilyIdentity

* **Conditions:** One supplied complete original family with actual initial tangent identity, one genuine inverse branch and a given complete curve with that actual chart momentum.
* **Objects:** Equality of the entire given curve with the corresponding member of the same supplied family.
* **Proof detail:** Use whole-slit Legendre injectivity to recover the actual initial tangent and then apply intrinsic complete-solution uniqueness.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): No replacement family or second inverse branch is selected.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerInitialFamilyIdentity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerInitialFamilyIdentity`; the selected original proof blocks follow. -/
section

/-!
# The same complete family represents the actual initial momentum

A given Legendre inverse identifies the actual chart tangent through injectivity
on the whole slit chart domain. The already supplied complete family then equals
the given entire Euler--Lagrange curve. No replacement family is constructed.
-/

open Set Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {F : ContinuousFinslerNorm E M}

/-- The prescribed complete family at the inverse of an actual initial energy
momentum equals the supplied complete curve, with both witnesses unchanged. -/
theorem eq_complete_family_of_chartMomentum (hF : F.IsSmoothStronglyConvex)
    (old : M) {t₀ : ℝ} {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old)
    {Γ : W → ℝ → M} {w : W}
    (hc : F.IsEulerLagrangeOn (Γ w) univ)
    (hsource : Γ w t₀ ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {q : E × (E →L[ℝ] ℝ)} (hq : q ∈ e.target)
    (hmomentum : F.chartMomentumFamily old Γ (w, t₀) = q) :
    Phi (e.symm q) = Γ w := by
  let z : E × E := (extChartAt 𝓘(ℝ, E) old (Γ w t₀),
    deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t₀)
  obtain ⟨hz, hcurve⟩ :=
    hF.eq_complete_family_of_isEulerLagrangeOn old hEL hinit hc hsource
  have hzq : parametricLegendre (F.chartEnergy old) z = q := hmomentum
  have hinv : e.symm q = z := by
    apply hF.injOn_parametricLegendre_chartEnergy old (hsub (e.map_target hq)) hz
    rw [hzq, ← he]
    exact e.right_inv hq
  rw [hinv]
  exact hcurve

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
