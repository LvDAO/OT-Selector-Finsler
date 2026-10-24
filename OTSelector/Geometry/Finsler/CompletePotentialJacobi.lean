import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.CompleteRegraphedJacobi
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialCompleteGauss
import OTSelector.Geometry.Symplectic.PotentialConormal

/-!
# Geometry.Finsler.CompletePotentialJacobi

* **Conditions:** A smooth potential whose actual central differential matches Finsler momentum in the complete geometry.
* **Objects:** Its own level chart and complete normal family with genuine graph Jacobi charts wherever the stated coordinate clock is positive.
* **Proof detail:** Construct the normalized level family and its initial phase rank/isotropy, then apply same-family graph reduction.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompletePotentialJacobi.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompletePotentialJacobi`; the selected original proof blocks follow. -/
section

/-!
# The same complete potential level family carries actual reduced Jacobi systems

Starting with a smooth potential whose differential matches the original momentum,
construct its own codimension-one level, the complete normal family, and genuine
reduced Jacobi charts of that family. Initial phase rank, canonical isotropy and Gauss
normality are proved by the construction, rather than supplied separately.
-/

open Set Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {V M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M] {F : ContinuousFinslerNorm (ℝ × V) M}

/-- One complete family realizes the original potential level and the actual Jacobi
systems in each legal positive-clock graph chart; no phase-structure oracle is an input. -/
theorem exists_complete_potentialLevelJacobiFamily [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {f : (ℝ × V) → ℝ} {Ω : Set (ℝ × V)} {y₀ v₀ : ℝ × V}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hy₀ : y₀ ∈ Ω)
    (hz : (y₀, v₀) ∈ chartEnergyDomain initial)
    (hmatch : fderiv ℝ f y₀ = fiberLegendre (F.chartEnergy initial) (y₀, v₀))
    (t₀ : ℝ) :
    let p := fderiv ℝ f y₀
    Module.finrank ℝ p.ker + 1 = Module.finrank ℝ (ℝ × V) ∧
    ∃ (B : Set p.ker) (σ : p.ker → ℝ × V) (a : p.ker → ℝ) (Γ : p.ker → ℝ → M),
      IsOpen B ∧ (0 : p.ker) ∈ B ∧
      ContDiffOn ℝ ∞ σ B ∧ σ 0 = y₀ ∧ MapsTo σ B Ω ∧
      (∀ w ∈ B, f (σ w) = f y₀) ∧ HasFDerivAt σ p.ker.subtypeL 0 ∧
      ContDiffOn ℝ ∞ a B ∧ a 0 = 1 ∧ (∀ w ∈ B, 0 < a w) ∧
      (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × V) (Γ 0) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, ℝ × V).prod 𝓘(ℝ, ℝ × V))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, ℝ × V) M)).symm (y₀, v₀) ∧
      (∀ w ∈ B, F.chartMomentumFamily initial Γ (w, t₀) =
        potentialConormalState f σ a w) ∧
      ContMDiffOn 𝓘(ℝ, p.ker × ℝ) (𝓘(ℝ, ℝ × V).prod 𝓘(ℝ, ℝ × V)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × V) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
      (∀ w ∈ B, ∀ t : ℝ,
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × V) (Γ w) ⟨t, (1 : ℝ)⟩) =
          F.chartEnergy initial (y₀, v₀)) ∧
      (∀ (old : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
        Function.Injective
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) 0)) ∧
      (∀ w ∈ B, ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
        ∀ ξ η : p.ker, canonicalPhasePairing
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w ξ)
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w η) = 0) ∧
      (∀ w ∈ B, ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
        ∀ ξ : p.ker, (F.chartMomentumFamily old Γ (w, t)).2
          (fderiv ℝ (fun b ↦ extChartAt 𝓘(ℝ, ℝ × V) old (Γ b t)) w ξ) = 0) ∧
      ∀ (old : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, ℝ × V) old).source →
        0 < (deriv (extChartAt 𝓘(ℝ, ℝ × V) old ∘ Γ 0) t).1 →
        F.HasGraphJacobiChart Γ B 0 old t := by
  obtain ⟨hdim, B, σ, a, Γ, hB, h0, hσ, hσ0, hσΩ, hlevel, hD, ha, ha0, hapos,
    hEL, hi, hm, hG, henergy, hrank, hpair, hnormal⟩ :=
    hF.exists_complete_normalPotentialLevelFamily hcomplete initial hΩ hf hy₀ hz hmatch t₀
  refine ⟨hdim, B, σ, a, Γ, hB, h0, hσ, hσ0, hσΩ, hlevel, hD, ha, ha0, hapos,
    hEL, hi, hm, hG, henergy, hrank, hpair, hnormal, ?_⟩
  intro old t hx hpositive
  exact hF.exists_completeFamily_chartGraphStructure hB hEL hG henergy h0
    hrank (hpair 0 h0) (hnormal 0 h0) old t hx hpositive

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
