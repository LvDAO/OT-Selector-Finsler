import OTSelector.Geometry.Finsler.CompletePotentialAdapted
import OTSelector.Geometry.Finsler.PotentialCompleteGauss
import OTSelector.Geometry.Finsler.CompleteAdaptedJacobi
import OTSelector.Geometry.FinslerCompleteAdaptedFocal

/-!
# Automatic adapted Jacobi charts of one complete potential-level family

The original general Finsler structure and a smooth potential matching one initial
momentum construct their own level and one complete family. At every time its actual
momentum chooses a clock; the same family has a genuine joint graph inverse and actual
reduced Jacobi equations. No preferred positive coordinate, product-model Finsler
structure, supplied level or phase-structure hypothesis is required.
-/

open Set Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}



/-- The same constructed complete family has actual focal expansions and finite singular
sets on compact subsets of each automatically selected graph time domain. No preferred
positive coordinate, supplied phase structure, basis or crossing condition is assumed. -/
theorem exists_complete_potentialLevelAdaptedFocalFamily [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {f : E → ℝ} {Ω : Set E} {y₀ v₀ : E}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (hy₀ : y₀ ∈ Ω)
    (hz : (y₀, v₀) ∈ chartEnergyDomain initial)
    (hmatch : fderiv ℝ f y₀ = fiberLegendre (F.chartEnergy initial) (y₀, v₀))
    (t₀ : ℝ) :
    let p := fderiv ℝ f y₀
    Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E ∧
    ∃ (B : Set p.ker) (σ : p.ker → E) (a : p.ker → ℝ) (Γ : p.ker → ℝ → M),
      IsOpen B ∧ (0 : p.ker) ∈ B ∧
      ContDiffOn ℝ ∞ σ B ∧ σ 0 = y₀ ∧ MapsTo σ B Ω ∧
      (∀ w ∈ B, f (σ w) = f y₀) ∧ HasFDerivAt σ p.ker.subtypeL 0 ∧
      ContDiffOn ℝ ∞ a B ∧ a 0 = 1 ∧ (∀ w ∈ B, 0 < a w) ∧
      (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ 0) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (y₀, v₀) ∧
      (∀ w ∈ B, F.chartMomentumFamily initial Γ (w, t₀) =
        potentialConormalState f σ a w) ∧
      ContMDiffOn 𝓘(ℝ, p.ker × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
      (∀ w ∈ B, ∀ t : ℝ,
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) =
          F.chartEnergy initial (y₀, v₀)) ∧
      (∀ (old : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        Function.Injective
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) 0)) ∧
      (∀ w ∈ B, ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        ∀ ξ η : p.ker, canonicalPhasePairing
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w ξ)
          (fderiv ℝ (fun b ↦ F.chartMomentumFamily old Γ (b, t)) w η) = 0) ∧
      (∀ w ∈ B, ∀ (old : M) (t : ℝ), Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        ∀ ξ : p.ker, (F.chartMomentumFamily old Γ (w, t)).2
          (fderiv ℝ (fun b ↦ extChartAt 𝓘(ℝ, E) old (Γ b t)) w ξ) = 0) ∧
      ∀ (old : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        let x := extChartAt 𝓘(ℝ, E) old ∘ Γ 0
        let pₜ := fiberLegendre (F.chartEnergy old) (x t, deriv x t)
        Module.finrank ℝ pₜ.ker + 1 = Module.finrank ℝ E ∧
          ∃ A : E ≃L[ℝ] (ℝ × pₜ.ker), A (deriv x t) = (1, 0) ∧
            F.HasAdaptedGraphFocalChart A Γ B 0 old t := by
  obtain ⟨hdim, B, σ, a, Γ, hB, h0, hσ, hσ0, hσΩ, hlevel, hD, ha, ha0, hapos,
    hEL, hi, hm, hG, henergy, hrank, hpair, hnormal, hcharts⟩ :=
    hF.exists_complete_potentialLevelAdaptedJacobiFamily
      hcomplete initial hΩ hf hy₀ hz hmatch t₀
  refine ⟨hdim, B, σ, a, Γ, hB, h0, hσ, hσ0, hσΩ, hlevel, hD, ha, ha0, hapos,
    hEL, hi, hm, hG, henergy, hrank, hpair, hnormal, ?_⟩
  intro old t hx
  obtain ⟨hdt, A, hAv, hJ⟩ := hcharts old t hx
  refine ⟨hdt, A, hAv, hF.hasAdaptedGraphFocalChart_of_finrank ?_ hJ⟩
  omega

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
