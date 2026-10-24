import OTSelector.Geometry.FinslerCompleteAdaptedFocalIsolation
import OTSelector.Geometry.Manifold.ManifoldFocalFinite
import OTSelector.Geometry.Manifold.TangentFamilyPosition
import OTSelector.Geometry.Finsler.PotentialCompleteGauss

/-!
# Finite intrinsic focal times of the same complete Finsler family

Local original-time isolation in varying legal charts gives finitely many intrinsic
position degeneracies on every compact time set. Actual smooth potential level data
construct the same complete family and all geometric hypotheses of this conclusion.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The same codimension-one complete normal family has finitely many intrinsic
position-degenerate times in any compact set of original times. Charts may vary. -/
theorem finite_noninjective_manifoldPosition_of_completeFamily [FiniteDimensional ℝ W]
    (hF : F.IsSmoothStronglyConvex)
    (hdim : Module.finrank ℝ W + 1 = Module.finrank ℝ E)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {C₀ : ℝ} (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = C₀)
    {w₀ : W} (hw : w₀ ∈ B)
    (hrank : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      Function.Injective (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀))
    (hpair : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      ∀ ξ η : W, canonicalPhasePairing
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ ξ)
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ η) = 0)
    (hnormal : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      ∀ ξ : W, (F.chartMomentumFamily old Γ (w₀, t)).2
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ ξ) = 0)
    {K : Set ℝ} (hK : IsCompact K) :
    {t ∈ K | ¬HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀}.Finite := by
  apply finite_noninjective_manifoldPosition_times
    (continuous_positionCurve_of_tangentFamily hB hG hw)
    (contMDiffAt_positionParameter_of_tangentFamily hB hG hw) hK
  intro t _
  have hx := mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ t)
  exact ⟨Γ w₀ t, hx, hF.eventually_injective_chartPosition_of_completeFamily
    hdim hB hEL hG henergy hw hrank hpair hnormal (Γ w₀ t) t hx⟩

/-- Original smooth potential data and one matching nonzero actual initial momentum
construct a complete level family with finite intrinsic focal times on every compact
time set. Rank, isotropy, Gauss normality and the seed dimension are all outputs. -/
theorem exists_complete_potentialLevelFamily_finite_focal [T2Space M] [PreconnectedSpace M]
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
      ∀ K : Set ℝ, IsCompact K →
        {t ∈ K | ¬HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) 0}.Finite := by
  obtain ⟨hdim, B, σ, a, Γ, hB, h0, hσ, hσ0, hσΩ, hlevel, hD, ha, ha0, hapos,
    hEL, hinit, hm, hG, henergy, hrank, hpair, hnormal⟩ :=
    hF.exists_complete_normalPotentialLevelFamily hcomplete initial hΩ hf hy₀ hz hmatch t₀
  refine ⟨hdim, B, σ, a, Γ, hB, h0, hσ, hσ0, hσΩ, hlevel, hD, ha, ha0, hapos,
    hEL, hinit, hm, hG, henergy, hrank, hpair, hnormal, ?_⟩
  intro K hK
  exact hF.finite_noninjective_manifoldPosition_of_completeFamily hdim hB hEL hG henergy
    h0 hrank (hpair 0 h0) (hnormal 0 h0) hK

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
