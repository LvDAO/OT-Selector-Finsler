import OTSelector.Analysis.Calculus.IntrinsicCostCoefficientNormalSeed
import OTSelector.Geometry.Finsler.PotentialCompleteGauss
import OTSelector.Geometry.Finsler.CompleteTangentSmooth

/-!
# Actual smooth normal families in the original labels

The prescribed complete flow transports the constructed potential level seed.
Its phase jet is the original one, and Gauss normality holds throughout its open
label domain, supplying the actual normal family needed for a calibrated tube.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {F : ContinuousFinslerNorm E M}

/-- A prescribed energy-tangent isotropic normal jet produces a genuinely normal
smooth family in the original label space, using the supplied complete flow. -/
theorem exists_prescribed_normalFamily_same_phaseJet
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : E × E → E × (E →L[ℝ] ℝ)) = parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {z₀ : E × (E →L[ℝ] ℝ)} (hz₀ : z₀ ∈ e.target)
    (henergy : localHamiltonian (F.chartEnergy old) e z₀ = (1 / 2 : ℝ))
    (R : W →L[ℝ] E) (Q : W →L[ℝ] E →L[ℝ] ℝ)
    (hzero : (fderiv ℝ (localHamiltonian (F.chartEnergy old) e) z₀).comp
      (R.prod Q) = 0)
    (hR : Function.Injective R) (hisotropic : ∀ ξ η : W, Q ξ (R η) = Q η (R ξ))
    (hnormal : ∀ ξ : W, z₀.2 (R ξ) = 0) (value : ℝ)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) :
    ∃ (H : E →L[ℝ] E →L[ℝ] ℝ) (B : Set W) (σ v : W → E) (a : W → ℝ),
      let Γ : W → ℝ → M := fun w ↦ Φ (σ w, v w)
      (∀ x y, H x y = H y x) ∧ H.comp R = Q ∧ IsOpen B ∧ 0 ∈ B ∧
      ContDiffOn ℝ ∞ σ B ∧ ContDiffOn ℝ ∞ v B ∧ ContDiffOn ℝ ∞ a B ∧
      σ 0 = z₀.1 ∧ HasFDerivAt σ R 0 ∧ a 0 = 1 ∧
      (∀ w ∈ B, secondJetPolynomial z₀.1 value z₀.2 H (σ w) = value) ∧
      (σ 0, v 0) = e.symm z₀ ∧ (∀ w ∈ B, (σ w, v w) ∈ chartEnergyDomain old) ∧
      (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
      (∀ w ∈ B, Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) old).source) ∧
      F.chartMomentumFamily old Γ (0, 0) = z₀ ∧
      HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, 0)) (R.prod Q) 0 ∧
      ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
      (∀ w ∈ B, ∀ t : ℝ,
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = (1 / 2 : ℝ)) ∧
      ∀ w ∈ B, ∀ (terminal : M) (t : ℝ),
        Γ w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source → ∀ ξ : W,
        (F.chartMomentumFamily terminal Γ (w, t)).2
          (fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (Γ z t)) w ξ) = 0 := by
  obtain ⟨H, B, σ, v, a, hsym, hcomp, hB, h0, hσ, hv, ha,
    hσ0, hσD, hv0, ha0, _, hlevel, hd, hjet⟩ :=
    hF.exists_normalPotentialSeed_same_phaseJet old he hsub hi hz₀ henergy
      R Q hzero hR hisotropic hnormal value
  let P := secondJetPolynomial z₀.1 value z₀.2 H
  let seed : W → E × E := fun w ↦ (σ w, v w)
  let Γ : W → ℝ → M := fun w ↦ Φ (seed w)
  have hseed : ContDiffOn ℝ ∞ seed B := hσ.prodMk hv
  have hlegal : ∀ w ∈ B, seed w ∈ chartEnergyDomain old := fun w hw ↦ hsub (hd w hw).1
  have hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ := fun w hw ↦ hEL _ (hlegal w hw)
  have hΓi (w : W) (hw : w ∈ B) :
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (seed w) := hinit _ (hlegal w hw)
  have hΓG := (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth old hB hΓ
    hseed (fun w hw ↦ hlegal w hw) hΓi).1
  have hsource (w : W) (hw : w ∈ B) :
      Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    have hb := congrArg (fun z : TangentBundle 𝓘(ℝ, E) M ↦ z.1) (hΓi w hw)
    rw [tangentChart_symm_eq old (hlegal w hw).1] at hb
    change Γ w 0 = (extChartAt 𝓘(ℝ, E) old).symm (seed w).1 at hb
    rw [hb]
    exact (extChartAt 𝓘(ℝ, E) old).map_target (hlegal w hw).1
  have hmomentum (w : W) (hw : w ∈ B) :
      F.chartMomentumFamily old Γ (w, 0) = potentialConormalState P σ a w :=
    (hF.chartMomentum_of_tangent_eq (hΓ w hw 0 (mem_univ _)) old (hlegal w hw)
      (hΓi w hw)).trans (Prod.ext rfl (hd w hw).2.2.2.1)
  have hnear : (fun w ↦ F.chartMomentumFamily old Γ (w, 0)) =ᶠ[𝓝 0]
      (fun w ↦ (σ w, a w • fderiv ℝ P (σ w))) := by
    filter_upwards [hB.mem_nhds h0] with w hw
    exact hmomentum w hw
  have hcentral : seed 0 = e.symm z₀ :=
    Prod.ext (hσ0.trans (parametricLegendre_inverse_components he hz₀).1.symm) hv0
  have hvalue : F.chartMomentumFamily old Γ (0, 0) = z₀ := by
    have hm : F.chartMomentumFamily old Γ (0, 0) =
        parametricLegendre (F.chartEnergy old) (seed 0) :=
      hF.chartMomentum_of_tangent_eq (hΓ 0 h0 0 (mem_univ _)) old (hlegal 0 h0)
        (hΓi 0 h0)
    rw [hcentral, ← he, e.right_inv hz₀] at hm
    exact hm
  have hΓenergy (w : W) (hw : w ∈ B) (t : ℝ) :
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = (1 / 2 : ℝ) := by
    calc
      _ = F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨0, (1 : ℝ)⟩) := by
        unfold ContinuousFinslerNorm.energy
        rw [hF.speed_eq_of_isEulerLagrangeOn (hΓ w hw) isPreconnected_univ
          (mem_univ t) (mem_univ 0)]
      _ = F.chartEnergy old (seed w) := congrArg F.energy (hΓi w hw)
      _ = 1 / 2 := (hd w hw).2.2.1
  refine ⟨H, B, σ, v, a, hsym, hcomp, hB, h0, hσ, hv, ha, hσ0, hσD, ha0,
    hlevel, hcentral, hlegal, hΓ, hsource, hvalue,
    hjet.congr_of_eventuallyEq hnear, hΓG, hΓenergy, ?_⟩
  intro w hw terminal t ht ξ
  apply hF.chartMomentumFamily_gauss_zero_of_potential_initial hB hΓ
    (hΓG.of_le (by simp)) hΓenergy old 0 hmomentum hw (hsource w hw)
    ((contDiff_secondJetPolynomial z₀.1 value z₀.2 H).differentiable (by simp) (σ w))
    ((hσ.contDiffAt (hB.mem_nhds hw)).differentiableAt (by simp))
    (c := value) _ terminal t ht ξ
  filter_upwards [hB.mem_nhds hw] with z hz
  exact hlevel z hz

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
