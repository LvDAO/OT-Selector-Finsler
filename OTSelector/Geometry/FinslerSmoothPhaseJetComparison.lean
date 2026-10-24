import OTSelector.Geometry.Finsler.CompleteMomentumRank
import OTSelector.Geometry.FinslerAffinePhaseJetSeed
import OTSelector.Geometry.Finsler.CompleteGauss
import OTSelector.Geometry.Finsler.CompleteAdaptedJacobi

/-!
# A complete smooth comparison family with the prescribed actual phase jet

Normalize an affine phase seed and run the complete original Finsler flow. Its initial
phase value and derivative are the prescribed ones. Initial immersion, isotropy and
normality propagate along that same family through every legal chart. The resulting
family therefore supplies actual adapted graph Jacobi coordinates.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- A normal isotropic phase jet tangent to energy one half constructs a complete family
with that exact jet, jointly C² total tangent, and its conserved central phase structure. -/
theorem exists_completeFamily_same_phaseJet
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (t₀ : ℝ)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : E × E → E × (E →L[ℝ] ℝ)) = parametricLegendre (F.chartEnergy initial))
    (hsub : e.source ⊆ chartEnergyDomain initial) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {z₀ : E × (E →L[ℝ] ℝ)} (hz₀ : z₀ ∈ e.target)
    (henergy : localHamiltonian (F.chartEnergy initial) e z₀ = (1 / 2 : ℝ))
    (R : W →L[ℝ] E) (Q : W →L[ℝ] E →L[ℝ] ℝ)
    (hzero : (fderiv ℝ (localHamiltonian (F.chartEnergy initial) e) z₀).comp
      (R.prod Q) = 0)
    (hR : Function.Injective R) (hisotropic : ∀ ξ η : W, Q ξ (R η) = Q η (R ξ))
    (hnormal : ∀ ξ : W, z₀.2 (R ξ) = 0) :
    ∃ (B : Set W) (Γ : W → ℝ → M),
      IsOpen B ∧ 0 ∈ B ∧
      (∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) ∧
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ 0) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (e.symm z₀) ∧
      F.chartMomentumFamily initial Γ (0, t₀) = z₀ ∧
      HasFDerivAt (fun w ↦ F.chartMomentumFamily initial Γ (w, t₀)) (R.prod Q) 0 ∧
      ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
        (B ×ˢ univ) ∧
      (∀ w ∈ B, ∀ t : ℝ,
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = (1 / 2 : ℝ)) ∧
      ∀ (old : M) (t : ℝ), Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        Function.Injective (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) 0) ∧
        (∀ ξ η : W, canonicalPhasePairing
          (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) 0 ξ)
          (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) 0 η) = 0) ∧
        ∀ ξ : W, (F.chartMomentumFamily old Γ (0, t)).2
          (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) 0 ξ) = 0 := by
  obtain ⟨B, v, a, hB, h0, hv, ha, hv0, ha0, haZero, hd, hjet⟩ :=
    hF.exists_affinePhase_constantEnergy_same_firstJet initial he hsub hi hz₀ henergy R Q hzero
  let σ : W → E := fun w ↦ z₀.1 + R w
  let q : W → E →L[ℝ] ℝ := fun w ↦ z₀.2 + Q w
  let seed : W → E × E := fun w ↦ (σ w, v w)
  let phase : W → E × (E →L[ℝ] ℝ) := fun w ↦ (σ w, a w • q w)
  change HasFDerivAt phase (R.prod Q) 0 at hjet
  have hσ : ContDiff ℝ ∞ σ := contDiff_const.add R.contDiff
  have hσD : HasFDerivAt σ R 0 := R.hasFDerivAt.const_add z₀.1
  have hs : ContDiffOn ℝ ∞ seed B := hσ.contDiffOn.prodMk hv
  have hm : MapsTo seed B (chartEnergyDomain initial) := fun w hw ↦ hsub (hd w hw).1
  have hseed0 : seed 0 = e.symm z₀ := by
    apply Prod.ext
    · simpa [seed, σ] using (parametricLegendre_inverse_components he hz₀).1.symm
    · exact hv0
  have hphase0 : phase 0 = z₀ := by simp [phase, σ, q, ha0]
  have hleg (w : W) (hw : w ∈ B) :
      parametricLegendre (F.chartEnergy initial) (seed w) = phase w :=
    Prod.ext rfl (hd w hw).2.2.2.1
  have hlegNear : (parametricLegendre (F.chartEnergy initial) ∘ seed) =ᶠ[𝓝 0] phase := by
    filter_upwards [hB.mem_nhds h0] with w hw
    exact hleg w hw
  have hlegJet := hjet.congr_of_eventuallyEq hlegNear
  obtain ⟨Φ, hEL, hinit, hG⟩ := hF.exists_complete_tangentFamily_C2 hcomplete initial t₀
  let Γ : W → ℝ → M := fun w ↦ Φ (seed w)
  have hΓ (w : W) (hw : w ∈ B) : F.IsEulerLagrangeOn (Γ w) univ := hEL _ (hm hw)
  have hΓi (w : W) (hw : w ∈ B) :
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (seed w) := hinit _ (hm hw)
  have hS : ContDiffOn ℝ 2 (fun q : W × ℝ ↦ (seed q.1, q.2)) (B ×ˢ univ) :=
    ((hs.of_le (by simp)).comp contDiffOn_fst (fun q hq ↦ hq.1)).prodMk contDiffOn_snd
  have hΓG := hG.comp hS.contMDiffOn (fun q hq ↦ ⟨hm hq.1, mem_univ _⟩)
  have hmomentum (w : W) (hw : w ∈ B) :
      F.chartMomentumFamily initial Γ (w, t₀) = phase w := by
    exact (hF.chartMomentum_of_tangent_eq (hΓ w hw t₀ (mem_univ _)) initial
      (hm hw) (hΓi w hw)).trans (hleg w hw)
  have hmomentumNear : (fun w ↦ F.chartMomentumFamily initial Γ (w, t₀)) =ᶠ[𝓝 0] phase := by
    filter_upwards [hB.mem_nhds h0] with w hw
    exact hmomentum w hw
  have hΓE (w : W) (hw : w ∈ B) (t : ℝ) :
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = (1 / 2 : ℝ) := by
    calc
      _ = F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩) := by
        unfold ContinuousFinslerNorm.energy
        rw [hF.speed_eq_of_isEulerLagrangeOn (hΓ w hw) isPreconnected_univ
          (mem_univ t) (mem_univ t₀)]
      _ = F.chartEnergy initial (seed w) := congrArg F.energy (hΓi w hw)
      _ = (1 / 2 : ℝ) := (hd w hw).2.2.1
  refine ⟨B, Γ, hB, h0, hΓ, ?_, (hmomentum 0 h0).trans hphase0,
    hjet.congr_of_eventuallyEq hmomentumNear, hΓG, hΓE, ?_⟩
  · simpa only [hseed0] using hΓi 0 h0
  · intro old t hx
    refine ⟨?_, ?_, ?_⟩
    · have hvD := (hv.contDiffAt (hB.mem_nhds h0)).differentiableAt (by simp)
      have hseedD : HasFDerivAt seed (R.prod (fderiv ℝ v 0)) 0 := hσD.prodMk hvD.hasFDerivAt
      have hinj : Function.Injective (fderiv ℝ seed 0) := by
        rw [hseedD.fderiv]
        intro ξ η hξη
        exact hR (congrArg Prod.fst hξη)
      exact hF.injective_fderiv_seeded_complete_chartMomentumFamily
        hcomplete initial t₀ hEL hinit hG hseedD.differentiableAt hinj (hm h0) old t hx
    · intro ξ η
      rw [hF.chartMomentumFamily_parameter_pairing_eq_initial
        hB hΓ hΓG initial t₀ hm hΓi h0 old t hx ξ η, hlegJet.fderiv]
      simp only [ContinuousLinearMap.prod_apply, canonicalPhasePairing,
        hisotropic ξ η, sub_self]
    · intro ξ
      rw [hF.chartMomentumFamily_gauss_eq_initial hB hΓ hΓG hΓE initial t₀ hm hΓi h0 old t hx ξ]
      have hp : fiberLegendre (F.chartEnergy initial) (seed 0) = z₀.2 := by
        simpa only [hphase0] using! congrArg Prod.snd (hleg 0 h0)
      change fiberLegendre (F.chartEnergy initial) (seed 0) (fderiv ℝ σ 0 ξ) = 0
      rw [hp, hσD.fderiv]
      exact hnormal ξ

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
