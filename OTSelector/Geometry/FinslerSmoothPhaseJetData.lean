import OTSelector.Geometry.FinslerSmoothPhaseJetComparison
import OTSelector.Analysis.Calculus.FlowJetMatching

/-!
# Complete smooth comparison data at the original label

The comparison retains the original label space and anchor. Its actual central initial
phase and first derivative agree with the prescribed data, and its common energy and
central phase structure hold for all real times. Initial positions stay in the supplied
chart on the constructed open label neighborhood.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Actual complete comparison geometry carrying one prescribed position-covector jet. -/
structure SmoothPhaseJetComparison (F : ContinuousFinslerNorm E M)
    (initial : M) (t₀ : ℝ) (w₀ : W) (z₀ : E × (E →L[ℝ] ℝ))
    (R : W →L[ℝ] E) (Q : W →L[ℝ] E →L[ℝ] ℝ) where
  labels : Set W
  open_labels : IsOpen labels
  anchor_mem : w₀ ∈ labels
  curve : W → ℝ → M
  complete : ∀ w ∈ labels, F.IsEulerLagrangeOn (curve w) univ
  initial_source : ∀ w ∈ labels, curve w t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source
  initial_phase : F.chartMomentumFamily initial curve (w₀, t₀) = z₀
  initial_jet : HasFDerivAt (fun w ↦ F.chartMomentumFamily initial curve (w, t₀))
    (R.prod Q) w₀
  tangent_C2 : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
    (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (curve q.1) ⟨q.2, (1 : ℝ)⟩) (labels ×ˢ univ)
  energy_eq : ∀ w ∈ labels, ∀ t : ℝ,
    F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (curve w) ⟨t, (1 : ℝ)⟩) = (1 / 2 : ℝ)
  phase_rank : ∀ (old : M) (t : ℝ), curve w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
    Function.Injective (fderiv ℝ (fun w ↦ F.chartMomentumFamily old curve (w, t)) w₀)
  phase_isotropic : ∀ (old : M) (t : ℝ), curve w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
    ∀ ξ η : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ F.chartMomentumFamily old curve (w, t)) w₀ ξ)
      (fderiv ℝ (fun w ↦ F.chartMomentumFamily old curve (w, t)) w₀ η) = 0
  normal : ∀ (old : M) (t : ℝ), curve w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
    ∀ ξ : W, (F.chartMomentumFamily old curve (w₀, t)).2
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (curve w t)) w₀ ξ) = 0

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The original geometry constructs smooth comparison data at any original label anchor. -/
theorem nonempty_smoothPhaseJetComparison (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (t₀ : ℝ) (w₀ : W)
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
    Nonempty (F.SmoothPhaseJetComparison initial t₀ w₀ z₀ R Q) := by
  obtain ⟨B, Γ, hB, h0, hEL, htangent, hphase, hjet, hG, henergy, hstructure⟩ :=
    hF.exists_completeFamily_same_phaseJet hcomplete initial t₀ he hsub hi hz₀ henergy
      R Q hzero hR hisotropic hnormal
  have hlegal := hsub (e.map_target hz₀)
  have hposition : Γ 0 t₀ = (extChartAt 𝓘(ℝ, E) initial).symm (e.symm z₀).1 := by
    have h := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) htangent
    rw [show e.symm z₀ = ((e.symm z₀).1, (e.symm z₀).2) from rfl,
      tangentChart_symm_eq initial hlegal.1] at h
    exact h
  have hsource0 : Γ 0 t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    rw [hposition]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target hlegal.1
  let U := B ∩ (fun w ↦ Γ w t₀) ⁻¹' (extChartAt 𝓘(ℝ, E) initial).source
  have hc : ContinuousOn (fun w ↦ Γ w t₀) B := fun w hw ↦
    (contMDiffAt_positionParameter_of_tangentFamily hB hG hw t₀).continuousAt.continuousWithinAt
  have hU : IsOpen U := hc.isOpen_inter_preimage hB (isOpen_extChartAt_source initial)
  let τ : W → W := fun w ↦ w - w₀
  let B' := τ ⁻¹' U
  let Γ' : W → ℝ → M := fun w ↦ Γ (τ w)
  have hτ : ContDiff ℝ ∞ τ := contDiff_id.sub contDiff_const
  have hτD : HasFDerivAt τ (ContinuousLinearMap.id ℝ W) w₀ :=
    (hasFDerivAt_id w₀).sub_const w₀
  have hτ0 : τ w₀ = 0 := sub_self w₀
  have hB' : IsOpen B' := hU.preimage hτ.continuous
  have hanchor : w₀ ∈ B' := by change τ w₀ ∈ U; exact hτ0 ▸ ⟨h0, hsource0⟩
  have hΓG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ' q.1) ⟨q.2, (1 : ℝ)⟩)
      (B' ×ˢ univ) := by
    have hmap : ContDiff ℝ 2 (fun q : W × ℝ ↦ (τ q.1, q.2)) :=
      ((hτ.of_le (by simp)).comp contDiff_fst).prodMk contDiff_snd
    exact hG.comp hmap.contMDiff.contMDiffOn (fun q hq ↦ ⟨hq.1.1, mem_univ _⟩)
  have hphaseD (old : M) (t : ℝ)
      (hx : Γ' w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
      fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ' (w, t)) w₀ =
        fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) 0 := by
    have hx' : Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source := by simpa only [Γ', hτ0] using hx
    have hC2 := hF.contDiffAt_chartMomentumFamily_of_tangentFamily hB hEL hG h0 old t hx'
    have hd : DifferentiableAt ℝ (fun w : W ↦ F.chartMomentumFamily old Γ (w, t)) 0 := by
      apply DifferentiableAt.comp (0 : W) (g := F.chartMomentumFamily old Γ)
      · exact hC2.differentiableAt (by norm_num)
      · exact differentiableAt_id.prodMk (differentiableAt_const t)
    have hdτ : HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, t))
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) 0) (τ w₀) := by
      rw [hτ0]
      exact hd.hasFDerivAt
    have h := hdτ.comp w₀ hτD
    simpa only [ContinuousLinearMap.comp_id] using! h.fderiv
  refine ⟨{
    labels := B', open_labels := hB', anchor_mem := hanchor, curve := Γ'
    complete := fun w hw ↦ hEL _ hw.1
    initial_source := fun w hw ↦ hw.2
    initial_phase := by
      change F.chartMomentumFamily initial Γ (τ w₀, t₀) = z₀
      rw [hτ0]
      exact hphase
    initial_jet := ?_
    tangent_C2 := hΓG
    energy_eq := fun w hw t ↦ henergy _ hw.1 t
    phase_rank := ?_, phase_isotropic := ?_, normal := ?_ }⟩
  · have hjetτ : HasFDerivAt (fun w ↦ F.chartMomentumFamily initial Γ (w, t₀))
        (R.prod Q) (τ w₀) := by rw [hτ0]; exact hjet
    simpa only [ContinuousLinearMap.comp_id] using! hjetτ.comp w₀ hτD
  · intro old t hx
    rw [hphaseD old t hx]
    exact (hstructure old t (by simpa only [Γ', hτ0] using hx)).1
  · intro old t hx ξ η
    rw [hphaseD old t hx]
    exact (hstructure old t (by simpa only [Γ', hτ0] using hx)).2.1 ξ η
  · intro old t hx ξ
    have hx' : Γ 0 t ∈ (extChartAt 𝓘(ℝ, E) old).source := by simpa only [Γ', hτ0] using hx
    have hp := congrArg (fun L : W →L[ℝ] E × (E →L[ℝ] ℝ) ↦
      (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp L) (hphaseD old t hx)
    have hC2 := hF.contDiffAt_chartMomentumFamily_of_tangentFamily hB hEL hG h0 old t hx'
    have hd := hC2.differentiableAt (by norm_num)
    have hC2' := hF.contDiffAt_chartMomentumFamily_of_tangentFamily hB'
      (fun w hw ↦ hEL _ hw.1) hΓG hanchor old t hx
    have hd' := hC2'.differentiableAt (by norm_num)
    have hs : DifferentiableAt ℝ (fun w : W ↦ F.chartMomentumFamily old Γ (w, t)) 0 := by
      apply DifferentiableAt.comp (0 : W) (g := F.chartMomentumFamily old Γ)
      · exact hd
      · exact differentiableAt_id.prodMk (differentiableAt_const t)
    have hs' : DifferentiableAt ℝ (fun w : W ↦ F.chartMomentumFamily old Γ' (w, t)) w₀ := by
      apply DifferentiableAt.comp w₀ (g := F.chartMomentumFamily old Γ')
      · exact hd'
      · exact differentiableAt_id.prodMk (differentiableAt_const t)
    rw [← hs.hasFDerivAt.fst.fderiv, ← hs'.hasFDerivAt.fst.fderiv] at hp
    change fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ' w t)) w₀ =
      fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) 0 at hp
    rw [hp]
    change (F.chartMomentumFamily old Γ (τ w₀, t)).2
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) 0 ξ) = 0
    rw [hτ0]
    exact (hstructure old t hx').2.2 ξ

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
