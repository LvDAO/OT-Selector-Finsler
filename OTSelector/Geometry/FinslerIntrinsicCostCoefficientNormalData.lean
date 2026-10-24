import OTSelector.Geometry.FinslerIntrinsicCostCoefficientNormalFamily

/-!
# Retained smooth normal potential family data

The complete family retains its original flow and labels, the actual polynomial
potential level section, and its true initial phase derivative. These are produced
geometric data used by the original distance expansion.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A genuine potential-level family in the supplied labels, with its complete
flow, exact initial phase jet, and normality throughout its open label domain. -/
structure NormalPotentialFamily (F : ContinuousFinslerNorm E M) (initial : M)
    (z₀ : E × (E →L[ℝ] ℝ)) (R : W →L[ℝ] E) (Q : W →L[ℝ] E →L[ℝ] ℝ)
    (value : ℝ) where
  hessian : E →L[ℝ] E →L[ℝ] ℝ
  hessian_symm : ∀ x y, hessian x y = hessian y x
  hessian_comp : hessian.comp R = Q
  labels : Set W
  open_labels : IsOpen labels
  anchor_mem : 0 ∈ labels
  position : W → E
  velocity : W → E
  scale : W → ℝ
  position_smooth : ContDiffOn ℝ ∞ position labels
  velocity_smooth : ContDiffOn ℝ ∞ velocity labels
  scale_smooth : ContDiffOn ℝ ∞ scale labels
  position_center : position 0 = z₀.1
  position_jet : HasFDerivAt position R 0
  scale_center : scale 0 = 1
  level : ∀ w ∈ labels, secondJetPolynomial z₀.1 value z₀.2 hessian (position w) = value
  flow : (E × E) → ℝ → M
  flow_complete : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (flow z) univ
  flow_initial : ∀ z ∈ chartEnergyDomain initial,
    tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (flow z) ⟨0, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z
  initial_legal : ∀ w ∈ labels, (position w, velocity w) ∈ chartEnergyDomain initial
  curve : W → ℝ → M
  curve_eq : curve = fun w ↦ flow (position w, velocity w)
  complete : ∀ w ∈ labels, F.IsEulerLagrangeOn (curve w) univ
  initial_source : ∀ w ∈ labels, curve w 0 ∈ (extChartAt 𝓘(ℝ, E) initial).source
  initial_phase : F.chartMomentumFamily initial curve (0, 0) = z₀
  initial_jet : HasFDerivAt (fun w ↦ F.chartMomentumFamily initial curve (w, 0)) (R.prod Q) 0
  tangent_smooth : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
    (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (curve q.1) ⟨q.2, (1 : ℝ)⟩) (labels ×ˢ univ)
  energy_eq : ∀ w ∈ labels, ∀ t : ℝ,
    F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (curve w) ⟨t, (1 : ℝ)⟩) = 1 / 2
  normal : ∀ w ∈ labels, ∀ (terminal : M) (t : ℝ),
    curve w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source → ∀ ξ : W,
      (F.chartMomentumFamily terminal curve (w, t)).2
        (fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (curve z t)) w ξ) = 0

namespace IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Actual isotropic normal energy-tangent data construct the retained smooth
potential family, including its complete flow and all-label normality. -/
theorem nonempty_normalPotentialFamily (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : E × E → E × (E →L[ℝ] ℝ)) = parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {z₀ : E × (E →L[ℝ] ℝ)} (hz₀ : z₀ ∈ e.target)
    (henergy : localHamiltonian (F.chartEnergy old) e z₀ = (1 / 2 : ℝ))
    (R : W →L[ℝ] E) (Q : W →L[ℝ] E →L[ℝ] ℝ)
    (hzero : (fderiv ℝ (localHamiltonian (F.chartEnergy old) e) z₀).comp (R.prod Q) = 0)
    (hR : Function.Injective R) (hisotropic : ∀ ξ η : W, Q ξ (R η) = Q η (R ξ))
    (hnormal : ∀ ξ : W, z₀.2 (R ξ) = 0) (value : ℝ) :
    Nonempty (F.NormalPotentialFamily old z₀ R Q value) := by
  obtain ⟨Φ, hEL, hinit, _⟩ := hF.exists_complete_tangentFamily_C2 hcomplete old 0
  obtain ⟨H, B, σ, v, a, hsym, hcomp, hB, h0, hσ, hv, ha, hσ0, hσD, ha0,
    hlevel, _, hlegal, hΓ, hsource, hvalue, hjet, hG, hE, hn⟩ :=
    hF.exists_prescribed_normalFamily_same_phaseJet old he hsub hi hz₀ henergy
      R Q hzero hR hisotropic hnormal value hEL hinit
  exact ⟨{
    hessian := H, hessian_symm := hsym, hessian_comp := hcomp
    labels := B, open_labels := hB, anchor_mem := h0
    position := σ, velocity := v, scale := a
    position_smooth := hσ, velocity_smooth := hv, scale_smooth := ha
    position_center := hσ0, position_jet := hσD, scale_center := ha0, level := hlevel
    flow := Φ, flow_complete := hEL, flow_initial := hinit, initial_legal := hlegal
    curve := fun w ↦ Φ (σ w, v w), curve_eq := rfl, complete := hΓ
    initial_source := hsource, initial_phase := hvalue, initial_jet := hjet
    tangent_smooth := hG, energy_eq := hE, normal := hn }⟩

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
