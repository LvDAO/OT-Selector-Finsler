import OTSelector.Geometry.FinslerStationaryPhaseAction
import OTSelector.Geometry.Manifold.TangentFamilyPosition

/-!
# Stationary phase action from a genuine tube

The retained initial-state family inherits the actual tube-distance jet through
its C2 endpoint maps. Its central whole-curve identity transports both length
covectors, so the existing phase action theorem gives the stationary action.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- A genuine tube jet yields a stationary action for the retained initial-phase
family. All endpoint regularity and chain-rule calculations are derived internally. -/
theorem stationary_phaseLengthAction_of_manifoldTube
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Phi : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Phi z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hC2 : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ)
      (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Phi q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain old) {P : E → ℝ}
    (hP : ContDiffAt ℝ 2 P z₀.1)
    (hmatch : fderiv ℝ P z₀.1 =
      fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) z₀)
    {Y : OpenPartialHomeomorph (ℝ × W) M} {Γ : W → ℝ → M}
    (hY : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞ Y.symm Y.target)
    (heq : (Y : ℝ × W → M) = fun q ↦ Γ q.2 q.1)
    {a b : ℝ} {w : W}
    (ha : (a, w) ∈ Y.source) (hb : (b, w) ∈ Y.source)
    (hsame : Phi z₀ = Γ w)
    (hdC : ContDiffAt ℝ 2 (F.tubeCoordinateDistance Y) ((a, w), (b, w)))
    (hd : let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Γ w t) →L[ℝ] ℝ := fun t ↦
        fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Γ w t) ↦
          (F.toFun ⟨Γ w t, v⟩ : ℝ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) t 1)
      HasFDerivAt (F.tubeCoordinateDistance Y)
        ((p b).comp (mfderiv 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
          (fun q ↦ Y q.2) ((a, w), (b, w))) -
          (p a).comp (mfderiv 𝓘(ℝ, (ℝ × W) × (ℝ × W)) 𝓘(ℝ, E)
            (fun q ↦ Y q.1) ((a, w), (b, w)))) ((a, w), (b, w))) :
    ContDiffAt ℝ 2 (F.phaseLengthAction old Phi P a b) (z₀, z₀) ∧
      HasFDerivAt (F.phaseLengthAction old Phi P a b)
        (0 : ((E × E) × (E × E)) →L[ℝ] ℝ) (z₀, z₀)
 := by
  have hpos := contMDiffOn_positionFamily_of_tangentFamily hC2
  have hposAt (t : ℝ) :
      ContMDiffAt 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) 2
        (fun q ↦ Phi q.1 q.2) (z₀, t) :=
    hpos.contMDiffAt (((isOpen_chartEnergyDomain old).prod isOpen_univ).mem_nhds
      (show (z₀, t) ∈ chartEnergyDomain old ×ˢ univ from ⟨hz₀, mem_univ _⟩))
  have hleft : ContMDiffAt 𝓘(ℝ, (E × E) × (E × E)) 𝓘(ℝ, E) 2
      (fun z ↦ Phi z.1 a) (z₀, z₀) :=
    (hposAt a).comp (z₀, z₀)
      ((contDiffAt_fst.prodMk contDiffAt_const).contMDiffAt)
  have hright : ContMDiffAt 𝓘(ℝ, (E × E) × (E × E)) 𝓘(ℝ, E) 2
      (fun z ↦ Phi z.2 b) (z₀, z₀) :=
    (hposAt b).comp (z₀, z₀)
      ((contDiffAt_snd.prodMk contDiffAt_const).contMDiffAt)
  have hfa : Phi z₀ a = Y (a, w) := by
    rw [heq]
    exact congrFun hsame a
  have hgb : Phi z₀ b = Y (b, w) := by
    rw [heq]
    exact congrFun hsame b
  let p : (t : ℝ) → TangentSpace 𝓘(ℝ, E) (Γ w t) →L[ℝ] ℝ := fun t ↦
    fderiv ℝ (fun v : TangentSpace 𝓘(ℝ, E) (Γ w t) ↦
      (F.toFun ⟨Γ w t, v⟩ : ℝ)) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) t 1)
  have hdist := F.distance_comp_jet_of_manifoldTube hY hi ha hb (p a) (p b)
    hdC hd hleft hright hfa hgb
  dsimp only [p] at hdist
  rw [← hsame] at hdist
  exact hF.stationary_phaseLengthAction old hEL hinit hC2 hz₀ hP hmatch a b
    hdist.1 hdist.2

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
