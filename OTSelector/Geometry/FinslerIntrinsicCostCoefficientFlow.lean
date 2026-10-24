import OTSelector.Geometry.FinslerIntrinsicCostCoefficient
import OTSelector.Geometry.Finsler.CompleteTangentSmooth

/-!
# Intrinsic distance coefficients preserved by actual flow jets

Equal initial tangent jets in the same prescribed complete flow give equal intrinsic
label Hessians at every original time. Joint manifold differentiability comes from
the actual flow and the differentiable seeds; it is not supplied for the families.
-/

open Set Filter Matrix Module Manifold Bundle
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E V W M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (F : ContinuousFinslerNorm E M)

/-- The intrinsic matrix depends only on the actual seed value and its first jet
under a differentiable manifold flow. -/
theorem familyLabelHessianMatrix_eq_of_seed_firstJet (bW : Basis ι ℝ W)
    {Φ : V × ℝ → M} {X Y : W → V} {w₀ : W} {t : ℝ}
    {D : W →L[ℝ] V} (hX : HasFDerivAt X D w₀) (hY : HasFDerivAt Y D w₀)
    (hvalue : X w₀ = Y w₀)
    (hΦ : MDifferentiableAt 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) Φ (X w₀, t)) :
    F.familyLabelHessianMatrix bW (fun q ↦ Φ (X q.1, q.2)) (w₀, t) =
      F.familyLabelHessianMatrix bW (fun q ↦ Φ (Y q.1, q.2)) (w₀, t) := by
  let J := (D.comp (ContinuousLinearMap.fst ℝ W ℝ)).prod
    (ContinuousLinearMap.snd ℝ W ℝ)
  have hDX : HasFDerivAt (fun q : W × ℝ ↦ (X q.1, q.2)) J (w₀, t) :=
    (hX.comp (w₀, t) hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have hDY : HasFDerivAt (fun q : W × ℝ ↦ (Y q.1, q.2)) J (w₀, t) :=
    (hY.comp (w₀, t) hasFDerivAt_fst).prodMk hasFDerivAt_snd
  have hΦY : MDifferentiableAt 𝓘(ℝ, V × ℝ) 𝓘(ℝ, E) Φ (Y w₀, t) := by
    rwa [← hvalue]
  have hx := mfderiv_comp (w₀, t) hΦ hDX.differentiableAt.mdifferentiableAt
  have hy := mfderiv_comp (w₀, t) hΦY hDY.differentiableAt.mdifferentiableAt
  rw [mfderiv_eq_fderiv, hDX.fderiv] at hx
  rw [mfderiv_eq_fderiv, hDY.fderiv] at hy
  dsimp only [Function.comp_def, Prod.fst, Prod.snd] at hx hy
  simp only [familyLabelHessianMatrix, hx, hy]
  rw [hvalue]

namespace IsSmoothStronglyConvex

variable {F} [FiniteDimensional ℝ E] [T2Space M]

/-- The prescribed original complete flow itself has smooth joint position. -/
theorem contMDiffOn_prescribed_complete_position (hF : F.IsSmoothStronglyConvex)
    (old : M) {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) :
    ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) 𝓘(ℝ, E) ∞
      (fun q ↦ Φ q.1 q.2) (chartEnergyDomain old ×ˢ univ) :=
  (hF.contMDiffOn_tangentFamily_of_chartSeed_smooth old
    (isOpen_chartEnergyDomain old) hEL contDiffOn_id (fun _ hz ↦ hz) hinit).2

/-- Initial tangent first jets identify the intrinsic matrices of the same actual
complete flow for every time, without a joint differentiability assumption. -/
theorem familyLabelHessianMatrix_complete_seed_eq (hF : F.IsSmoothStronglyConvex)
    (old : M) (bW : Basis ι ℝ W) {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {X Y : W → E × E} {w₀ : W} {D : W →L[ℝ] E × E}
    (hX : HasFDerivAt X D w₀) (hY : HasFDerivAt Y D w₀)
    (hvalue : X w₀ = Y w₀) (hlegal : X w₀ ∈ chartEnergyDomain old) (t : ℝ) :
    F.familyLabelHessianMatrix bW (fun q ↦ Φ (X q.1) q.2) (w₀, t) =
      F.familyLabelHessianMatrix bW (fun q ↦ Φ (Y q.1) q.2) (w₀, t) := by
  apply F.familyLabelHessianMatrix_eq_of_seed_firstJet bW
    (Φ := fun q : (E × E) × ℝ ↦ Φ q.1 q.2) hX hY hvalue
  exact ((hF.contMDiffOn_prescribed_complete_position old hEL hinit).contMDiffAt
    (((isOpen_chartEnergyDomain old).prod isOpen_univ).mem_nhds
      ⟨hlegal, mem_univ t⟩)).mdifferentiableAt (by simp)

variable [Fintype ι] [DecidableEq ι]

/-- The actual integrated coefficient is invariant under equal initial tangent jets
in the prescribed flow, in exactly the same original time and fixed label basis. -/
theorem intrinsicLengthQuadratic_complete_seed_eq (hF : F.IsSmoothStronglyConvex)
    (old : M) (bW : Basis ι ℝ W) {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {X Y : W → E × E} {w₀ : W} {D : W →L[ℝ] E × E}
    (hX : HasFDerivAt X D w₀) (hY : HasFDerivAt Y D w₀)
    (hvalue : X w₀ = Y w₀) (hlegal : X w₀ ∈ chartEnergyDomain old)
    (a b : ℝ) (w : W × W) :
    F.intrinsicLengthQuadratic bW (fun z t ↦ Φ (X z) t) w₀ a b w =
      F.intrinsicLengthQuadratic bW (fun z t ↦ Φ (Y z) t) w₀ a b w := by
  have hH : (fun t ↦ F.familyLabelHessianMatrix bW
      (fun q ↦ Φ (X q.1) q.2) (w₀, t)) =
      (fun t ↦ F.familyLabelHessianMatrix bW
        (fun q ↦ Φ (Y q.1) q.2) (w₀, t)) :=
    funext (hF.familyLabelHessianMatrix_complete_seed_eq old bW hEL hinit hX hY hvalue hlegal)
  simp only [intrinsicLengthQuadratic, congrFun hH]

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm
