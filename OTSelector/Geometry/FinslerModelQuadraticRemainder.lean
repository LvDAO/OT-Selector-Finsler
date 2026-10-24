import OTSelector.Geometry.FinslerUniformModelQuadratic
import OTSelector.Analysis.Calculus.QuadraticExpansionUniqueness

/-!
# Pointwise quadratic remainder of the actual normalized model

The compact uniform expansion specialized to one original point and one time pair
gives a little-o remainder with the actual polynomial phase quadratic coefficient.
Continuity of the original Hessian on the singleton is automatic.
-/

open Set Manifold Asymptotics
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual normalized model deficit has the actual phase quadratic coefficient
at one original point, without a Hessian continuity premise. -/
theorem polynomial_model_quadratic_remainder_isLittleO
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G) {x : E}
    (hlegal : (x, fderiv ℝ G x) ∈ eL.target)
    (henergy : F.chartEnergy old (eL.symm (x, fderiv ℝ G x)) = 1 / 2)
    {O : Set (ScalarSecondJet E)} {B : Set W}
    (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : W) ∈ B)
    (hj : (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    {σ : ScalarSecondJet E × W → E} (hσ : ContDiffOn ℝ 1 σ (O ×ˢ B))
    (hσ₀ : ∀ j ∈ O, σ (j, 0) = j.1)
    (hσlevel : ∀ j ∈ O, ∀ w ∈ B,
      scalarSecondJetPolynomial j (σ (j, w)) = j.2.1)
    (Φ : (E × E) → ℝ → M) (t : ℝ × ℝ)
    (hC3 : ContDiffAt ℝ 3 (F.parameterizedPhaseLengthAction old Φ)
      (((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), t),
        (eL.symm (x, fderiv ℝ G x), eL.symm (x, fderiv ℝ G x))))
    (hstationary : HasFDerivAt (F.phaseLengthAction old Φ
      (scalarSecondJetPolynomial (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x))
      t.1 t.2) (0 : ((E × E) × (E × E)) →L[ℝ] ℝ)
      (eL.symm (x, fderiv ℝ G x), eL.symm (x, fderiv ℝ G x)))
    (hcentralDistance : (F.lengthEDist (Φ (eL.symm (x, fderiv ℝ G x)) t.1)
      (Φ (eL.symm (x, fderiv ℝ G x)) t.2)).toReal = t.2 - t.1) :
    let j : ScalarSecondJet E :=
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
    (fun w : W × W ↦
      let pair := F.polynomialPhasePair old eL σ (j, w)
      ((F.lengthEDist (Φ pair.1 t.1) (Φ pair.2 t.2)).toReal - (t.2 - t.1)) -
        F.polynomialPhaseQuadratic old Φ eL σ j t w)
      =o[𝓝 (0 : W × W)] (fun w ↦ ‖w‖ ^ 2) := by
  dsimp only
  have model := hF.uniform_polynomial_model_quadratic old
    (W := W) (eL := eL) (G := G) (K := {x}) (O := O) (B := B) (σ := σ) (T := {t})
  have model₁ := model heL hsource hInv hG isCompact_singleton
    (continuousOn_singleton _ x)
  have model₂ := model₁
    (by simpa only [forall_mem_singleton] using hlegal)
    (by simpa only [forall_mem_singleton] using henergy)
  have model₃ := model₂ hO hB h0B
    (by simpa only [forall_mem_singleton] using hj) hσ hσ₀ hσlevel Φ isCompact_singleton
  have model₄ := model₃
    (by simpa only [forall_mem_singleton] using hC3)
    (by simpa only [forall_mem_singleton] using hstationary)
    (by simpa only [forall_mem_singleton] using hcentralDistance)
  apply isLittleO_norm_sq_of_remainder_bound
  intro ε hε
  obtain ⟨r, hr, hb⟩ := model₄ ε hε
  exact ⟨r, hr, fun w hw ↦ hb x (mem_singleton x) t (mem_singleton t) w hw⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
