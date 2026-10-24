import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.AdaptedGraphMomentum
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Symplectic.LinearCotangentPhase

/-!
# Geometry.Finsler.AdaptedPhaseDerivative

* **Conditions:** The actual adapted graph inverse and a common positive original Finsler speed.
* **Objects:** Exact adapted full-phase parameter differential including the same inverse-time correction.
* **Proof detail:** Differentiate the linearly transformed original phase and its constant-speed spatial momentum restriction.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerAdaptedPhaseDerivative.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerAdaptedPhaseDerivative`; the selected original proof blocks follow. -/
section

/-!
# Differential of the same adapted graph phase

A constant original Finsler speed identifies the true graph differential with the
spatial restriction of the actual linearly transformed cotangent phase differential.
The same graph inverse supplies the time correction in both position and momentum.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- At constant original speed the adapted graph derivative is the spatial restriction
of the actual transformed original phase derivative, with speed-normalized momentum. -/
theorem adaptedGraphPhase_differential_on_of_constant_speed (old : M)
    (T : E ≃L[ℝ] (ℝ × V))
    {ℓ : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hℓ : (ℓ : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : ℓ.source ⊆ chartEnergyDomain old)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : DifferentiableOn ℝ Ψ D) (hmap : MapsTo Ψ D ℓ.target)
    (hODE : ∀ p ∈ D, HasDerivAt (fun s ↦ Ψ (p.1, s))
      (localHamiltonianVectorField (F.chartEnergy old) ℓ (Ψ p)) p.2)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ T (Ψ z).1))
    (hesub : e.source ⊆ D) {Q : Set (W × ℝ)} (hQ : IsOpen Q) (hQt : Q ⊆ e.target)
    (hi : DifferentiableOn ℝ e.symm Q)
    (hpos : ∀ p ∈ Q, 0 < (fderiv ℝ (fun z ↦ T (Ψ z).1) (e.symm p) (0, 1)).1)
    {S : ℝ} (hS : ∀ p ∈ D, (F.chartLength old (ℓ.symm (Ψ p)) : ℝ) = S)
    {q : W × ℝ} (hq : q ∈ Q) :
    let ΨT := linearCotangentPhase T ∘ Ψ
    DifferentiableAt ℝ (F.adaptedGraphPhase old T (fun z ↦ T (Ψ z).1) e) q ∧
    ∀ w : W,
      fderiv ℝ (F.adaptedGraphPhase old T (fun z ↦ T (Ψ z).1) e) q (w, 0) =
        ((fderiv ℝ (ΨT ∘ e.symm) q (w, 0)).1.2,
          S⁻¹ • (fderiv ℝ (ΨT ∘ e.symm) q (w, 0)).2.comp
            (ContinuousLinearMap.inr ℝ ℝ V)) := by
  let ΨT := linearCotangentPhase T ∘ Ψ
  have hR : DifferentiableAt ℝ (ΨT ∘ e.symm) q :=
    ((linearCotangentPhase T).differentiableAt.comp _
      ((hΨ _ (hesub (e.map_target (hQt hq)))).differentiableAt
        (hD.mem_nhds (hesub (e.map_target (hQt hq)))))).comp q
          ((hi q hq).differentiableAt (hQ.mem_nhds hq))
  have hp := ((hR.hasFDerivAt.snd.const_smul S⁻¹).clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.inr ℝ ℝ V) q))
  have hT := hR.hasFDerivAt.fst.snd.prodMk hp
  have heq : F.adaptedGraphPhase old T (fun z ↦ T (Ψ z).1) e =ᶠ[𝓝 q]
      (fun p ↦ ((ΨT (e.symm p)).1.2,
        (S⁻¹ • (ΨT (e.symm p)).2).comp (ContinuousLinearMap.inr ℝ ℝ V))) := by
    filter_upwards [hQ.mem_nhds hq] with p hp
    have hs := hesub (e.map_target (hQt hp))
    rw [hF.adaptedGraphPhase_eq_rescaled_energy old T hℓ hsub he (hQt hp)
      ((hΨ _ hs).differentiableAt (hD.mem_nhds hs))
      ((hi p hp).differentiableAt (hQ.mem_nhds hp))
      (hmap hs) (hODE _ hs) (hpos p hp), hS _ hs]
    simp only [ΨT, Function.comp_apply, linearCotangentPhase_apply,
      ContinuousLinearMap.smul_comp]
  have hP := hT.congr_of_eventuallyEq heq
  refine ⟨hP.differentiableAt, ?_⟩
  intro w
  have hh := congrArg (fun A ↦ A (w, 0)) hP.fderiv
  simpa using hh

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
