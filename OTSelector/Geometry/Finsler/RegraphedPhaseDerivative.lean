import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.GraphMomentum
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.RegraphedPhaseDerivative.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.RegraphedPhaseDerivative`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.RegraphedPhaseDerivative

* **Conditions:** An actual differentiable phase family with its own inverse graph coordinates; constant positive original speed for the graph momentum differential formulas.
* **Objects:** The full position–momentum inverse-time correction and exact actual graph-phase parameter derivative.
* **Proof detail:** Apply the inverse graph chain rule to both phase components and differentiate the same constant-speed momentum normalization.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Actual full-phase derivative under the same graph inverse

The original phase is differentiated through its own position graph inverse.
The time correction acts on both position and momentum. No new phase family
or independently prescribed derivative is introduced.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual regraphed phase derivative includes the old-time correction in both blocks. -/
theorem regraphedPhase_parameter_fderiv
    {Ψ : W × ℝ → (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ (Ψ z).1))
    {q : W × ℝ} (hq : q ∈ e.target)
    (hΨ : DifferentiableAt ℝ Ψ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hv : (fderiv ℝ (fun z ↦ (Ψ z).1) (e.symm q) (0, 1)).1 ≠ 0) (w : W) :
    fderiv ℝ (Ψ ∘ e.symm) q (w, 0) =
      fderiv ℝ Ψ (e.symm q) (w, 0) -
        ((fderiv ℝ (fun z ↦ (Ψ z).1) (e.symm q) (w, 0)).1 /
          (fderiv ℝ (fun z ↦ (Ψ z).1) (e.symm q) (0, 1)).1) •
          fderiv ℝ Ψ (e.symm q) (0, 1) := by
  rw [fderiv_comp q hΨ hi]
  change fderiv ℝ Ψ (e.symm q) (fderiv ℝ e.symm q (w, 0)) = _
  rw [curveGraph_inverse_fderiv_apply he hq hΨ.fst hi hv]
  have hsplit (r : ℝ) : (w, r) = (w, 0) + r • (0, 1) := by
    ext <;> simp
  rw [hsplit, map_add, map_smul, zero_sub, neg_div]
  module

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M]
  {F : ContinuousFinslerNorm (ℝ × V) M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- At constant original speed, the true graph differential is the projected old phase
differential divided by that speed in the momentum block. -/
theorem chartGraphPhase_differential_on_of_constant_speed (x₀ : M)
    {ℓ : OpenPartialHomeomorph ((ℝ × V) × (ℝ × V))
      ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))}
    (hℓ : (ℓ : ((ℝ × V) × (ℝ × V)) → ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy x₀))
    (hsub : ℓ.source ⊆ chartEnergyDomain x₀)
    {Ψ : W × ℝ → (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : DifferentiableOn ℝ Ψ D) (hmap : MapsTo Ψ D ℓ.target)
    (hODE : ∀ p ∈ D, HasDerivAt (fun s ↦ Ψ (p.1, s))
      (localHamiltonianVectorField (F.chartEnergy x₀) ℓ (Ψ p)) p.2)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ (Ψ z).1))
    (hesub : e.source ⊆ D) {Q : Set (W × ℝ)} (hQ : IsOpen Q) (hQt : Q ⊆ e.target)
    (hi : DifferentiableOn ℝ e.symm Q)
    (hpos : ∀ p ∈ Q, 0 < (fderiv ℝ (fun z ↦ (Ψ z).1) (e.symm p) (0, 1)).1)
    {S : ℝ} (hS : ∀ p ∈ D, (F.chartLength x₀ (ℓ.symm (Ψ p)) : ℝ) = S)
    {q : W × ℝ} (hq : q ∈ Q) :
    DifferentiableAt ℝ (F.chartGraphPhase x₀ (fun z ↦ (Ψ z).1) e) q ∧
    ∀ w : W, fderiv ℝ (F.chartGraphPhase x₀ (fun z ↦ (Ψ z).1) e) q (w, 0) =
      ((fderiv ℝ (Ψ ∘ e.symm) q (w, 0)).1.2,
        S⁻¹ • (fderiv ℝ (Ψ ∘ e.symm) q (w, 0)).2.comp
          (ContinuousLinearMap.inr ℝ ℝ V)) := by
  have hR : DifferentiableAt ℝ (Ψ ∘ e.symm) q :=
    ((hΨ _ (hesub (e.map_target (hQt hq)))).differentiableAt
      (hD.mem_nhds (hesub (e.map_target (hQt hq))))).comp q
      ((hi q hq).differentiableAt (hQ.mem_nhds hq))
  have hp := ((hR.hasFDerivAt.snd.const_smul S⁻¹).clm_comp
    (hasFDerivAt_const (ContinuousLinearMap.inr ℝ ℝ V) q))
  have hT := hR.hasFDerivAt.fst.snd.prodMk hp
  have heq : F.chartGraphPhase x₀ (fun z ↦ (Ψ z).1) e =ᶠ[𝓝 q]
      (fun p ↦ ((Ψ (e.symm p)).1.2,
        (S⁻¹ • (Ψ (e.symm p)).2).comp (ContinuousLinearMap.inr ℝ ℝ V))) := by
    filter_upwards [hQ.mem_nhds hq] with p hp
    have hs := hesub (e.map_target (hQt hp))
    rw [hF.chartGraphPhase_eq_rescaled_energy x₀ hℓ hsub he (hQt hp)
      ((hΨ _ hs).differentiableAt (hD.mem_nhds hs))
      ((hi p hp).differentiableAt (hQ.mem_nhds hp))
      (hmap hs) (hODE _ hs) (hpos p hp), hS _ hs]
  have hP := hT.congr_of_eventuallyEq heq
  refine ⟨hP.differentiableAt, ?_⟩
  intro w
  have hh := congrArg (fun A ↦ A (w, 0)) hP.fderiv
  simpa using hh

/-- At constant original speed, the true graph differential is the projected old phase
differential divided by that speed in the momentum block. -/
theorem chartGraphPhase_fderiv_of_constant_speed (x₀ : M)
    {ℓ : OpenPartialHomeomorph ((ℝ × V) × (ℝ × V))
      ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))}
    (hℓ : (ℓ : ((ℝ × V) × (ℝ × V)) → ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy x₀))
    (hsub : ℓ.source ⊆ chartEnergyDomain x₀)
    {Ψ : W × ℝ → (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : DifferentiableOn ℝ Ψ D) (hmap : MapsTo Ψ D ℓ.target)
    (hODE : ∀ p ∈ D, HasDerivAt (fun s ↦ Ψ (p.1, s))
      (localHamiltonianVectorField (F.chartEnergy x₀) ℓ (Ψ p)) p.2)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ (Ψ z).1))
    (hesub : e.source ⊆ D) (hi : DifferentiableOn ℝ e.symm e.target)
    (hpos : ∀ p ∈ e.source, 0 < (fderiv ℝ (fun z ↦ (Ψ z).1) p (0, 1)).1)
    {S : ℝ} (hS : ∀ p ∈ D, (F.chartLength x₀ (ℓ.symm (Ψ p)) : ℝ) = S)
    {q : W × ℝ} (hq : q ∈ e.target) (w : W) :
    fderiv ℝ (F.chartGraphPhase x₀ (fun z ↦ (Ψ z).1) e) q (w, 0) =
      ((fderiv ℝ (Ψ ∘ e.symm) q (w, 0)).1.2,
        S⁻¹ • (fderiv ℝ (Ψ ∘ e.symm) q (w, 0)).2.comp
          (ContinuousLinearMap.inr ℝ ℝ V)) := by
  exact (hF.chartGraphPhase_differential_on_of_constant_speed x₀ hℓ hsub
    hD hΨ hmap hODE he hesub e.open_target (Subset.refl _) hi
    (fun p hp ↦ hpos _ (e.map_target hp)) hS hq).2 w

end ContinuousFinslerNorm.IsSmoothStronglyConvex

end OTSelector.Geometry

end
end
