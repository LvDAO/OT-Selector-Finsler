import OTSelector.Analysis.Calculus.Variational.HamiltonianFlatBase
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.TubeCoordinateEnergy
import OTSelector.Geometry.Finsler.TubeCoordinateFamily
import OTSelector.Geometry.Finsler.TubeCoordinateVariation
import OTSelector.Geometry.Jacobi.PositiveEndpointKernel

/-!
# Geometry.Finsler.TubeCoordinateKernel

* **Conditions:** The actual intrinsic family read in a genuine tube, positive inverse Hessian and zero-base-column dynamics along the central segment, with both endpoint position variations zero.
* **Objects:** Zero full initial phase variation for that actual endpoint-fixed direction.
* **Proof detail:** Integrate the constant actual momentum variation and its positive inverse-Hessian position response, forcing momentum and then initial phase to vanish.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateKernel.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateKernel`; the selected original proof blocks follow. -/
section

/-!
# The actual endpoint-fixed Jacobi kernel in genuine tube coordinates

The given intrinsic family, read through the genuine inverse tube, obeys the positive
inverse-Hessian variation equation. Its actual initial phase variation vanishes when
both endpoint position variations vanish. Only the central segment must lie in the tube;
nearby parameters are localized internally using the actual joint regularity.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E V W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [FiniteDimensional ℝ V] {F : ContinuousFinslerNorm E M}

/-- The actual initial tube phase variation is zero for every endpoint-fixed
variation when the actual pulled-back Hessian has zero base columns along the segment. -/
theorem tubeCoordinateMomentumFamily_endpoint_kernel_eq_zero
    (hF : F.IsSmoothStronglyConvex) {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) {a b : ℝ} (hab : a < b)
    (hx : ∀ t ∈ Icc a b, Γ w t ∈ Y.target)
    (hzero : ∀ t ∈ Icc a b, ∀ u : V,
      fderiv ℝ (fderiv ℝ (F.tubeCoordinateEnergy Y))
        (tubeCoordinateTangentFamily Y Γ (w, t)) (u, 0) = 0)
    {ξ : W}
    (ha : (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, a)) w ξ).1 = 0)
    (hb : (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, b)) w ξ).1 = 0) :
    fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, a)) w ξ = 0 := by
  let D := (B ×ˢ (univ : Set ℝ)) ∩ (fun q : W × ℝ ↦ Γ q.1 q.2) ⁻¹' Y.target
  have hc : ContinuousOn (fun q : W × ℝ ↦ Γ q.1 q.2) (B ×ˢ univ) :=
    (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp_continuousOn hG.continuousOn
  have hD : IsOpen D := hc.isOpen_inter_preimage (hB.prod isOpen_univ) Y.open_target
  have hq (t : ℝ) (ht : t ∈ Icc a b) : (w, t) ∈ D :=
    ⟨⟨hw, mem_univ _⟩, hx t ht⟩
  let R := fun t ↦ fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, t)) w ξ
  let C := fun t ↦ ContinuousLinearMap.inverse (verticalEnergyHessian
    (F.tubeCoordinateEnergy Y) (tubeCoordinateTangentFamily Y Γ (w, t)))
  have hODE (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt R (C t (R t).2, 0) t :=
    hF.hasDerivAt_tubeCoordinateMomentumVariation_of_hessian_base_zero hY hi hD
      (hG.mono inter_subset_left) (fun _ h ↦ h.2)
      (fun q h ↦ hEL q.1 h.1.1 q.2 (mem_univ _)) (hq t ht) (hzero t ht) ξ
  have hp0 : (R a).2 = 0 := by
    apply momentum_eq_zero_of_endpoint_fixed_positive_variation hab
      (fun t ht ↦ (hODE t ht).fst) (fun t ht ↦ (hODE t ht).snd) ?_ ha hb
    intro t ht p hp
    have hz := tubeCoordinateTangentFamily_mem_domain hY hi hD
      (hG.mono inter_subset_left) (hq t ht) (hx t ht) (hEL w hw t (mem_univ _))
    exact inverse_verticalEnergyHessian_pos
      (fun u hu ↦ hF.tubeCoordinateEnergy_fiber_hessian_pos hY hi hz.1 hz.2 hu) hp
  exact Prod.ext ha hp0

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
