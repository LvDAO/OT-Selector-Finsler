import OTSelector.Analysis.Calculus.PullbackGradientSymmetry
import OTSelector.Analysis.Calculus.SecondJetPolynomial
import OTSelector.Analysis.SecondOrderPeano
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerIntrinsicCostCoefficientPullback.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerIntrinsicCostCoefficientPullback`; the selected original proof blocks follow. -/
section

/-!
Conditions: An injective tangent map R with left inverse, a C1 scalar function and a differentiable pulled-back actual gradient along a C1 section.

Objects: A symmetric extension of the intrinsic pulled-back covector derivative and a matching quadratic polynomial along that section.

Proof detail: Prove symmetry on section directions, extend through the left inverse and apply the actual first-jet/Peano composition identities.

Sources: Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60); Hassler Whitney, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3) (https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2); Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html).
Relation: Intrinsic finite-jet extension derived locally. An ambient Hessian of the original C1 function is not assumed.
-/

/-!
# Polynomial potential jets from actual label derivatives

An injective section derivative and the derivative of its pulled-back covector
produce a symmetric ambient polynomial jet. The polynomial agrees to second order
along the original section, without assuming an ambient second derivative exists.
-/

open Set Filter Asymptotics
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Symmetric extension of a phase jet through a chosen left inverse of its position map. -/
def symmetricPhaseExtension (P : E →L[ℝ] W) (R : W →L[ℝ] E)
    (Q : W →L[ℝ] E →L[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  Q.comp P + (Q.comp P).flip -
    ((ContinuousLinearMap.compL ℝ E E ℝ).flip (R.comp P)).comp (Q.comp P)

/-- Isotropy is exactly the symmetry needed by the extension formula. -/
theorem symmetricPhaseExtension_symmetric (P : E →L[ℝ] W) (R : W →L[ℝ] E)
    (Q : W →L[ℝ] E →L[ℝ] ℝ)
    (hiso : ∀ ξ η : W, Q ξ (R η) = Q η (R ξ)) (x y : E) :
    symmetricPhaseExtension P R Q x y = symmetricPhaseExtension P R Q y x := by
  change Q (P x) y + Q (P y) x - Q (P x) (R (P y)) =
    Q (P y) x + Q (P x) y - Q (P y) (R (P x))
  rw [hiso (P x) (P y)]
  ring

/-- The extension retains the full covector derivative on every original label direction. -/
theorem symmetricPhaseExtension_comp (P : E →L[ℝ] W) (R : W →L[ℝ] E)
    (Q : W →L[ℝ] E →L[ℝ] ℝ) (hP : P.comp R = ContinuousLinearMap.id ℝ W)
    (hiso : ∀ ξ η : W, Q ξ (R η) = Q η (R ξ)) :
    (symmetricPhaseExtension P R Q).comp R = Q := by
  have hPR (ξ : W) : P (R ξ) = ξ := congrArg (fun A : W →L[ℝ] W ↦ A ξ) hP
  ext ξ y
  change Q (P (R ξ)) y + Q (P y) (R ξ) - Q (P (R ξ)) (R (P y)) = Q ξ y
  rw [hPR, hiso (P y) ξ]
  ring

/-- Every injective finite-dimensional phase jet with zero skew pairing admits
an actual symmetric ambient extension, with no ambient Hessian premise. -/
theorem exists_symmetric_phase_extension [FiniteDimensional ℝ E]
    (R : W →L[ℝ] E) (Q : W →L[ℝ] E →L[ℝ] ℝ)
    (hR : Function.Injective R) (hiso : ∀ ξ η : W, Q ξ (R η) = Q η (R ξ)) :
    ∃ H : E →L[ℝ] E →L[ℝ] ℝ,
      (∀ x y, H x y = H y x) ∧ H.comp R = Q := by
  let P : E →L[ℝ] W := LinearMap.toContinuousLinearMap R.toLinearMap.leftInverse
  have hP : P.comp R = ContinuousLinearMap.id ℝ W := by
    ext ξ
    exact LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hR) ξ
  exact ⟨symmetricPhaseExtension P R Q, symmetricPhaseExtension_symmetric P R Q hiso,
    symmetricPhaseExtension_comp P R Q hP hiso⟩

/-- A smooth scalar potential matching the original covector jet along a C1 section
has a quadratic-small error along that same section. -/
theorem pullback_potential_error_isLittleO
    {G P : E → ℝ} {σ : W → E} {w : W}
    {Q : W →L[ℝ] E →L[ℝ] ℝ} {H : E →L[ℝ] E →L[ℝ] ℝ}
    (hG : ContDiffAt ℝ 1 G (σ w)) (hP : ContDiffAt ℝ 1 P (σ w))
    (hσ : ContDiffAt ℝ 1 σ w)
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ G (σ z)) Q w)
    (hH : HasFDerivAt (fderiv ℝ P) H (σ w))
    (hmatch : H.comp (fderiv ℝ σ w) = Q)
    (hvalue : P (σ w) = G (σ w)) (hgrad : fderiv ℝ P (σ w) = fderiv ℝ G (σ w)) :
    (fun z ↦ G (σ z) - P (σ z)) =o[𝓝 w] (fun z ↦ ‖z - w‖ ^ 2) := by
  let f : W → ℝ := fun z ↦ G (σ z) - P (σ z)
  let g : W → E →L[ℝ] ℝ := fun z ↦ fderiv ℝ G (σ z) - fderiv ℝ P (σ z)
  let f' : W → W →L[ℝ] ℝ := fun z ↦ (g z).comp (fderiv ℝ σ z)
  have hs := (hσ.differentiableAt one_ne_zero).hasFDerivAt
  have hg : HasFDerivAt g (0 : W →L[ℝ] E →L[ℝ] ℝ) w := by
    have hh := hQ.sub (hH.comp w hs)
    simpa only [hmatch, sub_self] using! hh
  have hg0 : g w = 0 := by simp only [g, hgrad, sub_self]
  have hnear : ∀ᶠ z in 𝓝 w, HasFDerivAt f (f' z) z := by
    filter_upwards [hσ.continuousAt (hG.eventually (by simp)),
      hσ.continuousAt (hP.eventually (by simp)), hσ.eventually (by simp)] with z hGz hPz hσz
    change ContDiffAt ℝ 1 G (σ z) at hGz
    change ContDiffAt ℝ 1 P (σ z) at hPz
    have hsz := (hσz.differentiableAt one_ne_zero).hasFDerivAt
    convert! ((hGz.differentiableAt one_ne_zero).hasFDerivAt.comp z hsz).sub
      ((hPz.differentiableAt one_ne_zero).hasFDerivAt.comp z hsz) using 1
  have hsecond : HasFDerivAt f' (0 : W →L[ℝ] W →L[ℝ] ℝ) w := by
    simpa only [ContinuousLinearMap.comp_zero] using!
      hasFDerivAt_bilinear_of_zero_left (ContinuousLinearMap.compL ℝ W E ℝ)
        hg hg0 (hσ.continuousAt_fderiv (by simp))
  have hp := second_order_peano_of_hasFDerivAt hnear hsecond
  simpa only [f, f', hg0, hvalue, sub_self, ContinuousLinearMap.zero_comp,
    _root_.zero_apply, mul_zero, sub_zero] using hp

/-- The actual label jet produces a smooth ambient polynomial with second-order
agreement on the original section, even when its ambient gradient has no derivative. -/
theorem exists_polynomial_of_pullback_covector [FiniteDimensional ℝ E]
    {G : E → ℝ} {σ : W → E} {w : W} {Q : W →L[ℝ] E →L[ℝ] ℝ}
    (hG : ContDiffAt ℝ 1 G (σ w)) (hσ : ContDiffAt ℝ 1 σ w)
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ G (σ z)) Q w)
    (hR : Function.Injective (fderiv ℝ σ w)) :
    ∃ H : E →L[ℝ] E →L[ℝ] ℝ,
      (∀ x y, H x y = H y x) ∧ H.comp (fderiv ℝ σ w) = Q ∧
      let P := secondJetPolynomial (σ w) (G (σ w)) (fderiv ℝ G (σ w)) H
      ContDiff ℝ ∞ P ∧ HasFDerivAt P (fderiv ℝ G (σ w)) (σ w) ∧
        HasFDerivAt (fderiv ℝ P) H (σ w) ∧
        (fun z ↦ G (σ z) - P (σ z)) =o[𝓝 w] (fun z ↦ ‖z - w‖ ^ 2) := by
  obtain ⟨H, hsym, hcomp⟩ := exists_symmetric_phase_extension (fderiv ℝ σ w) Q hR
    (pullbackGradient_symmetric hG hσ hQ)
  let P := secondJetPolynomial (σ w) (G (σ w)) (fderiv ℝ G (σ w)) H
  have hPs : ContDiff ℝ ∞ P := contDiff_secondJetPolynomial _ _ _ _
  have hPD : HasFDerivAt P (fderiv ℝ G (σ w)) (σ w) := by
    simpa only [sub_self, map_zero, add_zero] using
      hasFDerivAt_secondJetPolynomial (σ w) (G (σ w)) (fderiv ℝ G (σ w)) H hsym (σ w)
  have hPH : HasFDerivAt (fderiv ℝ P) H (σ w) :=
    hasFDerivAt_fderiv_secondJetPolynomial _ _ _ _ hsym _
  refine ⟨H, hsym, hcomp, hPs, hPD, hPH, ?_⟩
  exact pullback_potential_error_isLittleO hG (hPs.contDiffAt.of_le (by simp)) hσ
    hQ hPH hcomp (secondJetPolynomial_self _ _ _ _) hPD.fderiv

end OTSelector.Geometry

end
end
