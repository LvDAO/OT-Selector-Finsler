import OTSelector.Geometry.Finsler.Jacobi.Pairing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.PullbackGradientSymmetry.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.PullbackGradientSymmetry`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C1 scalar function, a C1 section and an actual derivative of its gradient only after pullback along the section.

Objects: Symmetry of the pulled-back covector derivative and the corresponding phase isotropy.

Proof detail: Use the derivative of the scalar composition and mixed-increment cancellation to identify the two paired directions.

Sources: Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60); Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Ana Cannas da Silva, Homework 1, Symplectic Linear Algebra, p. 8; Section 2.2, pp. 9–10 (https://people.math.ethz.ch/~acannas/Papers/lsg.pdf#page=16).
Relation: Weaker-assumption pulled-back symmetry consequence; no ambient second derivative is inserted.
-/

/-!
# Symmetry of a differentiable pulled-back gradient

A scalar C¹ function need not have an ambient Hessian for its pulled-back gradient to
satisfy symmetry. If that gradient is differentiable along a C¹ parameterization,
its derivative is symmetric after evaluation on the parameterization's tangent map.
-/

open Filter Asymptotics
open scoped Topology ContDiff

namespace OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

section Bilinear

variable {W A B C : Type*}
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C]

/-- At a zero of the differentiable factor, continuity of the other factor suffices
for the derivative of a continuous bilinear expression. -/
theorem hasFDerivAt_bilinear_of_zero_left
    (L : A →L[ℝ] B →L[ℝ] C) {f : W → A} {g : W → B}
    {f' : W →L[ℝ] A} {x : W}
    (hf : HasFDerivAt f f' x) (hf0 : f x = 0) (hg : ContinuousAt g x) :
    HasFDerivAt (fun y ↦ L (f y) (g y)) ((L.flip (g x)).comp f') x := by
  have hfO : f =O[𝓝 x] (fun y ↦ y - x) := by
    simpa only [hf0, sub_zero] using hf.isBigO_sub
  have hgO : (fun y ↦ g y - g x) =o[𝓝 x] (fun _ ↦ (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).2 (tendsto_sub_nhds_zero_iff.2 hg)
  have herr : (fun y ↦ L (f y) (g y - g x)) =o[𝓝 x] (fun y ↦ y - x) := by
    apply L.isBoundedBilinearMap.isBigO_comp.trans_isLittleO
    simpa only [mul_one, isLittleO_norm_right] using hfO.norm_norm.mul_isLittleO hgO.norm_left
  have hzero : HasFDerivAt (fun y ↦ L (f y) (g y - g x)) (0 : W →L[ℝ] C) x := by
    apply HasFDerivAt.of_isLittleO
    simpa only [sub_self, map_zero, zero_apply, sub_zero] using herr
  have hfixed := (L.flip (g x)).hasFDerivAt.comp x hf
  convert hfixed.add hzero using 1
  · ext y
    simp [Function.comp_def]
  · simp only [add_zero]

end Bilinear

section Gradient

variable {E W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Differentiability of the pulled-back gradient gives symmetry on parameterized
tangent directions, without an ambient second derivative or a derivative of `Dσ`. -/
theorem pullbackGradient_symmetric
    {G : E → ℝ} {σ : W → E} {w : W}
    {Q : W →L[ℝ] E →L[ℝ] ℝ}
    (hG : ContDiffAt ℝ 1 G (σ w)) (hσ : ContDiffAt ℝ 1 σ w)
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ G (σ z)) Q w) (ξ η : W) :
    Q ξ (fderiv ℝ σ w η) = Q η (fderiv ℝ σ w ξ) := by
  let p := fderiv ℝ G (σ w)
  let f : W → ℝ := fun z ↦ G (σ z) - p (σ z)
  let f' : W → W →L[ℝ] ℝ := fun z ↦
    (fderiv ℝ G (σ z) - p).comp (fderiv ℝ σ z)
  let B : W →L[ℝ] W →L[ℝ] ℝ :=
    ((ContinuousLinearMap.compL ℝ W E ℝ).flip (fderiv ℝ σ w)).comp Q
  have hnear : ∀ᶠ z in 𝓝 w, HasFDerivAt f (f' z) z := by
    have hGs : ∀ᶠ z in 𝓝 w, ContDiffAt ℝ 1 G (σ z) :=
      hσ.continuousAt (hG.eventually (by simp))
    filter_upwards [hGs, hσ.eventually (by simp)] with z hGz hσz
    have hs : HasFDerivAt σ (fderiv ℝ σ z) z :=
      (hσz.differentiableAt (by simp)).hasFDerivAt
    have h := ((hGz.differentiableAt (by simp)).hasFDerivAt.comp z hs).sub
      (p.hasFDerivAt.comp z hs)
    convert! h using 1
  have hsecond : HasFDerivAt f' B w := by
    exact hasFDerivAt_bilinear_of_zero_left (ContinuousLinearMap.compL ℝ W E ℝ)
      (hQ.sub_const p) (sub_self _) (hσ.continuousAt_fderiv (by simp))
  exact second_derivative_symmetric_of_eventually_of_real hnear hsecond ξ η

/-- The phase derivative of a pulled-back gradient has zero canonical skew pairing. -/
theorem canonicalPhasePairing_pullbackGradient_eq_zero
    {G : E → ℝ} {σ : W → E} {w : W}
    {Q : W →L[ℝ] E →L[ℝ] ℝ}
    (hG : ContDiffAt ℝ 1 G (σ w)) (hσ : ContDiffAt ℝ 1 σ w)
    (hQ : HasFDerivAt (fun z ↦ fderiv ℝ G (σ z)) Q w) (ξ η : W) :
    canonicalPhasePairing (fderiv ℝ σ w ξ, Q ξ) (fderiv ℝ σ w η, Q η) = 0 := by
  simp only [canonicalPhasePairing, pullbackGradient_symmetric hG hσ hQ ξ η, sub_self]

end Gradient

end OTSelector.Geometry

end
