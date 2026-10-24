import OTSelector.Analysis.CanonicalUnitCurve
import OTSelector.Analysis.ContractivePerturbationInverse
import OTSelector.Analysis.LipschitzCommonScaleField
import OTSelector.Finite.LatticePairCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CommonScaleCanonicalPhaseCurve.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CommonScaleCanonicalPhaseCurve`; the selected original proof blocks follow. -/
section

/-!
# Analysis.CommonScaleCanonicalCurve

Conditions: A positive rescaling factor, the complete normed carrier, the original Lipschitz field and the same contractive mobility; the uniform-contributor version requires scale at least one.
Objects: The rescaled field and the same canonical inverse/position-momentum curve, with amplitude and approximation errors divided by the scale.
Proof detail: Plug the rescaled old solution into the inverse equation, identify it by uniqueness, and transport the established contributor and curve bounds through scalar homogeneity.

## Mathematical sources

- Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (author version)*: Section 2.1, Theorem 2.1 (Contraction principle), pp. 35–36. https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=46
- OT-Selector project, *Empirical optimal transport selection on general Finsler manifolds, main.tex*: Lemma lem:highd-perturbed-traffic, proof paragraph defining F_r and its inverse trajectory; phase-tube and rescaling bounds. ../main.tex#L3688

Source relation: A uniqueness-and-homogeneity corollary of the project’s quantitative contractive inverse. The reference supplies contraction uniqueness, while the exact same-curve scaling identity is proved here.
-/

/-! The existing canonical inverse curve scales with the same original
mobility. Uniqueness identifies it with the inverse of the rescaled field. -/
open Set Function MeasureTheory
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Rescaling the existing unique inverse is the canonical inverse of the
rescaled field; no new inverse existence theorem is required. -/
theorem canonicalUnitPhasePosition_commonScale {δ L : ℝ} (hδ : 0 < δ)
    (P : V → V) (hP : ∀ x y, ‖P x - P y‖ ≤ L * ‖x - y‖)
    (R : ℝ → V →L[ℝ] V)
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ)) (r : ℝ) :
    canonicalUnitPhasePosition (commonScalePhaseField δ P)
      (commonScalePhaseField_norm_lipschitz hδ hP) R hsmall r =
        commonScalePhaseCurve δ (canonicalUnitPhasePosition P hP R hsmall) r := by
  let z := canonicalUnitPhasePosition P hP R hsmall r
  have hz : z + unitPhaseMobility R r (P z) = 0 :=
    phaseInverseAt_eq hP _ (unitPhaseMobility_small R hsmall r) 0
  symm
  change δ⁻¹ • z = phaseInverseAt (commonScalePhaseField δ P)
    (commonScalePhaseField_norm_lipschitz hδ hP) (unitPhaseMobility R r)
      (unitPhaseMobility_small R hsmall r) 0
  apply phaseInverseAt_unique (commonScalePhaseField_norm_lipschitz hδ hP)
    (unitPhaseMobility R r) (unitPhaseMobility_small R hsmall r)
  rw [commonScalePhaseField_at_scaled hδ, map_smul, ← smul_add, hz, smul_zero]

/-- Position and momentum of the literal canonical pair share the same scale. -/
theorem canonicalUnitPhasePair_commonScale {q : ℕ} {δ L : ℝ} (hδ : 0 < δ)
    (P : (Fin q → ℝ) → Fin q → ℝ)
    (hP : ∀ x y, ‖P x - P y‖ ≤ L * ‖x - y‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ)) (r : ℝ) :
    canonicalUnitPhasePair (commonScalePhaseField δ P)
      (commonScalePhaseField_norm_lipschitz hδ hP) R hsmall r =
        commonScalePhaseCurve δ (canonicalUnitPhasePair P hP R hsmall) r := by
  unfold canonicalUnitPhasePair
  rw [canonicalUnitPhasePosition_commonScale hδ P hP R hsmall r]
  unfold commonScalePhaseCurve
  rw [commonScalePhaseField_at_scaled hδ P (canonicalUnitPhasePosition P hP R hsmall r),
    phasePairVector_common_smul]

/-- The original physical constraint and original node error give the scaled
curve tube directly, with the actual node error divided by `δ`. -/
theorem commonScaleCanonicalPhasePair_contributor {q : ℕ} {δ L : ℝ}
    (hδ : 0 < δ) (hL : 0 ≤ L)
    {P : (Fin q → ℝ) → Fin q → ℝ}
    (hP : ∀ x y, ‖P x - P y‖ ≤ L * ‖x - y‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ))
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) {ρ a b : ℝ} (hR : ‖R r‖ ≤ ρ)
    {x p : Fin q → ℝ} (hphysical : ‖δ⁻¹ • x + R r (δ⁻¹ • p)‖ ≤ a)
    (hnode : ‖p - P x‖ ≤ b) :
    ‖phasePairVector (δ⁻¹ • x) (δ⁻¹ • p) -
      commonScalePhaseCurve δ (canonicalUnitPhasePair P hP R hsmall) r‖ ≤
      max (2 * (a + ρ * (b / δ))) (b / δ + 2 * L * (a + ρ * (b / δ))) := by
  rw [← canonicalUnitPhasePair_commonScale hδ]
  exact canonicalUnitPhasePair_contributor hL (commonScalePhaseField_norm_lipschitz hδ hP)
    R hsmall hr hR hphysical (commonScalePhaseField_node_error hδ P hnode)

/-- At scales at least one, every original contributor has a tube radius
independent of the common phase scale. -/
theorem commonScaleCanonicalPhasePair_contributor_uniform {q : ℕ} {δ L : ℝ}
    (hδ : 1 ≤ δ) (hL : 0 ≤ L)
    {P : (Fin q → ℝ) → Fin q → ℝ}
    (hP : ∀ x y, ‖P x - P y‖ ≤ L * ‖x - y‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ))
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) {ρ a b : ℝ}
    (hρ : 0 ≤ ρ) (hb : 0 ≤ b) (hR : ‖R r‖ ≤ ρ)
    {x p : Fin q → ℝ} (hphysical : ‖δ⁻¹ • x + R r (δ⁻¹ • p)‖ ≤ a)
    (hnode : ‖p - P x‖ ≤ b) :
    ‖phasePairVector (δ⁻¹ • x) (δ⁻¹ • p) -
      commonScalePhaseCurve δ (canonicalUnitPhasePair P hP R hsmall) r‖ ≤
      max (2 * (a + ρ * b)) (b + 2 * L * (a + ρ * b)) := by
  apply (commonScaleCanonicalPhasePair_contributor (by linarith : 0 < δ)
    hL hP R hsmall hr hR hphysical hnode).trans
  have hbd : b / δ ≤ b := div_le_self hb hδ
  apply max_le_max
  · nlinarith [mul_le_mul_of_nonneg_left hbd hρ]
  · nlinarith [mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hbd hρ) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL)]

/-- The original amplitude is divided by δ in both literal curve bounds. -/
theorem commonScaleCanonicalPhasePair_bounds {q : ℕ} {δ L : ℝ}
    (hδ : 0 < δ) (hL : 0 ≤ L)
    {P : (Fin q → ℝ) → Fin q → ℝ}
    (hP : ∀ x y, ‖P x - P y‖ ≤ L * ‖x - y‖)
    (R : ℝ → (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))
    (hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * L ≤ (1 / 2 : ℝ))
    {ρ A : ℝ} (hρ : 0 ≤ ρ) (hA : 0 ≤ A)
    (hR : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ ρ)
    (hRLip : ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖R r - R s‖ ≤ A * |r - s|) :
    (∀ r ∈ Icc (0 : ℝ) 1,
      commonScalePhaseCurve δ (canonicalUnitPhasePosition P hP R hsmall) r +
        R r (commonScalePhaseField δ P
          (commonScalePhaseCurve δ (canonicalUnitPhasePosition P hP R hsmall) r)) = 0) ∧
    (∀ r ∈ Icc (0 : ℝ) 1,
      ‖commonScalePhaseCurve δ (canonicalUnitPhasePair P hP R hsmall) r‖ ≤
        2 * (ρ + 1) * (‖P 0‖ / δ)) ∧
    ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖commonScalePhaseCurve δ (canonicalUnitPhasePair P hP R hsmall) r -
        commonScalePhaseCurve δ (canonicalUnitPhasePair P hP R hsmall) s‖ ≤
          4 * (1 + L) * A * (‖P 0‖ / δ) * |r - s| := by
  have hb := canonicalUnitPhasePair_bounds hL (commonScalePhaseField_norm_lipschitz hδ hP)
    R hsmall hρ hA hR hRLip
  have hn : ‖commonScalePhaseField δ P 0‖ = ‖P 0‖ / δ := by
    rw [commonScalePhaseField_zero, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hδ)]
    ring
  simpa only [canonicalUnitPhasePosition_commonScale hδ P hP R hsmall,
    canonicalUnitPhasePair_commonScale hδ P hP R hsmall, hn] using
      (show _ ∧ _ ∧ _ from ⟨hb.1, hb.2.1, hb.2.2.1⟩)

end OTSelector.Reconstruction
end
end
