import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.Haar.Unique
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FocalConditionalPowerMomentsGlobalBounded.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FocalConditionalPowerMomentsGlobalBounded`; the selected original proof blocks follow. -/
section

/-!
Conditions: Continuous matrices J,K on the stated neighborhood, with det J nonzero at the center; finiteness of the integrating measure for the moment consequence.

Objects: Local boundedness of J inverse times K, all nonnegative power moments there and the singular determinant kernel criterion.

Proof detail: Use continuity of inversion away from determinant zero, local boundedness and finite-measure integration; use finite-dimensional rank for the singular case.

Sources: Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15); Stephen Boyd, Section 2.2.5, p. 34; Section 2.4.1, Example 2.15, p. 43; Appendix A.5.2, pp. 646–647 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=48); Sheldon Axler, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini) (https://measure.axler.net/MIRA.pdf).
Relation: Elementary matrix continuity/integration consequence; no special focal asymptotic or moment exponent is inferred.
-/

/-!
# Power moments near nonfocal endpoints

A continuous second solution divided by a nonsingular position matrix is locally
bounded. On the same finite conditional measure, this yields every nonnegative
power moment, with no moment assumption and no endpoint singularity estimate.
-/

open Set MeasureTheory Filter Matrix Metric
open scoped Topology Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The true inverse-times-second-solution representation is locally power-integrable
around every nonfocal point of the closed interval. -/
theorem exists_integrableOn_inverse_jacobi_product_rpow_near_nonfocal
    {J K T : ℝ → Matrix n n ℝ} {a b x r : ℝ}
    (hJ : ContinuousOn J (Icc a b)) (hK : ContinuousOn K (Icc a b))
    (hT : ContinuousOn T (Ioo a b))
    (hidentity : ∀ t ∈ Ioo a b, T t = (J t)⁻¹ * K t)
    (hx : x ∈ Icc a b) (hdet : (J x).det ≠ 0)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hr : 0 ≤ r) :
    ∃ δ > 0, IntegrableOn (fun t ↦ ‖T t‖ ^ r) (Ioo a b ∩ ball x δ) μ := by
  have hi : ContinuousAt (fun A : Matrix n n ℝ ↦ A⁻¹) (J x) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hdet
  have hG : ContinuousWithinAt (fun t ↦ (J t)⁻¹ * K t) (Icc a b) x :=
    (hi.comp_continuousWithinAt (hJ x hx)).mul (hK x hx)
  have hbound : ∀ᶠ t in 𝓝[Icc a b] x, ‖(J t)⁻¹ * K t‖ < ‖(J x)⁻¹ * K x‖ + 1 :=
    hG.norm (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.mem_nhdsWithin_iff.mp hbound
  refine ⟨δ, hδ, ?_⟩
  have hcont : ContinuousOn (fun t ↦ ‖T t‖ ^ r) (Ioo a b ∩ ball x δ) :=
    ((hT.mono inter_subset_left).norm).rpow_const (fun _ _ ↦ Or.inr hr)
  apply (integrable_const ((‖(J x)⁻¹ * K x‖ + 1) ^ r)).mono'
    (hcont.aestronglyMeasurable (measurableSet_Ioo.inter measurableSet_ball))
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.inter measurableSet_ball)] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  apply Real.rpow_le_rpow (norm_nonneg _) _ hr
  rw [hidentity t ht.1]
  exact (hδbound ⟨ht.2, Ioo_subset_Icc_self ht.1⟩).le

/-- A singular finite matrix has positive kernel dimension. -/
theorem jacobi_nullity_pos_of_det_eq_zero (J : Matrix n n ℝ) (hJ : J.det = 0) :
    0 < Module.finrank ℝ (LinearMap.ker J.mulVecLin) := by
  apply Nat.pos_of_ne_zero
  intro hdim
  have hker := Submodule.finrank_eq_zero.mp hdim
  have hdet : J.mulVecLin.det = 0 := by
    rw [← LinearMap.det_toLin'] at hJ
    exact hJ
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet) hker

end OTSelector.Geometry

end
