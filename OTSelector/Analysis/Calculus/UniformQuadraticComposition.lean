import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic

/-!
# Analysis.Calculus.UniformQuadraticComposition

Conditions: A family of quadratic remainders is uniformly small at zero, and the composed displacements are uniformly bounded linearly by the small parameter.

Objects: Uniform quadratic smallness after composition with those displacements.

Proof detail: Rescale the requested tolerance by the square of the displacement bound, choose the corresponding common remainder radius, and substitute the O(w) estimate.

## Mathematical sources

- [Jiří Lebl, Basic Analysis I](https://www.jirka.org/ra/html/sec_taylor.html): Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder).

Source relation: Elementary uniform little-o composition lemma; the normed-space family form is locally proved.
-/

/-!
# Uniform quadratic remainders along controlled displacements

A common ambient remainder radius and a common linear displacement bound give a
common quadratic remainder radius on the unchanged allowed parameter set.
-/

open Set

namespace OTSelector.Geometry

variable {I E W : Type*} [NormedAddCommGroup E] [NormedAddCommGroup W]

/-- Uniform ambient quadratic errors remain quadratic along maps with a common
linear displacement bound, including arbitrary allowed parameter sets. -/
theorem uniform_quadratic_error_of_linear_displacement
    (S : Set I) (center : I → E) (error : I → E → ℝ) (X : I → W → E)
    (allowed : I → W → Prop)
    (hrem : ∀ δ : ℝ, 0 < δ → ∃ r > 0, ∀ i ∈ S, ∀ h : E, ‖h‖ < r →
      ‖error i (center i + h)‖ ≤ δ * ‖h‖ ^ 2)
    {A R : ℝ} (hA : 0 ≤ A) (hR : 0 < R)
    (hsize : ∀ i ∈ S, ∀ w, ‖w‖ < R → allowed i w →
      ‖X i w - center i‖ ≤ A * ‖w‖)
    {η : ℝ} (hη : 0 < η) :
    ∃ r > 0, ∀ i ∈ S, ∀ w, ‖w‖ < r → allowed i w →
      ‖error i (X i w)‖ ≤ η * ‖w‖ ^ 2 := by
  let B := A + 1
  have hB : 0 < B := by dsimp [B]; linarith
  have hAB : A ≤ B := by dsimp [B]; linarith
  let δ := η / B ^ 2
  have hδ : 0 < δ := div_pos hη (sq_pos_of_pos hB)
  have hδB : δ * B ^ 2 = η := div_mul_cancel₀ η (ne_of_gt (sq_pos_of_pos hB))
  obtain ⟨r, hr, hb⟩ := hrem δ hδ
  refine ⟨min R (r / B), lt_min hR (div_pos hr hB), ?_⟩
  intro i hi w hw ha
  have hdisp : ‖X i w - center i‖ ≤ B * ‖w‖ :=
    (hsize i hi w (hw.trans_le (min_le_left _ _)) ha).trans
      (mul_le_mul_of_nonneg_right hAB (norm_nonneg _))
  have hsmall : ‖X i w - center i‖ < r := hdisp.trans_lt (by
    simpa only [mul_comm] using (lt_div_iff₀ hB).mp (hw.trans_le (min_le_right _ _)))
  have he := hb i hi (X i w - center i) hsmall
  rw [add_sub_cancel] at he
  calc
    _ ≤ δ * ‖X i w - center i‖ ^ 2 := he
    _ ≤ δ * (B * ‖w‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hdisp 2) hδ.le
    _ = η * ‖w‖ ^ 2 := by rw [mul_pow, ← mul_assoc, hδB]

end OTSelector.Geometry
