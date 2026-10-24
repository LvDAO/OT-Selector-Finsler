import Mathlib.Tactic
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.UniformQuadraticLinearCoordinates.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.UniformQuadraticLinearCoordinates`; the selected original proof blocks follow. -/
section

/-!
Conditions: A bounded continuous linear coordinate map and the stated uniform quadratic remainder on the allowed displacements.

Objects: The transformed uniform quadratic remainder in the original scale.

Proof detail: Apply the operator-norm displacement bound and rescale the error tolerance by the square of that bound.

Sources: Jiří Lebl, Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder) (https://www.jirka.org/ra/html/sec_taylor.html); Jiří Lebl, Section 8.1.3, Propositions 8.1.17–8.1.18, p. 15 (https://www.jirka.org/ra/realanal2.pdf#page=15).
Relation: Elementary quantitative coordinate substitution; it assumes no isometry.
-/

/-!
# Uniform quadratic remainders in retained linear coordinates

A bounded linear coordinate map supplies its own norm constant and radius change.
The allowed displacement set is retained exactly, with no isometry assumption.
-/

open Set

namespace OTSelector.Geometry

variable {I V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A uniform quadratic remainder on an allowed displacement set remains uniform
in arbitrary fixed linear coordinates, using the actual map's operator norm. -/
theorem uniform_quadratic_remainder_comp_clm (L : V →L[ℝ] W)
    (S : Set I) (error : I → W → ℝ) (allowed : I → W → Prop)
    (hrem : ∀ η : ℝ, 0 < η → ∃ r > 0, ∀ i ∈ S, ∀ w : W,
      ‖w‖ < r → allowed i w → ‖error i w‖ ≤ η * ‖w‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ r > 0, ∀ i ∈ S, ∀ v : V,
      ‖v‖ < r → allowed i (L v) → ‖error i (L v)‖ ≤ ε * ‖v‖ ^ 2 := by
  let B := ‖L‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hLB : ‖L‖ ≤ B := by dsimp [B]; linarith
  intro ε hε
  let η := ε / B ^ 2
  have hη : 0 < η := div_pos hε (sq_pos_of_pos hB)
  obtain ⟨r, hr, hb⟩ := hrem η hη
  refine ⟨r / B, div_pos hr hB, ?_⟩
  intro i hi v hv ha
  have hnorm : ‖L v‖ ≤ B * ‖v‖ :=
    (L.le_opNorm v).trans (mul_le_mul_of_nonneg_right hLB (norm_nonneg v))
  have hsmall : ‖L v‖ < r := hnorm.trans_lt (by
    simpa only [mul_comm] using (lt_div_iff₀ hB).mp hv)
  calc
    ‖error i (L v)‖ ≤ η * ‖L v‖ ^ 2 := hb i hi _ hsmall ha
    _ ≤ η * (B * ‖v‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) hη.le
    _ = ε * ‖v‖ ^ 2 := by
      rw [mul_pow, ← mul_assoc, div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hB))]

end OTSelector.Geometry

end
