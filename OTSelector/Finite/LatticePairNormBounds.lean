import OTSelector.Finite.LatticePairCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.PhasePairNormBounds.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.PhasePairNormBounds`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.PhasePairNormBounds

**Conditions:** Position and momentum have matching finite dimensions and the coordinate supremum norm.

**Objects:** Norm bounds and additive difference identity for their concatenated phase vector.

**Proof detail:** Split the coordinate index into position and momentum blocks; pointwise maxima give the pair norm bound and subtraction respects the two blocks exactly.

**Sources:** [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_7_1.lean), Sections 4.3 (absolute value) and 7.1 (finite series), in particular Proposition 7.1.11; [OTSelector project, Finite phase-animal counting in the high-dimensional localization proof](main.tex#eq:highd-phase-animal-tail), main.tex label eq:highd-phase-animal-tail, line 3267.

Source relation (adapter): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! # Norm control of the actual position-momentum coordinate vector -/
noncomputable section
namespace OTSelector.Reconstruction

/-- The literal combined vector has the maximum of the two component norm bounds. -/
theorem norm_phasePairVector_le {q : ℕ} (z p : Fin q → ℝ) :
    ‖phasePairVector z p‖ ≤ max ‖z‖ ‖p‖ := by
  apply (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg z))).mpr
  intro i
  by_cases h : (i : ℕ) < q
  · simpa only [phasePairVector, dite_eq_left h] using
      (norm_le_pi_norm z ⟨i, h⟩).trans (le_max_left _ _)
  · simpa only [phasePairVector, dite_eq_right h] using
      (norm_le_pi_norm p ⟨(i : ℕ) - q, by omega⟩).trans (le_max_right _ _)

/-- Subtraction keeps position and momentum in their original coordinates. -/
theorem phasePairVector_sub {q : ℕ} (z p w v : Fin q → ℝ) :
    phasePairVector z p - phasePairVector w v = phasePairVector (z - w) (p - v) := by
  funext i
  by_cases h : (i : ℕ) < q <;> simp [phasePairVector, h]

/-- Componentwise distance estimates give a true distance estimate in phase space. -/
theorem norm_phasePairVector_sub_le {q : ℕ} (z p w v : Fin q → ℝ) :
    ‖phasePairVector z p - phasePairVector w v‖ ≤ max ‖z - w‖ ‖p - v‖ := by
  rw [phasePairVector_sub]
  exact norm_phasePairVector_le _ _

/-- A common nonnegative component bound bounds the literal joint phase distance. -/
theorem norm_phasePairVector_sub_le_of_le {q : ℕ} {z p w v : Fin q → ℝ}
    {C : ℝ} (hz : ‖z - w‖ ≤ C) (hp : ‖p - v‖ ≤ C) :
    ‖phasePairVector z p - phasePairVector w v‖ ≤ C :=
  (norm_phasePairVector_sub_le _ _ _ _).trans (max_le hz hp)

end OTSelector.Reconstruction

end
end
